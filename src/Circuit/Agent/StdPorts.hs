{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Process ports: stdin / stdout / stderr as free dual ends.
--
-- A 'StdPorts' handle is a persistent child process viewed through three
-- independent 'Circuit.Ends' seats plus a close action.  Pipes all the way
-- down: no FIFO, no log files, no byte-offset polling.
--
-- Internal I/O is 'ByteString'.  Constructors take encode/decode adapters:
--
-- @
-- openStdPorts encodeUtf8 decodeUtf8 cfg  -- 'Text'
-- openStdPorts id id cfg                  -- 'ByteString'
-- @
--
-- = Stream marks
--
-- The boundary grammar of a process stream is a type, 'ProcMarks' — the
-- level-0 grammar of 'Circuit.Agent.Mark' surfaced at the process boundary.
-- A mark announces the end of a frame; everything before it is the payload.
-- 'splitFrame' is the stateless parse of the mark machine: the byte buffer
-- is the whole state.
--
-- A pump thread per output handle frames the raw stream and closes each
-- payload into a queue ('openIO' 'Unbounded').  The emit ends are the queue
-- companions: an emit /blocks/ until a complete frame arrives — the queue's
-- @readTQueue@ retry IS the blocking boundary.  Arrival is decided by
-- content, never inferred from quiet; there is no timeout and no empty
-- poll result on the emit side.
--
-- = Resource lifecycle
--
-- 'openStdPorts' returns a @'Loop' 'Either'@ where the feedback state is
-- the process.  'Left' = process alive, 'Right' = ports delivered.  The
-- 'StdPorts' ends are self-contained — they capture the pipe handles, the
-- queues, and the pump threads.  'stdClose' terminates the process, kills
-- the pumps, and closes the handles.
module Circuit.Agent.StdPorts
  ( -- * Configuration
    ProcConfig (..),
    defaultProcConfig,

    -- * Stream marks
    ProcMarks (..),
    splitFrame,
    lineMarks,
    ghciMarks,
    hermesMarks,
    sseMarks,

    -- * Process ports
    StdPorts (..),
    openStdPorts,

    -- * The mark machine
    frameAgent,
    frameProcess,

    -- * Ends / seat view (client-facing)
    ProcEnds (..),
    stdioEnds,
    stderrEnds,
    openProc,
    portsEnds,

    -- * In-memory test harness
    echo,
  )
where

import Circuit.Agent (Agent, run1)
import Circuit.Agent.Ends (ChannelPolicy (..), Queue (..), openChannel, openIO)
import Circuit.Category ((.>))
import Circuit.ChannelPoly (iterateSystem, systemAsProcess)
import Circuit.Ends (Ends (..), In (..), Out (..), commit, emit, open)
import Circuit.Loop (Loop (..))
import Circuit.Poly (Eval (..), fromEvalSystem)
import Circuit.Process (Process)
import Circuit.Tensor (Tensor (..))
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Concurrent (forkIO, killThread)
import Control.Exception (IOException, try)
import Control.Monad (void)
import Data.ByteString qualified as BS
import Data.Foldable (traverse_)
import Data.IORef
import Data.List (minimumBy)
import Data.Maybe (fromMaybe)
{- ORMOLU_DISABLE -}
-- $setup
-- >>> import Circuit.ChannelPoly (iterateSystem)
-- >>> import Circuit.Ends (Ends (..), HasDual (..), commit, emit, open)
-- >>> import Control.Arrow (Kleisli (..), runKleisli)
-- >>> import Data.Text.Encoding (decodeUtf8)
{- ORMOLU_ENABLE -}
import Data.Ord (comparing)
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import System.IO
  ( BufferMode (NoBuffering),
    Handle,
    hClose,
    hFlush,
    hSetBuffering,
  )
import System.Process
import Prelude

-- ---------------------------------------------------------------------------
-- Configuration
-- ---------------------------------------------------------------------------

data ProcConfig = ProcConfig
  { procCommand :: String,
    procArgs :: [String],
    procWorkingDir :: FilePath,
    -- | Boundary grammar of the stdout stream.  Stderr is line-framed
    -- ('lineMarks'); stderr is diagnostics, not dialogue.
    procMarks :: ProcMarks
  }
  deriving (Show, Eq)

defaultProcConfig :: ProcConfig
defaultProcConfig =
  ProcConfig
    { procCommand = "cabal",
      procArgs = ["repl"],
      procWorkingDir = ".",
      procMarks = ghciMarks
    }

-- ---------------------------------------------------------------------------
-- Stream marks
-- ---------------------------------------------------------------------------

-- | The boundary grammar of a process stream: a finite set of marks, each
-- a glyph sequence announcing the end of a frame.  This is the level-0
-- grammar of the process boundary — the free boundary @K + payload@ with
-- @K@ finite, the stateless 'splitFrame' of the mark machine.  Anything
-- stateful (turn counters, roles) lives above this layer.
newtype ProcMarks = ProcMarks [Text]
  deriving (Show, Eq)

-- | Line framing: the newline is the mark, one frame per line.  For line
-- protocols (ACP's JSON-RPC) and for stderr diagnostics.
lineMarks :: ProcMarks
lineMarks = ProcMarks ["\n"]

-- | The ghci prompt grammar.
ghciMarks :: ProcMarks
ghciMarks = ProcMarks ["ghci> ", "\955> "]

-- | The hermes CLI prompt grammar: @❯@ between separator lines when ready.
-- ANSI decorations ride inside the payload; the mark itself is a bare glyph.
-- (Probe card: @coffee\/loom\/hermes-boundary-probe.md@.)
hermesMarks :: ProcMarks
hermesMarks = ProcMarks ["❯"]

-- | The SSE (Server-Sent Events) level-0 grammar: the blank line ends an
-- event frame.  Payload is the @event:\/data:@ block, mark stripped.
sseMarks :: ProcMarks
sseMarks = ProcMarks ["\n\n"]

-- | The stateless mark parse: the earliest mark occurrence in the buffer,
-- giving @(payload, rest)@ — payload before the mark (mark stripped), rest
-- after it.  'Nothing' when no mark has arrived yet.
--
-- Marks are matched on bytes ('encodeUtf8').  UTF-8 is self-synchronising:
-- a valid multi-byte encoding never occurs inside another character, so a
-- byte-level mark cannot false-match, and a mark split across read chunks
-- is found once the buffer accumulates its final byte.
splitFrame :: ProcMarks -> BS.ByteString -> Maybe (BS.ByteString, BS.ByteString)
splitFrame (ProcMarks marks) buf =
  case hits of
    [] -> Nothing
    _ ->
      let (_, markBytes, before, rest) = minimumBy (comparing (\(n, _, _, _) -> n)) hits
       in Just (before, BS.drop (BS.length markBytes) rest)
  where
    hits =
      [ (BS.length before, markBytes, before, rest)
      | mark <- marks,
        let markBytes = encodeUtf8 mark,
        not (BS.null markBytes),
        let (before, rest) = BS.breakSubstring markBytes buf,
        markBytes `BS.isPrefixOf` rest
      ]

-- ---------------------------------------------------------------------------
-- Process ports
-- ---------------------------------------------------------------------------

-- | A process token with three free dual seats: stdin commit, stdout emit,
-- and stderr emit.
--
-- The emit seats block: an emit returns the next complete frame, waiting on
-- the queue when the stream has not produced one yet.  There is no
-- empty-read result — quiet is not an opinion here.
data StdPorts a b c = StdPorts
  { stdIn :: In (Kleisli IO) a,
    stdOut :: Out (Kleisli IO) b,
    stdErr :: Out (Kleisli IO) c,
    stdClose :: IO ()
  }

-- | Spawn a process and open its ports as a 'Loop' 'Either'.
--
-- @encode@ converts a token to bytes written to stdin (+ newline).
-- @decode@ converts a framed payload's bytes back to a token.
--
-- The feedback state is the process.  'Left' = process alive, 'Right' =
-- ports delivered, resources captured by 'stdClose'.
openStdPorts ::
  (a -> BS.ByteString) ->
  (BS.ByteString -> a) ->
  ProcConfig ->
  Loop Either (Kleisli IO) () (StdPorts a a a)
openStdPorts encode decode cfg = Knot (Kleisli step)
  where
    step (Right ()) = do
      let procSpec =
            (proc (procCommand cfg) (procArgs cfg))
              { cwd = Just (procWorkingDir cfg),
                std_in = CreatePipe,
                std_out = CreatePipe,
                std_err = CreatePipe
              }
      (Just stdinH, Just stdoutH, Just stderrH, ph) <- createProcess procSpec
      hSetBuffering stdinH NoBuffering
      hSetBuffering stdoutH NoBuffering
      hSetBuffering stderrH NoBuffering

      -- Mark-carrying stdout uses the linear (empty-residual) mediator so
      -- halt marks are preserved in order.  Diagnostic stderr uses a bounded
      -- weakening mediator: old diagnostics may be dropped when the reader
      -- falls behind, but the process dialogue must never lose a halt.
      qOut <- openChannel Linear
      qErr <- openChannel (NewestN 100)
      outTid <- forkIO (pumpFrames (procMarks cfg) decode stdoutH (sink qOut))
      errTid <- forkIO (pumpFrames lineMarks decode stderrH (sink qErr))

      let ports =
            StdPorts
              { stdIn = In $ \o -> Kleisli $ \a -> do
                  BS.hPutStr stdinH (encode a <> "\n")
                  hFlush stdinH
                  runKleisli (emit o (stdIn ports)) a,
                stdOut = companion qOut,
                stdErr = companion qErr,
                stdClose = do
                  void $ try @IOException (hClose stdinH)
                  terminateProcess ph
                  killThread outTid
                  killThread errTid
              }
      pure (Left ports)
    step (Left ports) =
      pure (Right ports)

-- | Commit one token to a queue end, plugged with unit ends.
sink :: Ends (Kleisli IO) a a -> a -> IO ()
sink q = runKleisli (commit (conjoint q) outU)
  where
    Ends _ outU = open :: Ends (Kleisli IO) () ()

-- | The pumper as an agent: a Moore machine from maybe-chunks to frame
-- lists.  The carrier is @(buffer, pending)@ — the unexplained suffix and
-- the frames awaiting observation.  @Just chunk@ is the percept,
-- 'Nothing' the end-of-stream mark: the EOF flush is content, decided by
-- the same stateless grammar.  This is the level-0 mark machine made
-- literal; 'pumpFrames' is merely its IO interpretation at a 'Handle'.
--
-- >>> iterateSystem (frameAgent lineMarks decodeUtf8) ("", []) [Just "a\n", Just "b", Nothing]
-- [["a"],[],["b"]]
frameAgent :: ProcMarks -> (BS.ByteString -> a) -> Agent (->) (BS.ByteString, [a]) (Maybe BS.ByteString) [a]
frameAgent marks decode = fromEvalSystem $ \(buf, pending) ->
  EP
    ( EK pending,
      EE $ \case
        Just chunk ->
          let (fs, buf') = peel (buf <> chunk)
           in (buf', map decode fs)
        Nothing ->
          (BS.empty, [decode buf | not (BS.null buf)])
    )
  where
    peel buf = case splitFrame marks buf of
      Nothing -> ([], buf)
      Just (p, rest) ->
        let (ps, rest') = peel rest
         in (p : ps, rest')

-- | The same machine as a 'Process': chunk stream in, frame lists out,
-- state carried implicitly.
frameProcess :: ProcMarks -> (BS.ByteString -> a) -> Process (Maybe BS.ByteString) [a]
frameProcess marks decode = systemAsProcess (frameAgent marks decode) (BS.empty, [])

-- | The pumper: the IO interpretation of 'frameAgent' at a 'Handle'.
-- Blocking reads deliver percepts; payloads are sunk into the queue.
-- A mark split across reads completes in the buffer; end-of-stream is the
-- 'Nothing' percept, flushing a partial frame as the final token.
pumpFrames :: ProcMarks -> (BS.ByteString -> a) -> Handle -> (a -> IO ()) -> IO ()
pumpFrames marks decode h snk = go (BS.empty, [])
  where
    sys = frameAgent marks decode
    go st = do
      r <- try @IOException (BS.hGetSome h 4096)
      let input = case r of
            Left _ -> Nothing
            Right bs
              | BS.null bs -> Nothing
              | otherwise -> Just bs
          (outs, st') = run1 sys st input
      traverse_ snk outs
      case input of
        Nothing -> pure ()
        Just _ -> go st'

-- ---------------------------------------------------------------------------
-- Ends / seat view
-- ---------------------------------------------------------------------------

-- | Client view of a process: two 'Ends' sharing stdin, plus resource close.
data ProcEnds a b c = ProcEnds
  { procStdio :: Ends (Kleisli IO) a b,
    procStderr :: Ends (Kleisli IO) a c,
    procClose :: IO ()
  }

-- | Stdin commit + stdout emit as matched 'Ends'.
stdioEnds :: StdPorts a b c -> Ends (Kleisli IO) a b
stdioEnds pp = Ends (stdIn pp) (stdOut pp)

-- | Stdin commit + stderr emit as matched 'Ends'.
stderrEnds :: StdPorts a b c -> Ends (Kleisli IO) a c
stderrEnds pp = Ends (stdIn pp) (stdErr pp)

-- | Open a process and return the dual-seat client view as a 'Loop' 'Either'.
openProc ::
  (a -> BS.ByteString) ->
  (BS.ByteString -> a) ->
  ProcConfig ->
  Loop Either (Kleisli IO) () (ProcEnds a a a)
openProc encode decode cfg =
  openStdPorts encode decode cfg .> Lift portsToProcEnds
  where
    portsToProcEnds = Kleisli $ \pp ->
      pure
        ProcEnds
          { procStdio = stdioEnds pp,
            procStderr = stderrEnds pp,
            procClose = stdClose pp
          }

-- | The wire view of 'StdPorts': one nested 'par' morphism.
portsEnds :: StdPorts a b c -> Loop (,) (Kleisli IO) (a, ((), ())) ((), (b, c))
portsEnds pp = par commitM (par outM errM)
  where
    commitM = Lift (commit (stdIn pp) outUIn)
    outM = Lift (emit (stdOut pp) inUOut)
    errM = Lift (emit (stdErr pp) inUErr)
    Ends _inUIn outUIn = open
    Ends inUOut _ = open
    Ends inUErr _ = open

-- ---------------------------------------------------------------------------
-- In-memory test harness
-- ---------------------------------------------------------------------------

-- | An in-memory echo repl: commit a token, emit the transformed result.
-- No process, no files.  For fast bus-connector testing.
--
-- >>> pp <- echo pure :: IO (StdPorts String String ())
-- >>> runKleisli (commit (stdIn pp) (companion (open :: Ends (Kleisli IO) () ()))) "hi"
-- >>> runKleisli (emit (stdOut pp) (conjoint (open :: Ends (Kleisli IO) () ()))) ()
-- "hi"
echo :: (a -> IO a) -> IO (StdPorts a a ())
echo f = do
  ref <- newIORef Nothing
  let ports =
        StdPorts
          { stdIn = In $ \o -> Kleisli $ \a -> do
              result <- f a
              writeIORef ref (Just result)
              runKleisli (emit o (stdIn ports)) a,
            stdOut = Out $ \_ -> Kleisli $ \_ -> do
              m <- readIORef ref
              writeIORef ref Nothing
              pure (fromMaybe (error "echo: no input yet") m),
            stdErr = Out $ \_ -> Kleisli $ \_ -> pure (),
            stdClose = pure ()
          }
  pure ports
