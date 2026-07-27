{-# LANGUAGE OverloadedStrings #-}

-- | Process ports: stdin / stdout / stderr as free dual ends.
--
-- A 'ProcessPorts' handle is a persistent child process viewed through three
-- independent 'Circuit.Ends' seats plus a close action.  The stdin seat
-- commits lines; the stdout and stderr seats emit new log lines since the
-- last poll.  Each seat carries its own cursor on the append-only log.
--
-- The monoidal / wire view is 'portsEnds':
-- @par peIn (par peOut peErr)@.
module Circuit.Agent.Process
  ( -- * Configuration
    ReplConfig (..),
    defaultReplConfig,

    -- * Process ports
    ProcessPorts (..),
    openProcessPorts,
    attachProcessPorts,
    openPtyProcessPorts,
    -- * Ends / seat view (client-facing)
    ProcessSeat (..),
    stdioEnds,
    stderrEnds,
    openProcessSeat,
    portsEnds,
  )
where

import Circuit.Ends (Ends (..), HasUnit (..), In (..), Out (..), commit, emit)
import Circuit.Layer (run)
import Circuit.Loop (Loop (..))
import Circuit.Tensor (Tensor (..))
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Concurrent (ThreadId, forkIO, killThread)
import Control.Exception (IOException, bracket, throwIO, try)
import Control.Monad (unless, void, forM_, when)
import Cursor qualified as Cur
import Data.Maybe (fromMaybe)
import Data.ByteString qualified as BS
import Data.IORef
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Data.Text.IO qualified as TIO
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.FilePath (takeDirectory)
import System.IO
  ( BufferMode (NoBuffering),
    IOMode (AppendMode, ReadMode, WriteMode),
    hClose,
    hFlush,
    hSetBuffering,
    openFile,
    withFile,
  )
import System.IO.Error (userError)
import System.Posix.Process (getProcessID)
import System.Posix.Pty (Pty, closePty, spawnWithPty, tryReadPty, writePty)
import System.Process
import System.Timeout (timeout)
import Prelude

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Circuit (run, par)
-- >>> import Circuit.Category ((.>))
-- >>> import Circuit.Ends (Ends (..), HasUnit (..), In (..), Out (..), close, commit, emit)
-- >>> import Circuit.Loop (Loop (..))
-- >>> import Control.Arrow (Kleisli (..), runKleisli)
-- >>> import Data.IORef
-- >>> import Data.Text (Text)

-- ---------------------------------------------------------------------------
-- Configuration
-- ---------------------------------------------------------------------------

data ReplConfig = ReplConfig
  { replCommand    :: String,
    replArgs       :: [String],
    replStdinPath  :: FilePath,
    replStdoutPath :: FilePath,
    replStderrPath :: FilePath,
    replWorkingDir :: FilePath,
    -- | Optional explicit cursor file for the stdout log. When 'Nothing',
    -- the default @<log>.cursor@ (open) or @<log>.cursor-attach-<pid>@
    -- (attach) is used.
    replCursorPath :: Maybe FilePath
  }
  deriving (Show, Eq)

defaultReplConfig :: ReplConfig
defaultReplConfig = ReplConfig
  { replCommand    = "cabal",
    replArgs       = ["repl"],
    replStdinPath  = "/tmp/repl-stdin",
    replStdoutPath = "/tmp/repl-stdout.md",
    replStderrPath = "/tmp/repl-stderr.md",
    replWorkingDir = ".",
    replCursorPath = Nothing
  }

-- ---------------------------------------------------------------------------
-- Process ports: stdin / stdout / stderr
-- ---------------------------------------------------------------------------

-- | A process token with three free dual seats: stdin commit, stdout emit,
-- and stderr emit. This is the splayed / store view: @(peIn, (peOut, peErr))@
-- as independent ends, not a monoidal object.
--
-- The monoidal / wire view is 'portsEnds': @par peIn (par peOut peErr)@.
--
-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Circuit (run, par)
-- >>> import Circuit.Category ((.>))
-- >>> import Circuit.Ends (Ends (..), HasUnit (..), In (..), Out (..), close, commit, emit)
-- >>> import Circuit.Loop (Loop (..))
-- >>> import Control.Arrow (Kleisli (..), runKleisli)
-- >>> import Data.Text (Text)
data ProcessPorts a b c = ProcessPorts
  { peIn    :: In  (Kleisli IO) a
  -- ^ Write TO the process (stdin / commit).
  , peOut   :: Out (Kleisli IO) b
  -- ^ Read FROM the process stdout.
  , peErr   :: Out (Kleisli IO) c
  -- ^ Read FROM the process stderr.
  , peClose :: IO ()
  -- ^ Release handles / kill child / detach.
  }

-- | Open a process with three line ports: stdin FIFO, stdout log, stderr log.
--
-- Spawns the configured command with stdin/stdout/stderr redirected, and
-- returns the three free ends plus a close action. Stdout and stderr each
-- have their own cursor on their respective log files.
openProcessPorts :: ReplConfig -> IO (ProcessPorts [Text] [Text] [Text])
openProcessPorts cfg = do
  ensureFifo (replStdinPath cfg)
  stdoutH <- openFile (replStdoutPath cfg) AppendMode
  stderrH <- openFile (replStderrPath cfg) AppendMode
  hSetBuffering stdoutH NoBuffering
  hSetBuffering stderrH NoBuffering
  stdinH <- openFile (replStdinPath cfg) ReadMode
  let procSpec =
        (proc (replCommand cfg) (replArgs cfg))
          { cwd = Just (replWorkingDir cfg),
            std_in = UseHandle stdinH,
            std_out = UseHandle stdoutH,
            std_err = UseHandle stderrH
          }
  (_, _, _, ph) <- createProcess procSpec
  hClose stdinH
  hClose stdoutH
  hClose stderrH

  let stdoutCursorFile = fromMaybe (cursorPath cfg) (replCursorPath cfg)
  stdoutCursor <- Cur.newFile stdoutCursorFile
  Cur.set stdoutCursor 0
  stderrCursor <- Cur.newFile (stderrCursorPath cfg)
  Cur.set stderrCursor 0
  lastOutP <- newIORef Nothing
  lastErrP <- newIORef Nothing

  let commit ts = mapM_ (\t -> withFile (replStdinPath cfg) WriteMode $ \h -> do
        TIO.hPutStrLn h t
        hFlush h) ts
      peIn_ = In $ \o -> Kleisli $ \ts -> commit ts >> runKleisli (emit o peIn_) ts
      peOut_ = Out $ \_ -> Kleisli $ \_ -> logEmit (replStdoutPath cfg) stdoutCursor lastOutP
      peErr_ = Out $ \_ -> Kleisli $ \_ -> logEmit (replStderrPath cfg) stderrCursor lastErrP
      closeAction = terminateProcess ph

  pure ProcessPorts { peIn = peIn_, peOut = peOut_, peErr = peErr_, peClose = closeAction }

-- | Attach to an existing process's logs without spawning.
--
-- Cursors start at the current end of both logs so the next poll only sees
-- future output. Each attachment gets its own cursor files (PID-suffix) so
-- multiple observers on the same logs do not interfere.
attachProcessPorts :: ReplConfig -> IO (ProcessPorts [Text] [Text] [Text])
attachProcessPorts cfg = do
  contentOut <- readLogContent (replStdoutPath cfg)
  contentErr <- readLogContent (replStderrPath cfg)
  stdoutCursorFile <- case replCursorPath cfg of
    Just p  -> pure p
    Nothing -> attachCursorPath (replStdoutPath cfg)
  stderrCursorFile <- attachCursorPath (replStderrPath cfg)
  stdoutCursor <- Cur.newFile stdoutCursorFile
  -- Only seek to end for a fresh cursor (position 0). An existing cursor
  -- file should resume from its stored position.
  outPos <- Cur.get stdoutCursor
  when (outPos == 0) $ Cur.seekEnd stdoutCursor (fst (splitComplete contentOut))
  stderrCursor <- Cur.newFile stderrCursorFile
  stderrPos <- Cur.get stderrCursor
  when (stderrPos == 0) $ Cur.seekEnd stderrCursor (fst (splitComplete contentErr))
  lastOutP <- newIORef Nothing
  lastErrP <- newIORef Nothing

  let commit ts = mapM_ (\t -> withFile (replStdinPath cfg) WriteMode $ \h -> do
        TIO.hPutStrLn h t
        hFlush h) ts
      peIn_ = In $ \o -> Kleisli $ \ts -> commit ts >> runKleisli (emit o peIn_) ts
      peOut_ = Out $ \_ -> Kleisli $ \_ -> logEmit (replStdoutPath cfg) stdoutCursor lastOutP
      peErr_ = Out $ \_ -> Kleisli $ \_ -> logEmit (replStderrPath cfg) stderrCursor lastErrP
      closeAction = pure () -- attach does not own the process

  pure ProcessPorts { peIn = peIn_, peOut = peOut_, peErr = peErr_, peClose = closeAction }

-- | Open a process on a pseudo-terminal.
--
-- Stdout and stderr are combined by the PTY, so both 'peOut' and 'peErr'
-- read from the same log.  Useful for targets (e.g. @python3 -q@) that
-- detect whether stdin is a terminal.
openPtyProcessPorts :: ReplConfig -> IO (ProcessPorts [Text] [Text] [Text])
openPtyProcessPorts cfg = do
  createDirectoryIfMissing True (takeDirectory (replStdoutPath cfg))
  appendFile (replStdoutPath cfg) ""
  (pty, ph) <- spawnWithPty Nothing True (replCommand cfg) (replArgs cfg) (100, 30)
  pumpTid  <- forkIO (pumpPtyToLog pty (replStdoutPath cfg))

  let cursorFile = fromMaybe (cursorPath cfg) (replCursorPath cfg)
  cursor <- Cur.newFile cursorFile
  Cur.set cursor 0
  lastOutP <- newIORef Nothing
  lastErrP <- newIORef Nothing

  let commitAction ts = mapM_ (\t -> writePty pty (encodeUtf8 (t <> "\n"))) ts
      peIn_ = In $ \o -> Kleisli $ \ts -> commitAction ts >> runKleisli (emit o peIn_) ts
      peOut_ = Out $ \_ -> Kleisli $ \_ -> logEmit (replStdoutPath cfg) cursor lastOutP
      peErr_ = Out $ \_ -> Kleisli $ \_ -> logEmit (replStdoutPath cfg) cursor lastErrP
      closeAction = do
        void $ try @IOException (terminateProcess ph)
        void $ timeout 500_000 $ do
          void $ try @IOException (closePty pty)
          killThread pumpTid

  pure ProcessPorts { peIn = peIn_, peOut = peOut_, peErr = peErr_, peClose = closeAction }

-- | Stdin commit + stdout emit as matched 'Ends'.
--
-- Shares 'peIn' with 'stderrEnds': two seats, one commit port.
--
-- >>> ref <- newIORef ([] :: [Text])
-- >>> let cin = In $ \o -> Kleisli $ \ts -> writeIORef ref ts >> runKleisli (emit o cin) ts
-- >>> let cout = Out $ \_ -> Kleisli $ \_ -> readIORef ref
-- >>> let pp = ProcessPorts { peIn = cin, peOut = cout, peErr = cout, peClose = pure () }
-- >>> let e = stdioEnds pp
-- >>> runKleisli (commit (conjoint e) (companion (open :: Ends (Kleisli IO) () ()))) ["hi"]
-- ()
-- >>> runKleisli (emit (companion e) (conjoint (open :: Ends (Kleisli IO) () ()))) ()
-- ["hi"]
stdioEnds :: ProcessPorts a b c -> Ends (Kleisli IO) a b
stdioEnds pp = Ends (peIn pp) (peOut pp)

-- | Stdin commit + stderr emit as matched 'Ends'.
--
-- Same conjoint as 'stdioEnds' ('peIn'); independent companion ('peErr').
stderrEnds :: ProcessPorts a b c -> Ends (Kleisli IO) a c
stderrEnds pp = Ends (peIn pp) (peErr pp)

-- | Client view of a process: two 'Ends' sharing stdin, plus resource close.
--
-- @
--   psOut = Ends peIn peOut   -- commit commands, poll stdout
--   psErr = Ends peIn peErr   -- same commit port, poll stderr
-- @
--
-- Commit through either conjoint reaches the process once (shared 'In').
-- Prefer a single commit path in a turn (usually 'psOut') so lines are not
-- double-written; emit on both. 'psClose' is process lifecycle — not the
-- categorical counit of 'Ends'.
--
-- 'ProcessPorts' remains the splayed store / open plumbing.
data ProcessSeat a b c = ProcessSeat
  { psOut :: Ends (Kleisli IO) a b,
    psErr :: Ends (Kleisli IO) a c,
    psClose :: IO ()
  }

-- | Open a process and return the dual-seat client view.
openProcessSeat :: ReplConfig -> IO (ProcessSeat [Text] [Text] [Text])
openProcessSeat cfg = do
  pp <- openProcessPorts cfg
  pure
    ProcessSeat
      { psOut = stdioEnds pp,
        psErr = stderrEnds pp,
        psClose = peClose pp
      }

-- | The wire view of 'ProcessPorts': one nested 'par' morphism.
--
-- Store @(peIn, (peOut, peErr))@ becomes
-- @par commit (par out err) :: Loop (,) (Kleisli IO) (a, ((), ())) ((), (b, c))@.
--
-- Each free end is unit-plugged with its own 'open' @()@ pair; the three
-- unit plugs are independent channels.
--
-- >>> let pp = ProcessPorts { peIn = undefined, peOut = undefined, peErr = undefined, peClose = pure () }
-- >>> let _wire = portsEnds pp :: Loop (,) (Kleisli IO) ([Text], ((), ())) ((), ([Text], [Text]))
--
-- Round-trip doctest (no process spawn): commit writes a shared cell; the
-- nested par reads it back through both @Out@ seats.
--
-- >>> ref <- newIORef ([] :: [Text])
-- >>> let commit = In $ \o -> Kleisli $ \ts -> writeIORef ref ts >> runKleisli (emit o commit) ts
-- >>> let emit   = Out $ \_ -> Kleisli $ \_ -> readIORef ref
-- >>> let pp' = ProcessPorts { peIn = commit, peOut = emit, peErr = emit, peClose = pure () }
-- >>> runKleisli (run (portsEnds pp')) (["hello"], ((), ()))
-- ((),(["hello"],["hello"]))
portsEnds :: ProcessPorts a b c -> Loop (,) (Kleisli IO) (a, ((), ())) ((), (b, c))
portsEnds pp = par commitM (par outM errM)
  where
    commitM = Lift (commit (peIn pp) outUIn)
    outM    = Lift (emit (peOut pp) inUOut)
    errM    = Lift (emit (peErr pp) inUErr)
    Ends _inUIn outUIn = open
    Ends inUOut _ = open
    Ends inUErr _ = open

-- ---------------------------------------------------------------------------
-- Shared helpers
-- ---------------------------------------------------------------------------

ensureFifo :: FilePath -> IO ()
ensureFifo path = do
  exists <- doesFileExist path
  unless exists $ callProcess "mkfifo" [path]

cursorPath :: ReplConfig -> FilePath
cursorPath cfg = replStdoutPath cfg <> ".cursor"

stderrCursorPath :: ReplConfig -> FilePath
stderrCursorPath cfg = replStderrPath cfg <> ".cursor"

attachCursorPath :: FilePath -> IO FilePath
attachCursorPath logPath = do
  pid <- getProcessID
  pure (logPath <> ".cursor-attach-" <> show pid)

pumpPtyToLog :: Pty -> FilePath -> IO ()
pumpPtyToLog pty logPath = go
  where
    go = do
      r <- try @IOException (tryReadPty pty)
      case r of
        Left _            -> pure ()
        Right (Left _)    -> go
        Right (Right bs)
          | BS.null bs    -> go
          | otherwise     -> BS.appendFile logPath bs >> go

readLogContent :: FilePath -> IO Text
readLogContent fp = do
  exists <- doesFileExist fp
  if not exists then pure "" else decodeUtf8 <$> BS.readFile fp

splitComplete :: Text -> ([Text], Maybe Text)
splitComplete content
  | T.null content                = ([], Nothing)
  | T.isSuffixOf "\n" content    = (T.lines content, Nothing)
  | otherwise                     =
      let parts = T.splitOn "\n" content
       in case parts of
            [] -> ([], Nothing)
            _  -> (init parts, Just (last parts))

logEmit :: FilePath -> Cur.Cursor -> IORef (Maybe Text) -> IO [Text]
logEmit logPath cursor lastP = do
  content <- readLogContent logPath
  let (complete, mPartial) = splitComplete content
  news <- Cur.pollLines cursor complete
  prev <- readIORef lastP
  writeIORef lastP mPartial
  let partialNews = case (news, prev, mPartial) of
        (_, _, Nothing)          -> []
        (_ : _, _, Just p)       -> [p]
        ([], Just old, Just p)
          | old == p             -> []
        ([], _, Just p)          -> [p]
  pure (news <> partialNews)
