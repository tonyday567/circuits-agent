{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Process ports: stdin / stdout / stderr as free dual ends.
--
-- A 'ReplPorts' handle is a persistent child process viewed through three
-- independent 'Circuit.Ends' seats plus a close action.
--
-- Internal I/O is 'ByteString'. Constructors take encode/decode adapters:
--
-- @
-- openReplPorts encodeUtf8 decodeUtf8 cfg  -- 'Text'
-- openReplPorts id id cfg                  -- 'ByteString'
-- @
--
-- = Resource lifecycle
--
-- 'openReplPorts' returns a @'Loop' 'Either'@ where the feedback state is
-- the 'ProcessHandle'. 'Left' = process alive, 'Right' = process released.
-- The 'ReplPorts' ends are self-contained — they capture the file paths
-- and byte-offset 'IORef's. 'replPortsClose' terminates the process.
module Circuit.Agent.Repl
  ( -- * Configuration
    ReplConfig (..),
    defaultReplConfig,

    -- * Process ports
    ReplPorts (..),
    openReplPorts,
    attachReplPorts,
    openPtyReplPorts,

    -- * Ends / seat view (client-facing)
    Repl (..),
    stdioEnds,
    stderrEnds,
    openRepl,
    portsEnds,

    -- * In-memory test harness
    echo,
  )
where

import Circuit.Ends (Ends (..), HasUnit (..), In (..), Out (..), commit, emit)
import Circuit.Category ((.>))
import Circuit.Loop (Loop (..))
import Circuit.Tensor (Tensor (..))
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Concurrent (ThreadId, forkIO, killThread)
import Control.Exception (IOException, try)
import Control.Monad (unless, void, when)
import Data.ByteString qualified as BS
import Data.IORef
import Data.Maybe (fromMaybe)
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
import System.Posix.Process (getProcessID)
import System.Posix.Pty (Pty, closePty, spawnWithPty, tryReadPty, writePty)
import System.Process
import System.Timeout (timeout)
import Prelude

-- ---------------------------------------------------------------------------
-- Configuration
-- ---------------------------------------------------------------------------

data ReplConfig = ReplConfig
  { replCommand    :: String,
    replArgs       :: [String],
    replStdinPath  :: FilePath,
    replStdoutPath :: FilePath,
    replStderrPath :: FilePath,
    replWorkingDir :: FilePath
  }
  deriving (Show, Eq)

defaultReplConfig :: ReplConfig
defaultReplConfig = ReplConfig
  { replCommand    = "cabal",
    replArgs       = ["repl"],
    replStdinPath  = "/tmp/repl-stdin",
    replStdoutPath = "/tmp/repl-stdout.md",
    replStderrPath = "/tmp/repl-stderr.md",
    replWorkingDir = "."
  }

-- ---------------------------------------------------------------------------
-- Process ports
-- ---------------------------------------------------------------------------

-- | A process token with three free dual seats: stdin commit, stdout emit,
-- and stderr emit.
data ReplPorts a b c = ReplPorts
  { replIn    :: In  (Kleisli IO) a,
    replOutO   :: Out (Kleisli IO) b,
    replErrO   :: Out (Kleisli IO) c,
    replPortsClose :: IO ()
  }

-- | Spawn a process and open its ports as a 'Loop' 'Either'.
--
-- @encode@ converts a token to bytes written to stdin (+ newline).
-- @decode@ converts bytes read from stdout/stderr back to a token.
--
-- The feedback state is the 'ProcessHandle'. 'Left' = process alive,
-- 'Right' = ports delivered, process handle captured by 'replPortsClose'.
openReplPorts ::
  (a -> BS.ByteString) ->
  (BS.ByteString -> a) ->
  ReplConfig ->
  Loop Either (Kleisli IO) () (ReplPorts a a a)
openReplPorts encode decode cfg = Knot (Kleisli step)
  where
    step (Right ()) = do
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

      outRef <- newIORef (0 :: Int)
      errRef <- newIORef (0 :: Int)

      let ports =
            ReplPorts
              { replIn = In $ \o -> Kleisli $ \a -> do
                  withFile (replStdinPath cfg) WriteMode $ \h -> do
                    BS.hPutStr h (encode a <> "\n")
                    hFlush h
                  runKleisli (emit o (replIn ports)) a,
                replOutO = Out $ \_ -> Kleisli $ \_ ->
                  pollFile decode (replStdoutPath cfg) outRef,
                replErrO = Out $ \_ -> Kleisli $ \_ ->
                  pollFile decode (replStderrPath cfg) errRef,
                replPortsClose = terminateProcess ph
              }
      pure (Left ports)

    step (Left ports) =
      pure (Right ports)

-- | Attach to an existing process's logs without spawning.
attachReplPorts ::
  (a -> BS.ByteString) ->
  (BS.ByteString -> a) ->
  ReplConfig ->
  IO (ReplPorts a a a)
attachReplPorts encode decode cfg = do
  outRef <- newIORef =<< fileLength (replStdoutPath cfg)
  errRef <- newIORef =<< fileLength (replStderrPath cfg)

  let ports =
        ReplPorts
          { replIn = In $ \o -> Kleisli $ \a -> do
              withFile (replStdinPath cfg) WriteMode $ \h -> do
                BS.hPutStr h (encode a <> "\n")
                hFlush h
              runKleisli (emit o (replIn ports)) a,
            replOutO = Out $ \_ -> Kleisli $ \_ ->
              pollFile decode (replStdoutPath cfg) outRef,
            replErrO = Out $ \_ -> Kleisli $ \_ ->
              pollFile decode (replStderrPath cfg) errRef,
            replPortsClose = pure ()
          }
  pure ports

-- | Open a process on a pseudo-terminal.
openPtyReplPorts ::
  (a -> BS.ByteString) ->
  (BS.ByteString -> a) ->
  ReplConfig ->
  IO (ReplPorts a a a)
openPtyReplPorts encode decode cfg = do
  createDirectoryIfMissing True (takeDirectory (replStdoutPath cfg))
  BS.appendFile (replStdoutPath cfg) ""
  (pty, ph) <- spawnWithPty Nothing True (replCommand cfg) (replArgs cfg) (100, 30)
  pumpTid <- forkIO (pumpPtyToLog pty (replStdoutPath cfg))

  ref <- newIORef (0 :: Int)

  let ports =
        ReplPorts
          { replIn = In $ \o -> Kleisli $ \a -> do
              writePty pty (encode a <> "\n")
              runKleisli (emit o (replIn ports)) a,
            replOutO = Out $ \_ -> Kleisli $ \_ ->
              pollFile decode (replStdoutPath cfg) ref,
            replErrO = Out $ \_ -> Kleisli $ \_ ->
              pollFile decode (replStdoutPath cfg) ref,
            replPortsClose = do
              void $ try @IOException (terminateProcess ph)
              void $ timeout 500_000 $ do
                void $ try @IOException (closePty pty)
                killThread pumpTid
          }
  pure ports

-- ---------------------------------------------------------------------------
-- Ends / seat view
-- ---------------------------------------------------------------------------

-- | Client view of a process: two 'Ends' sharing stdin, plus resource close.
data Repl a b c = Repl
  { replStdOut :: Ends (Kleisli IO) a b,
    replStdErr :: Ends (Kleisli IO) a c,
    replClose :: IO ()
  }

-- | Stdin commit + stdout emit as matched 'Ends'.
stdioEnds :: ReplPorts a b c -> Ends (Kleisli IO) a b
stdioEnds pp = Ends (replIn pp) (replOutO pp)

-- | Stdin commit + stderr emit as matched 'Ends'.
stderrEnds :: ReplPorts a b c -> Ends (Kleisli IO) a c
stderrEnds pp = Ends (replIn pp) (replErrO pp)

-- | Open a process and return the dual-seat client view as a 'Loop' 'Either'.
openRepl ::
  (a -> BS.ByteString) ->
  (BS.ByteString -> a) ->
  ReplConfig ->
  Loop Either (Kleisli IO) () (Repl a a a)
openRepl encode decode cfg =
  openReplPorts encode decode cfg .> Lift portsToRepl
  where
    portsToRepl = Kleisli $ \pp ->
      pure Repl
        { replStdOut = stdioEnds pp,
          replStdErr = stderrEnds pp,
          replClose = replPortsClose pp
        }

-- | The wire view of 'ReplPorts': one nested 'par' morphism.
portsEnds :: ReplPorts a b c -> Loop (,) (Kleisli IO) (a, ((), ())) ((), (b, c))
portsEnds pp = par commitM (par outM errM)
  where
    commitM = Lift (commit (replIn pp) outUIn)
    outM    = Lift (emit (replOutO pp) inUOut)
    errM    = Lift (emit (replErrO pp) inUErr)
    Ends _inUIn outUIn = open
    Ends inUOut _ = open
    Ends inUErr _ = open

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

-- | An in-memory echo repl: commit a token, emit the transformed result.
-- No process, no files. For fast bus-connector testing.
--
-- >>> pp <- echo pure
-- >>> runKleisli (commit (replIn pp) (companion (open :: Ends (Kleisli IO) () ()))) "hi"
-- ()
-- >>> runKleisli (emit (replOutO pp) (conjoint (open :: Ends (Kleisli IO) () ()))) ()
-- "hi"
echo :: (a -> IO a) -> IO (ReplPorts a a ())
echo f = do
  ref <- newIORef Nothing
  let ports =
        ReplPorts
          { replIn = In $ \o -> Kleisli $ \a -> do
              result <- f a
              writeIORef ref (Just result)
              runKleisli (emit o (replIn ports)) a,
            replOutO = Out $ \_ -> Kleisli $ \_ -> do
              m <- readIORef ref
              writeIORef ref Nothing
              pure (fromMaybe (error "echo: no input yet") m),
            replErrO = Out $ \_ -> Kleisli $ \_ -> pure (),
            replPortsClose = pure ()
          }
  pure ports

ensureFifo :: FilePath -> IO ()
ensureFifo path = do
  exists <- doesFileExist path
  unless exists $ callProcess "mkfifo" [path]

pollFile :: (BS.ByteString -> a) -> FilePath -> IORef Int -> IO a
pollFile decode path ref = do
  bs <- BS.readFile path
  offset <- readIORef ref
  let new = BS.drop offset bs
  writeIORef ref (BS.length bs)
  pure (decode new)

fileLength :: FilePath -> IO Int
fileLength path = do
  exists <- doesFileExist path
  if exists then fromIntegral . BS.length <$> BS.readFile path else pure 0

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
