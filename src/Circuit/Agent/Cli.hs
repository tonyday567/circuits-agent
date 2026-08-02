{-# LANGUAGE OverloadedStrings #-}

-- | Live CLI agents as opaque shards.
--
-- Lifted down from muster (@Muster.Agent@) and generalised: the invocation
-- recipe is data ('Cli'), not a hermes-shaped law.  A CLI agent is a
-- @Text -> IO Text@ boundary; 'cliShard' seats it as
-- @'Shard' IO [Post] [Post]@ — commit assembles a session prompt from the
-- input posts, emit returns addressed reply posts.
--
-- Session ids are scraped from CLI output and persisted in a file, so
-- context survives across dispatches; a stale session falls back to a
-- fresh one.  Prompts travel via 'proc' argv or stdin — never a shell
-- command line — so multi-line bodies and quoting survive by construction.
module Circuit.Agent.Cli
  ( -- * Invocation recipe
    Cli (..),
    hermesCli,
    kimiCli,
    grokCli,
    parseSessionId,

    -- * Query
    cliQuery,

    -- * Shard adapters
    queryShard,
    cliShard,
    echoShard,
    runShardIO,
    sessionPrompt,
    replyPosts,
  )
where

import Circuit.Agent (Ends (..), Post (..), Shard, close, replyTo, shard)
import Control.Arrow (runKleisli)
import Control.Exception (SomeException, try)
import Control.Monad (when)
import Data.Foldable (for_)
import Data.IORef (atomicModifyIORef', newIORef, writeIORef)
import Data.Maybe (listToMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory)
import System.Process (proc, readCreateProcessWithExitCode)
import Prelude

-- | Invocation recipe for a CLI agent.
--
-- Everything a session needs is plain data; there are no laws here beyond
-- what the CLI itself honours.
data Cli = Cli
  { -- | The executable (e.g. @"hermes"@, @"/bin/sh"@).
    cliCommand :: FilePath,
    -- | Full argv (excluding the command) for one query, given the prompt
    -- and any stored session id ('Nothing' = fresh session).
    cliArgv :: Text -> Maybe Text -> [String],
    -- | Stdin for the process, from the prompt ('const ""' for argv-only CLIs).
    cliStdin :: Text -> String,
    -- | Where the session id is persisted between calls.
    cliSessionFile :: FilePath,
    -- | Scrape a session id from CLI output.  @const Nothing@ for CLIs
    -- without sessions; no session file is then ever written.
    cliSessionId :: Text -> Maybe Text,
    -- | Is this (exit code, output) pair a stale-session response?
    cliStale :: ExitCode -> Text -> Bool,
    -- | Noise filter applied to output before it becomes a reply body.
    cliScrub :: Text -> Text
  }

-- | Recipe for the kimi CLI: @kimi -p \<prompt\> [-r \<sid\>]@,
-- text output.  kimi prints a plain-text resume hint line, so scraping and
-- scrubbing are line-oriented — no JSON needed.  Note: kimi exits 0 even
-- when the prompt fails (and @--auto@ cannot combine with @-p@), so stale
-- detection is output-based.
kimiCli :: Maybe Text -> FilePath -> Cli
kimiCli model sessionFile =
  Cli
    { cliCommand = "kimi",
      cliArgv = \prompt mSid ->
        ["-p", T.unpack prompt]
          <> maybe [] (\m -> ["-m", T.unpack m]) model
          <> maybe [] (\sid -> ["-r", T.unpack sid]) mSid,
      cliStdin = const "",
      cliSessionFile = sessionFile,
      cliSessionId = kimiSessionId,
      cliStale = \_ out ->
        "Session \"" `T.isInfixOf` out && "not found" `T.isInfixOf` out,
      cliScrub = kimiText
    }

-- | Scrape the @To resume this session: kimi -r \<id\>@ hint line.
kimiSessionId :: Text -> Maybe Text
kimiSessionId out =
  case filter ("To resume this session:" `T.isPrefixOf`) (T.lines out) of
    (l : _) -> listToMaybe (reverse (T.words l))
    [] -> Nothing

-- | Drop the resume-hint line; keep the reply text.
kimiText :: Text -> Text
kimiText =
  T.strip
    . T.unlines
    . filter (not . ("To resume this session:" `T.isPrefixOf`))
    . T.lines

-- | Recipe for the grok CLI: @grok -p \<prompt\> --output-format json
-- [--resume \<sid\>]@.  Plain output carries no session id, so the JSON
-- format is used and the @text@\/@sessionId@ fields are extracted.
grokCli :: Maybe Text -> FilePath -> Cli
grokCli model sessionFile =
  Cli
    { cliCommand = "grok",
      cliArgv = \prompt mSid ->
        ["-p", T.unpack prompt, "--output-format", "json"]
          <> maybe [] (\m -> ["-m", T.unpack m]) model
          <> maybe [] (\sid -> ["--resume", T.unpack sid]) mSid,
      cliStdin = const "",
      cliSessionFile = sessionFile,
      cliSessionId = jsonField "sessionId",
      cliStale = \code out ->
        code /= ExitSuccess || "Failed to restore session" `T.isInfixOf` out,
      cliScrub = grokText
    }

-- | Reply text is the JSON @text@ field, unescaped; if there is no such
-- field (an error page), keep the whole output so failures stay visible.
grokText :: Text -> Text
grokText out = maybe (T.strip out) unescapeJson (jsonField "text" out)

-- | Best-effort extraction of a top-level @"key": "value"@ string field
-- (space after the colon optional; escapes respected).  Not a JSON parser —
-- good enough for one-line NDJSON records and flat pretty-printed objects.
jsonField :: Text -> Text -> Maybe Text
jsonField key src =
  case T.breakOn pat src of
    (_, rest)
      | T.null rest -> Nothing
      | otherwise -> jsonString (T.dropWhile (== ' ') (T.drop (T.length pat) rest))
  where
    pat = "\"" <> key <> "\":"

-- | Read a JSON string body after the opening quote, honouring backslash
-- escapes; 'Nothing' if the opening quote is missing or the string is
-- unterminated.
jsonString :: Text -> Maybe Text
jsonString t0 = case T.uncons t0 of
  Just ('"', t) -> go t []
  _ -> Nothing
  where
    go rest acc = case T.uncons rest of
      Nothing -> Nothing
      Just ('\\', r) -> case T.uncons r of
        Just (c, r') -> go r' (c : '\\' : acc)
        Nothing -> Nothing
      Just ('"', _) -> Just (T.pack (reverse acc))
      Just (c, r') -> go r' (c : acc)

-- | Unescape the common JSON string escapes; unknown escapes are kept
-- literally.  Best-effort, not a full @\\u@ decoder.
unescapeJson :: Text -> Text
unescapeJson t = case T.uncons t of
  Nothing -> t
  Just ('\\', r) -> case T.uncons r of
    Just (c, r') -> case esc c of
      Just u -> T.cons u (unescapeJson r')
      Nothing -> T.cons '\\' (T.cons c (unescapeJson r'))
    Nothing -> "\\"
  Just (c, r) -> T.cons c (unescapeJson r)
  where
    esc 'n' = Just '\n'
    esc 'r' = Just '\r'
    esc 't' = Just '\t'
    esc '"' = Just '"'
    esc '\\' = Just '\\'
    esc '/' = Just '/'
    esc _ = Nothing

-- | Scrape a @session_id:@ line from CLI output.
parseSessionId :: Text -> Maybe Text
parseSessionId out =
  case filter ("session_id:" `T.isPrefixOf`) (T.lines out) of
    (line : _) ->
      let sid = T.strip (T.drop (T.length "session_id:") line)
       in if T.null sid then Nothing else Just sid
    [] -> Nothing

-- | Recipe for the hermes CLI: @hermes chat -q \<prompt\> … --resume \<sid\>@.
hermesCli :: Maybe Text -> Maybe Text -> FilePath -> Cli
hermesCli model provider sessionFile =
  Cli
    { cliCommand = "hermes",
      cliArgv = \prompt mSid ->
        ["chat", "-q", T.unpack prompt]
          <> maybe [] (\m -> ["-m", T.unpack m]) model
          <> maybe [] (\p -> ["--provider", T.unpack p]) provider
          <> ["--yolo", "-Q", "--max-turns", "90"]
          <> maybe [] (\sid -> ["--resume", T.unpack sid]) mSid,
      cliStdin = const "",
      cliSessionFile = sessionFile,
      cliSessionId = parseSessionId,
      cliStale = \code out ->
        code /= ExitSuccess
          || "No session found matching" `T.isInfixOf` out
          || "Session not found" `T.isInfixOf` out,
      cliScrub = cleanCliOut
    }

-- | One query against a CLI agent.
--
-- First call (or no stored session) runs fresh; subsequent calls resume the
-- stored session id.  A stale session falls back to fresh and records the
-- new id.  Scraped ids are re-persisted on every successful call, so
-- server-side session rotation is followed.
cliQuery :: Cli -> Text -> IO Text
cliQuery cli prompt = do
  mSid <- readStoredSession (cliSessionFile cli)
  case mSid of
    Nothing -> fresh
    Just sid -> do
      (code, out) <- run (Just sid)
      if cliStale cli code out
        then fresh
        else do
          scrape out
          pure (cliScrub cli out)
  where
    run mSid = do
      (code, out, err) <-
        readCreateProcessWithExitCode
          (proc (cliCommand cli) (cliArgv cli prompt mSid))
          (cliStdin cli prompt)
      pure (code, T.pack out <> T.pack err)
    fresh = do
      (code, out) <- run Nothing
      when (code /= ExitSuccess) $
        fail
          ( "cliQuery: "
              <> cliCommand cli
              <> " exited "
              <> show code
              <> ": "
              <> T.unpack (T.take 200 out)
          )
      scrape out
      pure (cliScrub cli out)
    scrape out =
      for_ (cliSessionId cli out) (writeStoredSession (cliSessionFile cli))

readStoredSession :: FilePath -> IO (Maybe Text)
readStoredSession path = do
  exists <- doesFileExist path
  if not exists
    then pure Nothing
    else do
      res <- try @SomeException (TIO.readFile path)
      pure $ case res of
        Left _ -> Nothing
        Right t ->
          let sid = T.strip t
           in if T.null sid then Nothing else Just sid

writeStoredSession :: FilePath -> Text -> IO ()
writeStoredSession path sid = do
  createDirectoryIfMissing True (takeDirectory path)
  TIO.writeFile path sid

-- | Hermes-flavoured TUI noise filter: drops session chatter, decorative
-- rules, and ANSI lines; keeps plain reply text.
cleanCliOut :: Text -> Text
cleanCliOut =
  T.unlines
    . filter keep
    . map T.strip
    . T.lines
  where
    keep l
      | T.null l = False
      | "session_id:" `T.isPrefixOf` l = False
      | "Warning:" `T.isPrefixOf` l = False
      | "Resumed session" `T.isInfixOf` l = False
      | "Reached maximum" `T.isInfixOf` l = False
      | "Requesting summary" `T.isInfixOf` l = False
      | "No session found matching" `T.isInfixOf` l = False
      | "Use 'hermes sessions list'" `T.isInfixOf` l = False
      | "Resume this session with:" `T.isInfixOf` l = False
      | "Shutting down" `T.isInfixOf` l = False
      | "Session:" `T.isPrefixOf` l = False
      | "Duration:" `T.isPrefixOf` l = False
      | "Messages:" `T.isPrefixOf` l = False
      | "⚕" `T.isPrefixOf` l = False
      | "❯" `T.isPrefixOf` l = False
      | T.any (== '\x1b') l = False
      | isDecorative l = False
      | otherwise = True
    isDecorative t =
      T.all (\c -> c == ' ' || c == '\r' || c `elem` ("─│┌┐└┘" :: String)) t

-- ---------------------------------------------------------------------------
-- Living agent as Shard IO [Post] [Post]
-- ---------------------------------------------------------------------------

-- | Session assembly for the opaque seat: bodies, oldest-first, one per line.
--
-- This is the discoverable side of the boundary (data).  How the CLI folds
-- it is not.
sessionPrompt :: [Post Text] -> Text
sessionPrompt = T.intercalate "\n" . map body

-- | Build reply posts from a cleaned agent response.
--
-- Addresses the last input's sender, preserves any other names on the
-- original wire (e.g. the bus channel), and threads onto the last input's
-- sender (see 'replyTo').  Empty reply → no posts (quiet).
replyPosts :: Text -> [Post Text] -> Text -> [Post Text]
replyPosts who ins reply =
  case (listToMaybe (reverse ins), T.strip reply) of
    (_, r) | T.null r -> []
    (Nothing, _) -> []
    (Just lastIn, r) -> [replyTo who lastIn r]

-- | Opaque evaluate seat: any @Text -> IO Text@ behind list ends.
--
-- Commit assembles a session prompt from the input posts; emit is
-- 'replyPosts' of the query result (empty = quiet).
queryShard :: Text -> (Text -> IO Text) -> IO (Shard IO [Post Text] [Post Text])
queryShard who query = do
  outbox <- newIORef []
  pure $
    shard
      ( \ins ->
          if null ins
            then writeIORef outbox []
            else do
              reply <- query (sessionPrompt ins)
              writeIORef outbox (replyPosts who ins reply)
      )
      (atomicModifyIORef' outbox ([],))

-- | A live CLI agent as a list 'Shard'.  Session file and process stay
-- inside @IO@ — apply-only at this boundary.  @who@ is the agent nick
-- (from on emitted posts).
cliShard :: Text -> Cli -> IO (Shard IO [Post Text] [Post Text])
cliShard who cli = queryShard who (cliQuery cli)

-- | Mock seat: reply body is the session prompt (echo).
--
-- Demonstrates the living-agent path without a CLI.
echoShard :: Text -> IO (Shard IO [Post Text] [Post Text])
echoShard who = queryShard who pure

-- | One closed shard turn: commit @ins@, emit replies.
runShardIO :: Shard IO [Post Text] [Post Text] -> [Post Text] -> IO [Post Text]
runShardIO sh = runKleisli (close (conjoint sh) (companion sh))
