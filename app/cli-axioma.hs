{-# LANGUAGE OverloadedStrings #-}

-- | Oracles for 'Circuit.Agent.Cli'.
--
-- No invented-API laws: the oracles are exact.  The pure side is checked
-- against 'echoShard' (reply = session prompt).  The process side is
-- checked against a fake CLI (a /bin/sh script) whose behaviour is fully
-- known: it prints a fixed @session_id@, echoes its argv and stdin, and
-- (when told) rejects --resume so the stale-fallback path is exercised.
module Main (main) where

import Circuit.Agent (Post (..), branches, cone, mkPost, replyTo, sortNub, synthesis)
import Circuit.Agent.Cli
import Cursor (newMem, pollNumberedFile)
import Control.Monad (when)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory
  ( createDirectoryIfMissing,
    doesFileExist,
    getPermissions,
    getTemporaryDirectory,
    removeFile,
    setOwnerExecutable,
    setPermissions,
  )
import System.Environment (getEnv, setEnv, unsetEnv)
import System.Exit (ExitCode (..), exitFailure)
import System.FilePath ((</>))
import Prelude

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

p1 :: Post Text
p1 = mkPost "tony" ["kimi"] "hello"

p2 :: Post Text
p2 = mkPost "grok" ["kimi", "tony"] "line1\nline2"

-- | Fake CLI whose behaviour is fully known:
--
-- - rejects @--resume@ when FAIL_RESUME=1 (stale-session simulation)
-- - prints a fixed session id
-- - echoes argv and stdin verbatim
fakeScript :: String
fakeScript =
  unlines
    [ "#!/bin/sh",
      "if [ \"$1\" = \"--resume\" ] && [ \"$FAIL_RESUME\" = \"1\" ]; then",
      "  echo \"No session found matching $2\"",
      "  exit 1",
      "fi",
      "echo \"session_id: fake-42\"",
      "echo \"argv:$*\"",
      "printf 'stdin:'",
      "cat"
    ]

-- | Recipe for the fake CLI: prompt on stdin, resume id as @--resume sid@.
fakeCli :: FilePath -> FilePath -> Cli
fakeCli script sessionFile =
  Cli
    { cliCommand = "/bin/sh",
      cliArgv = \_ mSid -> [script] <> maybe [] (\sid -> ["--resume", T.unpack sid]) mSid,
      cliStdin = T.unpack,
      cliSessionFile = sessionFile,
      cliSessionId = parseSessionId,
      cliStale = \code out ->
        code /= ExitSuccess || "No session found matching" `T.isInfixOf` out,
      cliScrub = id
    }

-- | Canned @kimi@ binary: emits the exact shapes kimiCli scrapes and
-- scrubs — reply lines, a plain-text resume hint, and (with FAIL_RESUME=1)
-- a stale-session error.  Fully known behaviour = exact oracle.
fakeKimiScript :: String
fakeKimiScript =
  unlines
    [ "#!/bin/sh",
      "PROMPT=\"\"; SID=\"\"",
      "while [ $# -gt 0 ]; do",
      "  case \"$1\" in",
      "    -p) PROMPT=\"$2\"; shift 2;;",
      "    -r) SID=\"$2\"; shift 2;;",
      "    *) shift;;",
      "  esac",
      "done",
      "if [ -n \"$SID\" ] && [ \"$FAIL_RESUME\" = \"1\" ]; then",
      "  echo \"error: failed to run prompt: Session \\\"$SID\\\" not found.\"",
      "  exit 0",
      "fi",
      "if [ -n \"$SID\" ]; then",
      "  echo \"kimi resumed as $SID\"",
      "else",
      "  echo \"kimi fresh\"",
      "fi",
      "echo \"kimi heard: $PROMPT\"",
      "echo \"To resume this session: kimi -r session_fake-kimi\""
    ]

-- | Canned @grok@ binary: emits the exact JSON shapes grokCli scrapes —
-- a @text@ field with escapes and a @sessionId@ field; rejects --resume
-- with a restore error when FAIL_RESUME=1.
fakeGrokScript :: String
fakeGrokScript =
  unlines
    [ "#!/bin/sh",
      "SID=\"\"",
      "while [ $# -gt 0 ]; do",
      "  case \"$1\" in",
      "    --resume) SID=\"$2\"; shift 2;;",
      "    *) shift;;",
      "  esac",
      "done",
      "if [ -n \"$SID\" ] && [ \"$FAIL_RESUME\" = \"1\" ]; then",
      "  printf '%s\\n' 'Error: Failed to restore session from remote: 404 Not Found'",
      "  exit 0",
      "fi",
      "printf '%s\\n' '{'",
      "if [ -n \"$SID\" ]; then",
      "  printf '%s\\n' \"  \\\"text\\\": \\\"grok resumed as $SID\\\",\"",
      "else",
      "  printf '%s\\n' '  \"text\": \"line1\\nline2 \\\"quoted\\\"\",'",
      "fi",
      "printf '%s\\n' '  \"sessionId\": \"grok-fake-uuid\"'",
      "printf '%s\\n' '}'"
    ]

-- | Write an executable script and put its directory first on PATH.
installFake :: FilePath -> String -> IO ()
installFake path contents = do
  TIO.writeFile path (T.pack contents)
  perms <- getPermissions path
  setPermissions path (setOwnerExecutable True perms)

-- | Remove a file if present (session files persist between runs).
wipe :: FilePath -> IO ()
wipe f = do
  e <- doesFileExist f
  when e (removeFile f)

main :: IO ()
main = do
  putStrLn "sessionPrompt / replyPosts (data side)"
  assert
    "sessionPrompt concatenates bodies oldest-first"
    (sessionPrompt [p1, p2] == "hello\nline1\nline2")
  assert
    "replyPosts addresses last sender, preserves wire"
    (replyPosts "kimi" [p1, p2] [1] "sure" == [replyTo "kimi" 1 p2 "sure"])
  assert
    "whitespace reply is quiet"
    (replyPosts "kimi" [p1] [0] "  \n " == [])
  assert
    "empty input is quiet"
    (replyPosts "kimi" [] [] "x" == [])

  putStrLn "echoShard (exact mock oracle)"
  sh <- echoShard "kimi"
  r1 <- runShardIO sh [p1, p2]
  assert
    "echo reply body is the session prompt"
    (map body r1 == [sessionPrompt [p1, p2]]
       && all ((== "kimi") . from) r1
       && all ((== ["grok", "tony"]) . to) r1)
  r2 <- runShardIO sh [p1]
  assert
    "outbox drains between closes"
    (map body r2 == ["hello"]
       && all ((== "kimi") . from) r2
       && all ((== ["tony"]) . to) r2)
  r3 <- runShardIO sh []
  assert "empty commit emits nothing" (null r3)

  putStrLn "thread (ancestry) oracles"
  assert "root post has no parents" (thread p1 == [])
  assert
    "reply threads onto the parent id"
    (thread (replyTo "kimi" 1 p2 "x" :: Post Text) == [1])
  assert
    "replyPosts threads onto the last input's id"
    (case replyPosts "kimi" [p1, p2] [0, 1] "sure" of
       [rp] -> thread rp == [1]
       _ -> False)
  let r1' :: Post Text
      r1' = replyTo "kimi" 1 p2 "a"
      r2' :: Post Text
      r2' = replyTo "tony" 2 r1' "b"
  assert
    "branches of a root are its sender"
    (branches [p1, p2] p2 == [["grok"]])
  assert
    "branches of a reply are pure cons"
    (branches [p1, p2] r1' == map ("kimi" :) (branches [p1, p2] p2))
  assert
    "branches unfolds a three-post thread"
    (branches [p1, p2, r1'] r2' == [["tony", "kimi", "grok"]])
  let r0 :: Post Text
      r0 = replyTo "kimi" 0 p1 "old"
  assert
    "same-named posts are disambiguated by exact id"
    (branches [p1, p2, r0, r1'] r2' == [["tony", "kimi", "grok"]])

  putStrLn "synthesis (wire-merge) oracles"
  let syn :: Post Text
      syn = synthesis "sum" ["human"] [1, 0] "Σ"
  assert
    "synthesis ancestry is a normalised set of parent ids"
    (thread syn == [0, 1])
  assert
    "synthesis ancestry discards duplicate ids"
    (thread (synthesis "sum" [] [0, 0] "Σ" :: Post Text) == [0])
  assert
    "branches of a synthesis has one path per parent"
    (branches [p1, p2] syn == [["sum", "tony"], ["sum", "grok"]])
  assert
    "branches of a synthesis continues through each parent"
    (branches [p1, p2, r1'] (synthesis "sum" [] [2, 0] "Σ" :: Post Text)
       == [["sum", "tony"], ["sum", "kimi", "grok"]])

  putStrLn "honest provenance oracles"
  let syn2 = case synthesisPosts "sum" [p2, p1, r1'] [1, 0, 2] "Σ2" of
        [s] -> s
        _ -> error "synthesisPosts: expected one post"
      prior = [p2, p1, r1']
  assert
    "synthesisPosts ancestry cites every input id"
    (thread syn2 == [0, 1, 2])
  assert
    "synthesisPosts audience is senders and wires, minus self"
    (to syn2 == ["grok", "kimi", "tony"])
  assert "synthesisPosts is quiet on empty reply" $
    null (synthesisPosts "sum" [p1] [0] "  ")
  assert "synthesisPosts is quiet on no inputs" $
    null (synthesisPosts "sum" [] [] "x")
  assert
    "ancestry monotonicity: every parent id is a valid prior index"
    (all (< fromIntegral (length prior)) (thread syn2))
  assert
    "cone-union law: cone of a synthesis is the union of parent cones"
    (cone prior (synthesis "sum" [] [2, 0] "Σ")
       == sortNub ("sum" : concatMap (cone prior) [r1', p1]))
  assert
    "cone of a synthesis is the contributor set"
    (cone prior (synthesis "sum" [] [2, 0] "Σ") == ["grok", "kimi", "sum", "tony"])

  putStrLn "cursor numbered poll oracles"
  tmpC <- getTemporaryDirectory
  let logf = tmpC </> "circuits-agent-cursor-axioma.log"
  wipe logf
  TIO.writeFile logf "a\nb\n"
  cur <- newMem 0
  r1 <- pollNumberedFile cur logf
  assert "complete lines are numbered 1-based" (r1 == [(1, "a"), (2, "b")])
  r2 <- pollNumberedFile cur logf
  assert "frozen log polls empty" (null r2)
  TIO.appendFile logf "c"
  r3 <- pollNumberedFile cur logf
  assert "partial trailing line is left unconsumed" (null r3)
  TIO.appendFile logf "\n"
  r4 <- pollNumberedFile cur logf
  assert "completed line is delivered exactly once, with its number" (r4 == [(3, "c")])
  TIO.writeFile logf "x\n"
  r5 <- pollNumberedFile cur logf
  assert "truncation resets to zero" (r5 == [(1, "x")])

  putStrLn "cliQuery against fake CLI (process oracle)"
  tmp <- getTemporaryDirectory
  let dir = tmp </> "circuits-agent-cli-axioma"
      script = dir </> "fake-agent.sh"
      sessionFile = dir </> "session"
  createDirectoryIfMissing True dir
  TIO.writeFile script (T.pack fakeScript)
  wipe sessionFile
  let cli = fakeCli script sessionFile

  unsetEnv "FAIL_RESUME"
  out1 <- cliQuery cli "hello\nworld"
  assert
    "multi-line prompt survives stdin verbatim"
    ("stdin:hello\nworld" `T.isInfixOf` out1)
  assert "session id scraped" ("session_id: fake-42" `T.isInfixOf` out1)
  stored <- TIO.readFile sessionFile
  assert "session id persisted" (T.strip stored == "fake-42")

  out2 <- cliQuery cli "again"
  assert
    "second call resumes with stored id"
    ("argv:--resume fake-42" `T.isInfixOf` out2)

  putStrLn "stale session falls back to fresh"
  writeFile sessionFile "stale-99"
  setEnv "FAIL_RESUME" "1"
  out3 <- cliQuery cli "third"
  unsetEnv "FAIL_RESUME"
  assert
    "stale --resume rejected, fresh retry succeeded"
    ("session_id: fake-42" `T.isInfixOf` out3)
  assert
    "fresh call carried no --resume"
    (not ("--resume" `T.isInfixOf` out3))
  stored3 <- TIO.readFile sessionFile
  assert "new session id persisted" (T.strip stored3 == "fake-42")

  putStrLn "kimiCli recipe against canned kimi binary"
  let fakebin = dir </> "fakebin"
      kimiSf = dir </> "kimi-session"
      grokSf = dir </> "grok-session"
  createDirectoryIfMissing True fakebin
  installFake (fakebin </> "kimi") fakeKimiScript
  installFake (fakebin </> "grok") fakeGrokScript
  oldPath <- getEnv "PATH"
  setEnv "PATH" (fakebin <> ":" <> oldPath)
  wipe kimiSf
  wipe grokSf

  unsetEnv "FAIL_RESUME"
  let kcli = kimiCli Nothing kimiSf
  k1 <- cliQuery kcli "hello kimi"
  assert
    "kimi fresh reply scrubbed of resume hint"
    (k1 == "kimi fresh\nkimi heard: hello kimi")
  kstored <- TIO.readFile kimiSf
  assert "kimi session id persisted" (T.strip kstored == "session_fake-kimi")
  k2 <- cliQuery kcli "again"
  assert
    "kimi resume passes stored id"
    (k2 == "kimi resumed as session_fake-kimi\nkimi heard: again")
  writeFile kimiSf "session_old"
  setEnv "FAIL_RESUME" "1"
  k3 <- cliQuery kcli "third"
  unsetEnv "FAIL_RESUME"
  assert
    "kimi stale session falls back to fresh"
    ("kimi fresh" `T.isInfixOf` k3)
  kstored3 <- TIO.readFile kimiSf
  assert "kimi new session id persisted" (T.strip kstored3 == "session_fake-kimi")

  putStrLn "grokCli recipe against canned grok binary"
  let gcli = grokCli Nothing grokSf
  g1 <- cliQuery gcli "hello grok"
  assert
    "grok text field extracted and unescaped"
    (g1 == "line1\nline2 \"quoted\"")
  gstored <- TIO.readFile grokSf
  assert "grok session id persisted" (T.strip gstored == "grok-fake-uuid")
  g2 <- cliQuery gcli "again"
  assert
    "grok resume passes stored id"
    (g2 == "grok resumed as grok-fake-uuid")
  writeFile grokSf "stale-grok"
  setEnv "FAIL_RESUME" "1"
  g3 <- cliQuery gcli "third"
  unsetEnv "FAIL_RESUME"
  assert
    "grok stale session falls back to fresh"
    ("line1" `T.isInfixOf` g3)
  gstored3 <- TIO.readFile grokSf
  assert "grok new session id persisted" (T.strip gstored3 == "grok-fake-uuid")
  setEnv "PATH" oldPath

  putStrLn "cliShard (live seat shape)"
  csh <- cliShard "fake" cli
  r4 <- runShardIO csh [p1]
  assert
    "cli reply is addressed to the last sender"
    (case r4 of
       [rp] -> from rp == "fake" && to rp == ["tony", "kimi"] && "stdin:hello" `T.isInfixOf` body rp
       _ -> False)

  putStrLn "all cli oracles green"
