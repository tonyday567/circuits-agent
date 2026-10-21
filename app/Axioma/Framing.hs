{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | framing, query adapters, ancestry oracles, cursors.
module Axioma.Framing
  ( framingTopic,
  )
where

import Axioma.Common
import Circuit.Agent
import Circuit.Agent.Framing
import Circuit.Agent.Framing qualified as Framing
import Circuit.Agent.Query
import Cursor (newMem, pollNumberedFile)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (getTemporaryDirectory)
import System.FilePath ((</>))

default (Text)

framingTopic :: IO ()
framingTopic = do
  putStrLn "Tier F: framing laws"
  do
    let p = Post "kimi" ["bus"] [3] ("hello \nworld ♪" :: Text)
        stored = case parseTimeText "2026-08-03T23:10:25" of
          Just ts -> Stamped (ts, 42) p
          Nothing -> error "bad timestamp"
    assert "F0: round-trip unicode and embedded newlines" $
      unframeStored @Text (frameStored stored) == Just stored

  do
    let p = Post "a" ["b"] [2] ("body" :: Text)
        stored = case parseTimeText "2026-08-03T23:10:25" of
          Just ts -> Stamped (ts, 7) p
          Nothing -> error "bad timestamp"
    assert "F1: id is preserved across round-trip" $
      maybe False ((== 7) . snd . stamp) (unframeStored @Text (frameStored stored))

  do
    let line = "{\"ts\":\"2026-08-03T12:00:00\",\"sender\":\"kimi\",\"body\":\"legacy\"}" :: Text
    assert "F2: legacy triple round-trip" $
      case parseLineAt 5 line of
        Just s ->
          snd (stamp s) == 5
            && from (stamped s) == "kimi"
            && body (stamped s) == "legacy"
            && to (stamped s) == []
            && thread (stamped s) == []
        Nothing -> False

  do
    let line = "[2026-08-03T12:00:00] kimi: legacy bracket" :: Text
    assert "F3: legacy bracket round-trip" $
      case parseLineAt 3 line of
        Just s ->
          snd (stamp s) == 3
            && from (stamped s) == "kimi"
            && body (stamped s) == "legacy bracket"
        Nothing -> False

  do
    let p = Post "kimi" ["bus"] [] ("hi" :: Text)
        stored = case parseTimeText "2026-08-03T23:10:25" of
          Just ts -> Stamped (ts, 1) p
          Nothing -> error "bad timestamp"
    assert "F4: parseMessage extracts (from, body) on stamped line" $
      parseMessage (frameStored stored) == Just ("kimi", "hi")

  do
    let p = Post "kimi" ["bus"] [] ("hi" :: Text)
        s = case parseTimeText "2026-08-03T23:10:25" of
          Just ts -> Stamped (ts, 9) p
          Nothing -> error "bad timestamp"
        rendered = renderStored s
    assert "F5: renderStored includes id@ts" $
      "[9@2026-08-03T23:10:25]" `T.isPrefixOf` rendered
    assert "F6: renderStored contains from:body" $
      "kimi: \"hi\"" `T.isSuffixOf` rendered

  do
    let dummyTS = case parseTimeText "2026-01-01T00:00:00" of
          Just ts -> ts
          Nothing -> error "bad timestamp"
        a = Stamped (dummyTS, 0) (Post "a" [] [] "A")
        b = Stamped (dummyTS, 1) (Post "b" [] [] "B")
        j :: Framing.Log Text
        j = snoc (snoc (Log []) a) b
    assert "F7: Snoc then Uncons peels oldest first" $
      case uncons j of
        These a' (Log rest1) ->
          a' == a
            && case uncons (Log rest1 :: Framing.Log Text) of
              This b' -> b' == b
              _ -> False
        _ -> False

  do
    let dummyTS = case parseTimeText "2026-01-01T00:00:00" of
          Just ts -> ts
          Nothing -> error "bad timestamp"
        posts =
          [ Stamped (dummyTS, 0) (Post "a" ["x"] [1, 2] "multi\nline ♪"),
            Stamped (dummyTS, 1) (Post "b" ["y"] [] "body2"),
            Stamped (dummyTS, 2) (Post "c" [] [] "body3")
          ] ::
            [Stamped Text]
        j :: Framing.Log Text
        j = foldl snoc (Log []) posts
        go :: Framing.Log Text -> [Stamped Text]
        go (Log []) = []
        go js =
          case uncons js of
            This p -> [p]
            These p js' -> p : go js'
            That _ -> []
    assert "F8: Recreate from Log via snoc/uncons" $
      go j == posts

  -------------------------------------------------------------------------
  -- Query-to-post adapters (from old cli-axioma)
  -------------------------------------------------------------------------
  do
    let p1 :: Post Text
        p1 = mkPost "tony" ["kimi"] "hello"
        p2 :: Post Text
        p2 = mkPost "grok" ["kimi", "tony"] "line1\nline2"

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
      ( map body r1 == [sessionPrompt [p1, p2]]
          && all ((== "kimi") . from) r1
          && all ((== ["grok", "tony"]) . to) r1
      )
    r2 <- runShardIO sh [p1]
    assert
      "outbox drains between closes"
      ( map body r2 == ["hello"]
          && all ((== "kimi") . from) r2
          && all ((== ["tony"]) . to) r2
      )
    r3 <- runShardIO sh []
    assert "empty commit emits nothing" (null r3)

    putStrLn "shard boundary: id-blind by protocol (M1b)"
    -- The Shard protocol carries bare Posts; stamped ids live in the log
    -- it is mounted on. A bare shard reply therefore carries no thread
    -- edge — the ancestry law is enforced by the runners that hold the
    -- stamp (runSeatBus, runAgentLoop), one layer up.
    shB <- echoShard "kimi"
    rb <- runShardIO shB [p1]
    assert
      "a bare shard reply carries no thread edge (ids live in the stamped log)"
      (map thread rb == [[]])

    putStrLn "thread (ancestry) oracles"
    assert "root post has no parents" (thread p1 == [])
    assert
      "reply threads onto the parent id"
      (thread (replyTo "kimi" 1 p2 "x" :: Post Text) == [1])
    assert
      "replyPosts threads onto the last input's id"
      ( case replyPosts "kimi" [p1, p2] [0, 1] "sure" of
          [rp] -> thread rp == [1]
          _ -> False
      )
    let r1' :: Post Text
        r1' = replyTo "kimi" 1 p2 "a"
        r2' :: Post Text
        r2' = replyTo "tony" 2 r1' "b"
    assert
      "branches of a root are its sender"
      (branchesByIndex [p1, p2] p2 == [["grok"]])
    assert
      "branches of a reply are pure cons"
      (branchesByIndex [p1, p2] r1' == map ("kimi" :) (branchesByIndex [p1, p2] p2))
    assert
      "branches unfolds a three-post thread"
      (branchesByIndex [p1, p2, r1'] r2' == [["tony", "kimi", "grok"]])
    let r0 :: Post Text
        r0 = replyTo "kimi" 0 p1 "old"
    assert
      "same-named posts are disambiguated by exact id"
      (branchesByIndex [p1, p2, r1', r0] r2' == [["tony", "kimi", "grok"]])

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
      (branchesByIndex [p1, p2] syn == [["sum", "tony"], ["sum", "grok"]])
    assert
      "branches of a synthesis continues through each parent"
      ( branchesByIndex [p1, p2, r1'] (synthesis "sum" [] [2, 0] "Σ" :: Post Text)
          == [["sum", "tony"], ["sum", "kimi", "grok"]]
      )

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
      ( coneByIndex prior (synthesis "sum" [] [2, 0] "Σ")
          == sortNub ("sum" : concatMap (coneByIndex prior) [r1', p2])
      )
    assert
      "cone of a synthesis is the contributor set"
      (coneByIndex prior (synthesis "sum" [] [2, 0] "Σ") == ["grok", "kimi", "sum", "tony"])

    putStrLn "cursor numbered poll oracles"
    tmpC <- getTemporaryDirectory
    let logf = tmpC </> "circuits-agent-cursor-axioma.log"
    wipe logf
    TIO.writeFile logf "a\nb\n"
    cur <- newMem 0
    r4 <- pollNumberedFile cur logf
    assert "complete lines are numbered 1-based" (r4 == [(1, "a"), (2, "b")])
    r5 <- pollNumberedFile cur logf
    assert "frozen log polls empty" (null r5)
    TIO.appendFile logf "c"
    r6 <- pollNumberedFile cur logf
    assert "partial trailing line is left unconsumed" (null r6)
    TIO.appendFile logf "\n"
    r7 <- pollNumberedFile cur logf
    assert "completed line is delivered exactly once, with its number" (r7 == [(3, "c")])
    TIO.writeFile logf "x\n"
    r8 <- pollNumberedFile cur logf
    assert "truncation resets to zero" (r8 == [(1, "x")])
