{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Circuit.Agent (Post (..))
import Circuit.Agent.Framing
  ( Jsonl (..),
    Stamped (..),
    StoredPost,
    Cons (..),
    Snoc (..),
    These (..),
    Uncons (..),
    frameStored,
    parseLine,
    parseLineAt,
    parseMessage,
    renderStored,
  )
import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty
import Test.Tasty.HUnit

mkStored :: Integer -> Text -> Post Text -> StoredPost
mkStored i ts p = Stamped (fromIntegral i) ts p

main :: IO ()
main = defaultMain $
  testGroup "circuits-agent-framing"
    [ testCase "round-trip unicode and embedded newlines" $ do
        let p = Post "kimi" ["bus"] [3] ("hello \nworld \9835" :: Text)
            stored = mkStored 42 "2026-08-03T23:10:25" p
        parseLine (frameStored stored) @?= Just stored,
      testCase "id is preserved across round-trip" $ do
        let p = Post "a" ["b"] [2] ("body" :: Text)
            stored = mkStored 7 "2026-08-03T23:10:25" p
        case parseLine (frameStored stored) of
          Just s -> stampId s @?= 7
          Nothing -> assertFailure "parseLine failed",
      testCase "legacy triple round-trip" $ do
        let line = "{\"ts\":\"2026-08-03T12:00:00\",\"sender\":\"kimi\",\"body\":\"legacy\"}" :: Text
        case parseLineAt 5 line of
          Just s -> do
            stampId s @?= 5
            from (stamped s) @?= "kimi"
            body (stamped s) @?= "legacy"
            to (stamped s) @?= []
            thread (stamped s) @?= []
          Nothing -> assertFailure "parseLineAt failed for triple",
      testCase "legacy bracket round-trip" $ do
        let line = "[2026-08-03T12:00:00] kimi: legacy bracket" :: Text
        case parseLineAt 3 line of
          Just s -> do
            stampId s @?= 3
            from (stamped s) @?= "kimi"
            body (stamped s) @?= "legacy bracket"
          Nothing -> assertFailure "parseLineAt failed for bracket",
      testCase "parseMessage extracts (from, body) on stamped line" $ do
        let p = Post "kimi" ["bus"] [] ("hi" :: Text)
            stored = mkStored 1 "2026-08-03T23:10:25" p
        parseMessage (frameStored stored) @?= Just ("kimi", "hi"),
      testCase "renderStored includes id and from" $ do
        let p = Post "kimi" ["bus"] [] ("hi" :: Text)
            s = mkStored 9 "2026-08-03T23:10:25" p
            rendered = renderStored s
        assertBool "rendered contains id@ts" ("[9@2026-08-03T23:10:25]" `T.isPrefixOf` rendered)
        assertBool "rendered contains from:body" ("kimi: hi" `T.isSuffixOf` rendered),
      testCase "Snoc then Uncons peels oldest first" $ do
        let a = mkStored 0 "t0" (Post "a" [] [] "A")
            b = mkStored 1 "t1" (Post "b" [] [] "B")
            j = snoc (snoc (Jsonl []) a) b
        case uncons j of
          These a' (Jsonl rest1) -> do
            a' @?= a
            case uncons (Jsonl rest1) of
              This b' -> b' @?= b
              _ -> assertFailure "expected This b"
          _ -> assertFailure "expected These a rest",
      testCase "Recreate from Jsonl via snoc/uncons" $ do
        let posts =
              [ mkStored 0 "t0" (Post "a" ["x"] [1, 2] "multi\nline ♪"),
                mkStored 1 "t1" (Post "b" ["y"] [] "body2"),
                mkStored 2 "t2" (Post "c" [] [] "body3")
              ]
            j = foldl snoc (Jsonl []) posts
            go (Jsonl []) = []
            go js =
              case uncons js of
                This p -> [p]
                These p js' -> p : go js'
                That _ -> []
        go j @?= posts
    ]
