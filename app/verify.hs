{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Circuit.Agent
import Circuit.Poly (Eval (..), Mono, System)
import Circuit.Poly.Process (iterateSystem)
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Monad.State (State, get, modify, runState)
import Data.Functor.Identity (Identity (..))
import Data.Text (Text)
import Data.Text qualified as T
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

mkPost :: Text -> Text -> Text -> Text -> Post
mkPost = Post

peek :: [Post] -> Post
peek [] = error "verify: empty history"
peek (p : _) = p

reply :: Text -> [Post] -> Post
reply name hist =
  mkPost name (author (peek hist)) (channel (peek hist)) ("ack: " <> body (peek hist))

main :: IO ()
main = do
  putStrLn "circuits-agent oracle tests"

  -------------------------------------------------------------------------
  -- The pretense: carrier is invisible at the interface.
  -------------------------------------------------------------------------
  putStrLn "the pretense"
  do
    let sumAgent :: System Int (Mono Int Int)
        sumAgent s = EP (EK s, EE (+ s))
    assert "tape sum == [1,3,6]" $
      iterateSystem (tape sum) [] [1, 2, 3 :: Int] == [1, 3, 6]
    assert "sumAgent == [1,3,6]" $
      iterateSystem sumAgent 0 [1, 2, 3 :: Int] == [1, 3, 6]

  -------------------------------------------------------------------------
  -- Delivery: addressed posts, no redelivery.
  -------------------------------------------------------------------------
  putStrLn "delivery"
  do
    let t0 =
          [ mkPost "human" "k" "beta" "hi k",
            mkPost "human" "j" "alpha" "hi j"
          ]
    let (sj1, t1) = turn "j" (tape (reply "j")) ([], t0)
    let (sk1, t2) = turn "k" (tape (reply "k")) ([], t1)
    assert "j receives only its addressed posts" $
      map body (reverse sj1) == ["hi j"]
    assert "k receives only its addressed posts" $
      map body (reverse sk1) == ["hi k"]

    let t3 = post (mkPost "human" "j" "alpha" "again") t2
    let (sj2, _t4) = turn "j" (tape (reply "j")) (sj1, t3)
    assert "j sees the new post, no redelivery" $
      map body (reverse sj2) == ["hi j", "again"]

  -------------------------------------------------------------------------
  -- Compaction invariance: summary-insensitive folds survive it.
  -------------------------------------------------------------------------
  putStrLn "compaction invariance"
  do
    let a = tape sum :: System [Int] (Mono Int Int)
    let (_, s1) = run1 a [] 1
    let (_, s2) = run1 a s1 2
    let (o3, _) = run1 a [sum s2] 3
    assert "sum survives wholesale compaction" $ o3 == 6

    let b = tape length :: System [Int] (Mono Int Int)
    let (_, t1) = run1 b [] 1
    let (_, t2) = run1 b t1 2
    let (p3, _) = run1 b [sum t2] 3
    assert "length notices wholesale compaction" $ p3 == 2

  -------------------------------------------------------------------------
  -- Turn integrity: one turn appends exactly the fold's output.
  -------------------------------------------------------------------------
  putStrLn "turn integrity"
  do
    let t0 = [mkPost "human" "j" "alpha" "calc:1 2 3"]
    let (sj1, t1) = turn "j" (tape llmJ) ([], t0)
    let (_sc1, t2) = turn "calc" (tape calc) ([], t1)
    let (_sj2, t3) = turn "j" (tape llmJ) (sj1, t2)
    assert "tool-call chain produces expected final post" $
      body (peek t3) == "final: 6"
    assert "turn appends exactly one post per input" $
      length t3 == 4

  -------------------------------------------------------------------------
  -- Loop v0: round-robin to quiescence (replaces hand-scheduling).
  -------------------------------------------------------------------------
  putStrLn "loop quiescence"
  do
    let roster =
          [ ("j", tape (reply "j")),
            ("k", tape (reply "k"))
          ]
    let t0 =
          [ mkPost "human" "k" "beta" "hi k",
            mkPost "human" "j" "alpha" "hi j"
          ]
    let (seens, t1) = loop roster t0
    assert "loop delivers both agents" $
      map body (reverse (maybe [] id (lookup "j" seens))) == ["hi j"]
        && map body (reverse (maybe [] id (lookup "k" seens))) == ["hi k"]
    assert "loop posts both acks" $
      length t1 == 4
    assert "loop reaches quiescence (no pending)" $
      all (\(n, s) -> not (hasPending n s t1)) seens

    let roster2 = [("j", tape llmJ), ("calc", tape calc)]
    let tCalc0 = [mkPost "human" "j" "alpha" "calc:1 2 3"]
    let (_seens2, tCalc) = loop roster2 tCalc0
    assert "loop runs tool-call chain to final" $
      body (peek tCalc) == "final: 6"
    assert "loop tool chain length" $
      length tCalc == 4

    let (_emptySeens, tEmpty) = loop roster []
    assert "loop on empty log is identity" $ null tEmpty

  -------------------------------------------------------------------------
  -- Shard combinators: composition and codec adapters on Ends.
  -------------------------------------------------------------------------
  putStrLn "shard combinators"
  do
    let p1 = mkPost "human" "j" "alpha" "hi"
        p2 = mkPost "j" "human" "alpha" "ack"
        fixedShard :: Shard Identity
        fixedShard = endsK (\_ -> pure ()) (pure [p2])
        coded = codecShard (map (\p -> p {body = "in:" <> body p})) (map (\p -> p {body = body p <> ":out"})) fixedShard
        out = runIdentity (runKleisli (close (conjoint coded) (companion coded)) [p1])
    assert "codec transforms commit and emit" $
      map body out == ["ack:out"]

    let accumShard :: Shard (State [Post])
        accumShard = endsK (\ps -> modify (ps ++)) get
        composed = composeShard accumShard (suffixShard (map (\p -> p {body = body p <> "!"})) accumShard)
        (out2, st) = runState (runKleisli (close (conjoint composed) (companion composed)) [p1]) []
    assert "compose chains shards through the monad" $
      map body out2 == ["hi!", "hi!"] && length st == 2

  putStrLn "All tests passed"
  where
    llmJ :: [Post] -> Post
    llmJ hist =
      let p = peek hist
       in if "calc:" `T.isPrefixOf` body p
            then mkPost "j" "calc" (channel p) (T.drop 5 (body p))
            else
              mkPost
                "j"
                (author (peek (dropWhile ((== "calc") . author) hist)))
                (channel p)
                ("final: " <> body p)

    calc :: [Post] -> Post
    calc hist =
      let p = peek hist
       in mkPost
            "calc"
            (author p)
            (channel p)
            (T.pack (show (sum [read (T.unpack w) :: Int | w <- T.words (body p)])))
