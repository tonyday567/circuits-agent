{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | tape/behaviour laws: A0/A1, O1/O2/S3, compaction, run1 monologue (M3).
module Axioma.Tape
  ( tapeTopic,
  )
where

import Algebra.Graph.Labelled qualified as LG
import Axioma.Common
import Circuit.Agent
import Circuit.Agent.StdPorts
import Circuit.Machine (Body (Body), Moore, MooreT (..), Poles (..), Step (..))
import Circuit.Poly (Eval (..), evalAsCell)
import Circuit.Tensor (Const (..))
import Data.Text (Text)

default (Text)

tapeTopic :: IO ()
tapeTopic = do
  putStrLn "Tier A: structural laws"

  putStrLn "A0: identity agent"
  do
    let idAgent :: Moore (,) [Int] (->) Int Int
        idAgent = tape head
    assert "A0: tape head streams inputs through unchanged" $
      iterateAgent idAgent [] [1, 2, 3 :: Int] == [1, 2, 3]

  putStrLn "A1: sequential stream composition"
  do
    let f :: Int -> Int
        f = (+ 10)
        g :: Int -> Int
        g = (* 2)
        fAgent :: Moore (,) [Int] (->) Int Int
        fAgent = tape (f . head)
        gAgent :: Moore (,) [Int] (->) Int Int
        gAgent = tape (g . head)
        inputs = [1, 2, 3 :: Int]
        chained = iterateAgent gAgent [] (iterateAgent fAgent [] inputs)
        direct = iterateAgent (tape (g . f . head)) [] inputs
    assert "A1: chaining outputs equals feeding the composed function" $
      chained == direct

  putStrLn "the pretense"
  do
    let sumAgent :: Moore (,) Int (->) Int Int
        (k, o) = evalAsCell (\s -> EP (EK s, EE (+ s)))
        sumAgent = Body (\i -> k (0, i)) k (Const . o)
    assert "tape sum == [1,3,6]" $
      iterateAgent (tape sum) [] [1, 2, 3 :: Int] == [1, 3, 6]
    assert "sumAgent == [1,3,6]" $
      iterateAgent sumAgent 0 [1, 2, 3 :: Int] == [1, 3, 6]

    -- O1: tape is the anamorphism that applies f to each input prefix.
    -- iterateAgent emits f applied to the state after each input, i.e. the
    -- non-empty prefixes of the input stream (newest-first), so we drop the
    -- initial empty prefix from scanl.
    let xs = [1, 2, 3 :: Int]
    assert "O1: tape f xs == map f (drop 1 (scanl (flip (:)) [] xs))" $
      iterateAgent (tape sum) [] xs == map sum (drop 1 (scanl (flip (:)) [] xs))

  putStrLn "run1 monologue law (M3)"
  do
    let (o1, s1) = run1 (selfrec sum) ([] :: [Int]) (1 :: Int)
    assert "M3 run1 steps once: emitted equals the recorded head" $
      o1 == head s1
    assert "M3 the trace shape is (1, [1, 1]), not the double-step (2, [1, 1])" $
      (o1, s1) == (1, [1, 1 :: Int])
    -- The second turn reads the monologue back: the recorded utterance
    -- drives the next response, newest first.
    let (o2, s2) = run1 (selfrec sum) s1 (2 :: Int)
    assert "M3 the next turn's monologue includes what was emitted" $
      o2 == head s2 && drop 1 s2 == (2 :: Int) : s1

  putStrLn "O2: coalgebra homomorphism"
  do
    let xs = [1, 2, 3 :: Int]
        f hist = [head hist]
        h = take 1
        sys1 :: Moore (,) [Int] (->) Int [Int]
        sys1 = tape f
        sys2 :: Moore (,) [Int] (->) Int [Int]
        sys2 = tape (f . h)
    assert "O2: summarizer h preserves behaviour" $
      iterateAgent sys2 (h []) xs == iterateAgent sys1 [] xs

  putStrLn "S3: behaviour functoriality"
  do
    let xs = [1, 2 :: Int]
        ys = [3 :: Int]
        agent :: Moore (,) [Int] (->) Int [Int]
        agent = tape (\hist -> [head hist])
        s0 = [] :: [Int]
    assert "S3: beh s0 (xs ++ ys) == beh s0 xs ++ beh (finalAgent agent s0 xs) ys" $
      behA agent s0 (xs ++ ys)
        == behA agent s0 xs ++ behA agent (finalAgent (tape (\hist -> [head hist])) s0 xs) ys

  putStrLn "compaction invariance"
  do
    let a = tape sum :: Moore (,) [Int] (->) Int Int
    let (_, s1) = runCell a [] 1
    let (_, s2) = runCell a s1 2
    let (o3, _) = runCell a [sum s2] 3
    assert "sum survives wholesale compaction" $ o3 == 6

    let b = tape length :: Moore (,) [Int] (->) Int Int
    let (_, t1) = runCell b [] 1
    let (_, t2) = runCell b t1 2
    let (p3, _) = runCell b [sum t2] 3
    assert "length notices wholesale compaction" $ p3 == 2
