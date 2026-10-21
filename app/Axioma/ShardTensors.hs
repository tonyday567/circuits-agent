{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | shard-level tensor laws.
module Axioma.ShardTensors
  ( shardTensorsTopic,
  )
where

import Algebra.Graph.Labelled qualified as LG
import Axioma.Common
import Circuit.Agent
import Circuit.Agent.Tensor
import Data.Text (Text)
import Data.Text qualified as T

default (Text)

shardTensorsTopic :: IO ()
shardTensorsTopic = do
  putStrLn "shard-level tensors"

  putStrLn "silent shard"
  do
    let posts = [mkPost "human" ["bot"] "x"]
    (outs, st) <- closeShardIO silentShard posts []
    assert "silent shard emits empty" $ null outs
    assert "silent shard clears buffer" $ null st

  putStrLn "awaitShard is product with silent unit"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        a = constShard [p]
        b = constShard [q]
        z = silentShard
        posts = [mkPost "human" [] "one"]
    (outsAZ, _) <- closeShardIO (awaitShard z a) posts []
    (outsZA, _) <- closeShardIO (awaitShard a z) posts []
    (outsA, _) <- closeShardIO a posts []
    (outsAB, _) <- closeShardIO (awaitShard a b) posts []
    assert "awaitShard: silent is right unit" $ outsAZ == outsA
    assert "awaitShard: silent is left unit" $ outsZA == outsA
    assert "awaitShard: both branches speak" $ outsAB == [p, q]

  putStrLn "awaitShard associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constShard [p]
        b = constShard [q]
        c = constShard [r]
        posts = [mkPost "human" [] "one"]
        left = awaitShard (awaitShard a b) c
        right = awaitShard a (awaitShard b c)
    (outsL, _) <- closeShardIO left posts []
    (outsR, _) <- closeShardIO right posts []
    assert "awaitShard associative" $ outsL == outsR

  putStrLn "raceShard is coproduct with silent unit / left bias"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        a = constShard [p]
        b = constShard [q]
        z = silentShard
        posts = [mkPost "human" [] "one"]
    (outsAB, _) <- closeShardIO (raceShard a b) posts []
    (outsAZ, _) <- closeShardIO (raceShard a z) posts []
    (outsZA, _) <- closeShardIO (raceShard z a) posts []
    assert "raceShard: left bias" $ outsAB == [p]
    assert "raceShard: silent right unit" $ outsAZ == [p]
    assert "raceShard: silent left falls back" $ outsZA == [p]

  putStrLn "raceShard associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constShard [p]
        b = constShard [q]
        c = constShard [r]
        posts = [mkPost "human" [] "one"]
        left = raceShard (raceShard a b) c
        right = raceShard a (raceShard b c)
    (outsL, _) <- closeShardIO left posts []
    (outsR, _) <- closeShardIO right posts []
    assert "raceShard associative" $ outsL == outsR

  putStrLn "raceShard agrees with seat-level raceA"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        posts = [mkPost "human" [] "one"]
        (outsAgent, _) =
          runAgentShard
            (raceA (cellToAgent (tape (const [p]))) (cellToAgent (tape (const [q]))))
            (AgentSeat ([], []) [])
            posts
    (outsShard, _) <- closeShardIO (raceShard (constShard [p]) (constShard [q])) posts []
    assert "raceShard outputs match raceA outputs" $ outsShard == outsAgent

  putStrLn "fanOutShard runs branches on copies"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        posts = [mkPost "human" [] "one"]
    (outs, _) <- closeShardIO (fanOutShard [constShard [p], constShard [q]]) posts []
    assert "fanOutShard: both branches see input" $ outs == [p, q]

  putStrLn "fanInShard summarizes branch outputs"
  do
    let posts = [mkPost "human" [] "one"]
        summary pss = [mkPost "sum" [] (T.intercalate "+" (map body (concat pss)))]
    (outs, _) <- closeShardIO (fanInShard summary [tagShard "-a", tagShard "-b"]) posts []
    assert "fanInShard: summary is one post" $ length outs == 1
    assert "fanInShard: summary body collects branches" $
      case outs of
        [o] -> body o == "one-a+one-b"
        _ -> False

  putStrLn "fanInShard with synthesisSummary is honest by construction"
  do
    let posts = [mkPost "human" [] "one"]
        branchA = constShard [mkPost "a" [] "x"]
        branchB = constShard [mkPost "b" [] "y"]
        summary = synthesisSummary "sum" ["human"] [0, 1] (T.intercalate "+" . map body . concat)
    (outs, _) <- closeShardIO (fanInShard summary [branchA, branchB]) posts []
    assert "honest fan-in: one synthesis post" $ length outs == 1
    assert "honest fan-in: ancestry cites every branch output by id" $
      case outs of
        [o] -> thread o == [0, 1] && body o == "x+y"
        _ -> False
    assert "honest fan-in: empty body is quiet" $
      null (synthesisSummary "sum" [] [0] (const "") [[mkPost "a" [] "x"]])
