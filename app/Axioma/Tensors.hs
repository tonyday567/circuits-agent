{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | race/await tensors at every level, S/X agents.
module Axioma.Tensors
  ( tensorsTopic,
  )
where

import Algebra.Graph.Labelled qualified as LG
import Axioma.Common
import Circuit.Agent
import Circuit.Agent.Tensor
import Circuit.Category (K (..))
import Circuit.Machine (Body (Body), MooreT (..), Poles (..), Step (..))
import Control.Concurrent (threadDelay)
import Data.Text (Text)

default (Text)

tensorsTopic :: IO ()
tensorsTopic = do
  putStrLn "race await tensors"

  putStrLn "race is orElse with silence as zero"
  do
    let f :: [Post Text] -> [Post Text]
        f = const [mkPost "f" [] "f"]
        g :: [Post Text] -> [Post Text]
        g = const [mkPost "g" [] "g"]
        h :: [Post Text] -> [Post Text]
        h = const [mkPost "h" [] "h"]
    assert "race: silent is left identity" $ raceP silent f [] == f []
    assert "race: silent is right identity" $ raceP f silent [] == f []
    assert "race: associativity of bias" $ raceP (raceP f g) h [] == raceP f (raceP g h) []
    assert "race: left bias (left speaks)" $ raceP f g [] == f []
    assert "race: fallback to right when left silent" $ raceP silent g [] == g []
    assert "race: both silent is silent" $ null (raceP silent silent [])

  putStrLn "await is product with silence as unit"
  do
    let f :: [Post Text] -> [Post Text]
        f = const [mkPost "f" [] "f"]
        g :: [Post Text] -> [Post Text]
        g = const [mkPost "g" [] "g"]
        h :: [Post Text] -> [Post Text]
        h = const [mkPost "h" [] "h"]
    assert "await: silent is left unit" $ awaitP silent f [] == f []
    assert "await: silent is right unit" $ awaitP f silent [] == f []
    assert "await: associativity" $ awaitP (awaitP f g) h [] == awaitP f (awaitP g h) []
    assert "await: order is observable (not a bag)" $ awaitP f g [] /= awaitP g f []

  putStrLn "race takes the whole winning branch emit"
  do
    let f2 :: [Post Text] -> [Post Text]
        f2 = const [mkPost "f" [] "f1", mkPost "f" [] "f2"]
        g1 :: [Post Text] -> [Post Text]
        g1 = const [mkPost "g" [] "g"]
    assert "race: left branch whole emit wins" $ raceP f2 g1 [] == f2 []
    assert "race: not just the first post of concat" $ raceP f2 g1 [] /= take 1 (f2 [] ++ g1 [])

  putStrLn "exchange probe"
  do
    let a :: [Post Text] -> [Post Text]
        a = const [mkPost "a" [] "a"]
        b :: [Post Text] -> [Post Text]
        b = const [mkPost "b" [] "b"]
        c :: [Post Text] -> [Post Text]
        c = const [mkPost "c" [] "c"]
        d :: [Post Text] -> [Post Text]
        d = const [mkPost "d" [] "d"]
        leftHand = outcomesRace (awaitP a c) (awaitP b d) []
        rightHand = [x <> y | x <- outcomesRace a b [], y <- outcomesRace c d []]
        isSubset xs ys = all (`elem` ys) xs
    assert "exchange: correlated outcomes are a subset of independent outcomes" $
      isSubset leftHand rightHand
    assert "exchange: mixed outcome a+d exists only in independent choice" $
      [mkPost "a" [] "a", mkPost "d" [] "d"] `elem` rightHand
        && [mkPost "a" [] "a", mkPost "d" [] "d"] `notElem` leftHand

  putStrLn "seat-level tensors"

  putStrLn "awaitA is product with silent unit"
  do
    let p = mkPost "test" [] "p"
        a = constAgent [p]
        z = constAgent []
        ins = [mkPost "human" [] "one"]
        (outsAZ, _) = runAgentShard (awaitA a z) (AgentSeat ([], []) []) ins
        (outsZA, _) = runAgentShard (awaitA z a) (AgentSeat ([], []) []) ins
        (outsA, _) = runAgentShard a (AgentSeat [] []) ins
    assert "awaitA: silent agent is right unit (outputs)" $ outsAZ == outsA
    assert "awaitA: silent agent is left unit (outputs)" $ outsZA == outsA

  putStrLn "awaitA associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constAgent [p]
        b = constAgent [q]
        c = constAgent [r]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        left = awaitA (awaitA a b) c
        right = awaitA a (awaitA b c)
        (outsL, _) = runAgentShard left (AgentSeat (([], []), []) []) ins
        (outsR, _) = runAgentShard right (AgentSeat ([], ([], [])) []) ins
    assert "awaitA: associativity of outputs" $ outsL == outsR

  putStrLn "raceA is coproduct with silent unit / left bias"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        a = constAgent [p]
        b = constAgent [q]
        z = constAgent []
        ins = [mkPost "human" [] "one"]
        (outsAB, _) = runAgentShard (raceA a b) (AgentSeat ([], []) []) ins
        (outsAZ, _) = runAgentShard (raceA a z) (AgentSeat ([], []) []) ins
        (outsZA, _) = runAgentShard (raceA z a) (AgentSeat ([], []) []) ins
    assert "raceA: left bias (left speaks)" $ outsAB == [p]
    assert "raceA: silent right unit" $ outsAZ == [p]
    assert "raceA: silent left falls back to right" $ outsZA == [p]

  putStrLn "raceA associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constAgent [p]
        b = constAgent [q]
        c = constAgent [r]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        left = raceA (raceA a b) c
        right = raceA a (raceA b c)
        (outsL, _) = runAgentShard left (AgentSeat (([], []), []) []) ins
        (outsR, _) = runAgentShard right (AgentSeat ([], ([], [])) []) ins
    assert "raceA: associativity of outputs" $ outsL == outsR

  putStrLn "seat-level race agrees with policy-level race"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        f = const [p] :: [Post Text] -> [Post Text]
        g = const [q] :: [Post Text] -> [Post Text]
        a = constAgent [p]
        b = constAgent [q]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        (outsA, _) = runAgentShard (raceA a b) (AgentSeat ([], []) []) ins
    assert "raceA outputs match raceP per input" $
      outsA == concat (replicate (length ins) (raceP f g []))

  putStrLn "S-agent tensors"

  putStrLn "awaitS is product with silent unit"
  do
    let p = mkPost "test" [] "p"
        a = constAgentS [p]
        z = constAgentS []
        ins = [mkPost "human" [] "one"]
    (outsAZ, _) <- runAgentS (awaitS a z) ([], []) ins
    (outsZA, _) <- runAgentS (awaitS z a) ([], []) ins
    (outsA, _) <- runAgentS a [] ins
    assert "awaitS: silent agent is right unit (outputs)" $ outsAZ == outsA
    assert "awaitS: silent agent is left unit (outputs)" $ outsZA == outsA

  putStrLn "awaitS associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constAgentS [p]
        b = constAgentS [q]
        c = constAgentS [r]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        left = awaitS (awaitS a b) c
        right = awaitS a (awaitS b c)
    (outsL, _) <- runAgentS left (([], []), []) ins
    (outsR, _) <- runAgentS right ([], ([], [])) ins
    assert "awaitS: associativity of outputs" $ outsL == outsR

  putStrLn "raceS is coproduct with silent unit / left bias"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        a = constAgentS [p]
        b = constAgentS [q]
        z = constAgentS []
        ins = [mkPost "human" [] "one"]
    (outsAB, _) <- runAgentS (raceS a b) ([], []) ins
    (outsAZ, _) <- runAgentS (raceS a z) ([], []) ins
    (outsZA, _) <- runAgentS (raceS z a) ([], []) ins
    assert "raceS: left bias (left speaks)" $ outsAB == [p]
    assert "raceS: silent right unit" $ outsAZ == [p]
    assert "raceS: silent left falls back to right" $ outsZA == [p]

  putStrLn "raceS associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constAgentS [p]
        b = constAgentS [q]
        c = constAgentS [r]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        left = raceS (raceS a b) c
        right = raceS a (raceS b c)
    (outsL, _) <- runAgentS left (([], []), []) ins
    (outsR, _) <- runAgentS right ([], ([], [])) ins
    assert "raceS: associativity of outputs" $ outsL == outsR

  putStrLn "S-agent race agrees with pure seat-level race"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        aPure = constAgent [p]
        bPure = constAgent [q]
        aSTM = constAgentS [p]
        bSTM = constAgentS [q]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        (outsPure, _) = runAgentShard (raceA aPure bPure) (AgentSeat ([], []) []) ins
    (outsSTM, _) <- runAgentS (raceS aSTM bSTM) ([], []) ins
    assert "raceS outputs match raceA outputs" $ outsSTM == outsPure

  putStrLn "X-agent temporal race"

  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        seed = mkPost "human" [] "one"
        fastLeft = Step $ K $ \(_, _) -> pure ((), ([p], ()))
        slowRight = Step $ K $ \(_, _) -> threadDelay 10000 >> pure ((), ([q], ()))
    (outs, _) <- runAgentM (raceIO fastLeft slowRight) ((), ()) seed
    assert "raceIO: fast left wins" $ outs == [p]

  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        seed = mkPost "human" [] "one"
        slowLeft = Step $ K $ \(_, _) -> threadDelay 10000 >> pure ((), ([p], ()))
        fastRight = Step $ K $ \(_, _) -> pure ((), ([q], ()))
    (outs, _) <- runAgentM (raceIO slowLeft fastRight) ((), ()) seed
    assert "raceIO: fast right wins" $ outs == [q]

  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        seed = mkPost "human" [] "one"
        fastLeft = Step $ K $ \(_, _) -> pure ((), ([p], ()))
        fastRight = Step $ K $ \(_, _) -> pure ((), ([q], ()))
    (outs, _) <- runAgentM (raceIO fastLeft fastRight) ((), ()) seed
    assert "raceIO: both emit -> one of them" $ outs == [p] || outs == [q]

  putStrLn "Container dial"

  do
    let a = mkPost "alice" [] "a"
        b = mkPost "bob" [] "b"
        c = mkPost "carol" [] "c"
        outPost x = x {body = "out:" <> body x}
        sh = ioShard (pure . map outPost)
        runBag sh' ins = do
          (outs, _) <- closeShardIO sh' ins []
          pure (toBag outs)
    bag1 <- runBag sh [a, b, c]
    bag2 <- runBag sh [c, a, b]
    assert "permuting input preserves output bag" $ bag1 == bag2
