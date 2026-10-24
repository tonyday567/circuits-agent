{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | turn and meeting laws: turn integrity, loop quiescence, multi-seat cards.
module Axioma.Turns
  ( turnsTopic,
  )
where

import Axioma.Common
import Circuit.Agent
import Circuit.Syntax (eval)
import Data.List (find, sort)
import Data.Text (Text)

default (Text)

turnsTopic :: IO ()
turnsTopic = do
  putStrLn "turn integrity"
  do
    let t0 = [mkPost "human" ["j"] "calc:1 2 3"]
    let (stJ1, t1, _) = turn (cellToAgent (tape llmJ)) (seedState ["j"] t0) t0
    let (_stCalc, t2, _) = turn (cellToAgent (tape calc)) (seedState ["calc"] t1) t1
    let (_stJ2, t3, _) = turn (cellToAgent (tape llmJ)) (feedState (newFor ["j"] t2 stJ1) stJ1) t2
    assert "tool-call chain produces expected final post" $
      body (peek t3) == "final: 6"
    assert "turn appends exactly one post per input" $
      length t3 == 4

  putStrLn "loop quiescence"
  do
    let roster =
          [ ("j", cellToAgent (tape (reply "j"))),
            ("k", cellToAgent (tape (reply "k")))
          ]
    let t0 =
          [ mkPost "human" ["k"] "hi k",
            mkPost "human" ["j"] "hi j"
          ]
    let (states, t1, derivs) = loop roster t0
    assert "loop delivers both agents" $
      map body (reverse (maybe [] asCarrier (lookup "j" states))) == ["hi j"]
        && map body (reverse (maybe [] asCarrier (lookup "k" states))) == ["hi k"]
    assert "loop posts both acks" $
      length t1 == 4
    assert "loop reaches quiescence (no pending)" $
      all (\(_n, st) -> not (hasPending @Text st)) states
    assert "loop records a derivation per processed post" $
      length derivs == 2
    assert "derivation agent names match roster" $
      sort (map dAgent derivs) == ["j", "k"]

    let pToJ = mkPost "human" ["j"] "hi j"
        expectedAckJ = mkPost "j" ["human"] "ack: hi j"
        jDeriv = find (\d -> dAgent d == "j") derivs
    assert "reply derivation records input, outputs, and agent" $
      case jDeriv of
        Just d -> dInput d == pToJ && dOutputs d == [expectedAckJ] && null (dChildren d)
        Nothing -> False

    let roster2 = [("j", cellToAgent (tape llmJ)), ("calc", cellToAgent (tape calc))]
    let tCalc0 = [mkPost "human" ["j"] "calc:1 2 3"]
    let (_states2, tCalc, derivs2) = loop roster2 tCalc0
    assert "loop runs tool-call chain to final" $
      body (peek tCalc) == "final: 6"
    assert "loop tool chain length" $
      length tCalc == 4
    assert "tool-call chain records three derivations" $
      length derivs2 == 3

    let (_emptyStates, tEmpty, emptyDerivs) = loop roster ([] :: [Post Text])
    assert "loop on empty log is identity" $ null tEmpty
    assert "loop on empty log records no derivations" $ null emptyDerivs

    -- S0a: the meeting is a 'FreeTrace Either (->)' value; 'trace' agrees with 'loopWith'.
    let states0 = [(n, feedState (watch @Text [n] t0) (emptyAgentState @Text [n])) | (n, _) <- roster]
        bundle0 = (states0, t0, [])
    assert "meetingLoop run agrees with loopWith" $
      eval (meetingLoop roster) bundle0 == loopWith roster states0 t0

  putStrLn "multi-seat card"
  do
    let cardRoster =
          [ ("alpha", ["xyzzy"], cellToAgent (tape (reply "alpha"))),
            ("beta", ["xyzzy"], cellToAgent (tape (reply "beta")))
          ]
        seed = [mkPost "human" ["xyzzy"] "hello card"]
        (cardStates, cardLog, cardDerivs) = loopSubs cardRoster seed
    let replies = filter (\p -> from p /= "human") cardLog
    assert "both subscribers processed the card post" $
      map body (reverse (maybe [] asCarrier (lookup "alpha" cardStates))) == ["hello card"]
        && map body (reverse (maybe [] asCarrier (lookup "beta" cardStates))) == ["hello card"]
    assert "log has seed plus one reply per subscriber" $
      length cardLog == 3 && length replies == 2
    assert "replies are from alpha and beta" $
      sort (map from replies) == ["alpha", "beta"]
    assert "replies are addressed to the original sender" $
      all ((== ["human"]) . to) replies
    assert "derivations name the subscriber agents, not the card" $
      sort (map dAgent cardDerivs) == ["alpha", "beta"]

  putStrLn "O8: schedule independence"
  do
    let rosterInd =
          [ ("j", cellToAgent (tape (reply "j"))),
            ("k", cellToAgent (tape (reply "k")))
          ]
        t0Ind =
          [ mkPost "human" ["k"] "hi k",
            mkPost "human" ["j"] "hi j"
          ]
        (_, loopInd, derivsInd) = loop rosterInd t0Ind
        parallelInd = runParallel rosterInd t0Ind
    assert "O8: independent addresses agree between loop and parallel" $
      loopInd == parallelInd
    assert "O8: independent loop records two derivations" $
      length derivsInd == 2

    let forwardTo target hist =
          [mkPost "j" [target] ("fwd: " <> body (peek hist))]
        ackToHuman hist =
          [mkPost "k" ["human"] ("ack: " <> body (peek hist))]
        rosterDep =
          [ ("j", cellToAgent (tape (forwardTo "k"))),
            ("k", cellToAgent (tape ackToHuman))
          ]
        t0Dep = [mkPost "human" ["j"] "tell k"]
        (_, loopDep, derivsDep) = loop rosterDep t0Dep
        parallelDep = runParallel rosterDep t0Dep
    assert "O8: dependent-address counterexample recorded (loop /= parallel)" $
      loopDep /= parallelDep
    assert "O8: dependent loop records two derivations" $
      length derivsDep == 2

  putStrLn "multi-round pure (two Moore agents)"
  do
    let rounds = 3 :: Int
        nudge :: Agent (->) [Post Text] (Post Text) [Post Text]
        nudge =
          cellToAgent
            ( tape
                ( const
                    [mkPost "nudge" ["worker"] "tell me more."]
                )
            )
        worker :: Agent (->) [Post Text] (Post Text) [Post Text]
        worker =
          cellToAgent
            ( tape
                ( \hist ->
                    let p = peek hist
                     in [mkPost "worker" ["nudge"] ("ack:" <> body p)]
                )
            )
        -- seed: human addresses worker
        t0 = [mkPost "human" ["worker"] "start"]
        roundStep (sw, sn, lg) =
          let (sw', lg1, _) = turn worker sw lg
              sn' = feedState (diffLog lg lg1) sn
              (sn'', lg2, _) = turn nudge sn' lg1
              sw'' = feedState (diffLog lg1 lg2) sw'
           in (sw'', sn'', lg2)
        (_, _, tF) = iterate roundStep (seedState ["worker"] t0, seedState ["nudge"] t0, t0) !! rounds
        -- newest first: take dialogue posts (exclude seed)
        dialogue = take (2 * rounds) tF
    assert "multi-round: log grew by 2 posts per round" $
      length tF == 1 + 2 * rounds
    assert "multi-round: worker and nudge both posted" $
      any ((== "worker") . from) dialogue
        && any ((== "nudge") . from) dialogue
    assert "multi-round: nudge bodies constant" $
      all (\p -> from p /= "nudge" || body p == "tell me more.") tF
