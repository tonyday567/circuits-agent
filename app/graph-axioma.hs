{-# LANGUAGE OverloadedStrings #-}

-- | Deterministic graph-law oracles for the algebraic wiring of agent
-- meetings. Each law is checked on a concrete witness; non-deterministic
-- (property) generation belongs in @-machina@, not axioma.
--
-- The witness agents are one-shot (they ignore their own posts). This keeps
-- 'runGraph' terminating on relay graphs — the wiring runs to quiescence, so a
-- self-echoing agent on a feedback edge would otherwise loop forever.
module Main (main) where

import Algebra.Graph.Labelled qualified as LG
import Circuit.Agent (Agent, Post (..), mkPost, tape)
import Circuit.Agent.Graph
  ( AgentGraph,
    AgentRegistry,
    atomic,
    channel,
    flatten,
    nested,
    runGraph,
  )
import Data.List (sortOn)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import System.Exit (exitFailure)

-- | Canonical, order-insensitive run of the graph wiring.
run :: AgentGraph -> AgentRegistry -> [Post Text] -> [Post Text]
run g reg ins = sortOn (\p -> (from p, body p)) (runGraph g reg ins)

-- | One-shot ack agent: replies to the newest post it did not send itself.
ack :: Text -> Agent (->) [Post Text] (Post Text) [Post Text]
ack name = tape $ \hist ->
  case filter (\p -> from p /= name) hist of
    (p : _) -> [p {from = name, to = [], body = "ack:" <> body p}]
    [] -> []

-- | Registry mapping each name to an atomic one-shot ack agent.
ackReg :: [Text] -> AgentRegistry
ackReg names = Map.fromList [(n, atomic (ack n)) | n <- names]

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

main :: IO ()
main = do
  putStrLn "circuits-agent graph-law oracles (deterministic)"

  let va = LG.vertex "a"
      vb = LG.vertex "b"
      vc = LG.vertex "c"
      bus = channel "bus"
      leaf = channel "leaf"
      ins = [mkPost "human" ["bus"] "hi"]
      reg = ackReg ["a", "b", "c"]

  -- Pin the mechanism: connect a -> b on "bus"; posts must actually flow.
  assert "wiring produces output (non-vacuous)" $
    not (null (run (LG.connect bus va vb) (ackReg ["a", "b"]) ins))

  -- overlay commutativity
  let g = LG.connect bus va vb
      h = LG.connect leaf vb vc
  assert "overlay commutativity" $
    run (LG.overlay g h) reg ins == run (LG.overlay h g) reg ins

  -- overlay associativity (DAG: a->b, b->c, a->c)
  let x = LG.connect bus va vb
      y = LG.connect leaf vb vc
      z = LG.connect bus va vc
  assert "overlay associativity" $
    run (LG.overlay (LG.overlay x y) z) reg ins == run (LG.overlay x (LG.overlay y z)) reg ins

  -- overlay idempotence
  assert "overlay idempotence" $
    run (LG.overlay g g) reg ins == run g reg ins

  -- connect identities
  assert "connect left identity" $
    run (LG.connect bus LG.empty g) reg ins == run g reg ins
  assert "connect right identity" $
    run (LG.connect bus g LG.empty) reg ins == run g reg ins

  -- distributivity
  assert "left distributivity" $
    run (LG.connect bus va (LG.overlay vb vc)) reg ins
      == run (LG.overlay (LG.connect bus va vb) (LG.connect bus va vc)) reg ins
  assert "right distributivity" $
    run (LG.connect bus (LG.overlay va vb) vc) reg ins
      == run (LG.overlay (LG.connect bus va vc) (LG.connect bus vb vc)) reg ins

  -- decomposition: the left-hand (x->y)->z creates a relay vertex (y both
  -- subscribes and posts on the same channel), so behavioural comparison under
  -- 'runGraph's quiescence loop diverges. State the law structurally on the
  -- graph algebra itself.
  assert "decomposition (structural)" $
    LG.connect bus (LG.connect bus va vb) vc
      == LG.overlay
        (LG.connect bus va vb)
        (LG.overlay (LG.connect bus va vc) (LG.connect bus vb vc))

  -- orchestrator flatten: a nested vertex expands to the same behaviour
  let innerGraph = LG.vertex "x"
      innerReg = Map.fromList [("x", atomic (ack "x"))]
      parentGraph = LG.connect (channel "outer") (LG.vertex "nested") (LG.vertex "a")
      parentReg =
        Map.fromList
          [ ("nested", nested innerGraph innerReg),
            ("a", atomic (ack "a"))
          ]
      (g', reg') = flatten parentGraph parentReg
      ins9 = [mkPost "human" ["outer"] "hi"]
  assert "orchestrator flatten" $
    run parentGraph parentReg ins9 == run g' reg' ins9

  putStrLn "All graph-law oracles passed"
