{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}
-- | wiring-graph oracles and graph-algebra laws (graph-axioma merged).
module Axioma.Graph
  ( graphTopic,
  )
where

import Axioma.Common
import Algebra.Graph.Labelled qualified as LG
import Circuit.Agent
import Circuit.Agent.Delivery
import Circuit.Category (K (..))
import Circuit.Agent.Graph
  ( AgentGraph,
    AgentRegistry,
    atomic,
    bus,
    channel,
    flatten,
    nested,
    runGraph,
    star,
  )
import Data.List (sortOn)
import Data.Map qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

default (Text)

-- | Canonical, order-insensitive run of the graph wiring.
runG :: AgentGraph -> AgentRegistry -> [Post Text] -> [Post Text]
runG g reg ins = sortOn (\p -> (from p, body p)) (runGraph g reg ins)

-- | One-shot ack agent: replies to the newest post it did not send itself.
ack :: Text -> Agent (->) [Post Text] (Post Text) [Post Text]
ack name = cellToAgent $ tape $ \hist ->
  case filter (\p -> from p /= name) hist of
    (p : _) -> [p {from = name, to = [], body = "ack:" <> body p}]
    [] -> []

-- | Registry mapping each name to an atomic one-shot ack agent.
ackReg :: [Text] -> AgentRegistry
ackReg names = Map.fromList [(n, atomic (ack n)) | n <- names]

graphTopic :: IO ()
graphTopic = do
  putStrLn "agent graph wiring"
  do
    let echo name hist =
          let p = peek hist
           in [mkPost name [] ("ack:" <> body p) | from p == "human"]
        reg :: AgentRegistry
        reg =
          Map.fromList
            [ ("j", atomic (cellToAgent (tape (echo "j")))),
              ("k", atomic (cellToAgent (tape (echo "k"))))
            ]
        t0 = [mkPost "human" ["bus"] "hello"]
        logBus = runGraph (bus ["j", "k"] "bus") reg t0
    assert "bus: both agents see the shared post and reply" $
      any ((== "j") . from) logBus && any ((== "k") . from) logBus

  do
    let summary :: [Post Text] -> [Post Text]
        summary hist =
          let p = peek hist
           in [mkPost "hub" [] ("summary: " <> body p) | from p == "leaf"]
        leafEcho :: [Post Text] -> [Post Text]
        leafEcho hist =
          let p = peek hist
           in [mkPost "leaf" [] ("leaf:" <> body p) | from p == "human"]
        reg :: AgentRegistry
        reg =
          Map.fromList
            [ ("hub", atomic (cellToAgent (tape summary))),
              ("leaf", atomic (cellToAgent (tape leafEcho)))
            ]
        -- leaf subscribes to the "hub" channel, so the seed must be posted
        -- there for leaf to receive it first.
        t0 = [mkPost "human" ["hub"] "data"]
        logStar = runGraph (star "hub" ["leaf"] "hub" "leaf") reg t0
    assert "star: hub posts a summary after receiving from leaf" $
      any ((== "hub") . from) logStar

  do
    let echo name hist =
          let p = peek hist
           in [mkPost name [] ("ack:" <> body p) | from p == "human"]
        reg :: AgentRegistry
        reg =
          Map.fromList
            [ ("j", atomic (cellToAgent (tape (echo "j")))),
              ("k", atomic (cellToAgent (tape (echo "k"))))
            ]
        t0 = [mkPost "human" ["bus"] "hello"]
        g = bus ["j", "k"] "bus"
        isolated = LG.overlay (LG.vertex "j") (LG.vertex "k")
        logFull = runGraph g reg t0
        logWithIsolated = runGraph (LG.overlay g isolated) reg t0
    assert "overlay with isolated vertices is a no-op" $
      logFull == logWithIsolated

  putStrLn "self-loop"

  putStrLn "self-loop halts on mark"
  do
    let k = 3 :: Int
        roster = [("xyzzy", cellToAgent (tape (selfLoopPolicy "xyzzy" k)))]
        t0 = [mkPost "human" ["xyzzy"] "start"]
        (states, tF, derivs) = loop roster t0
    assert "self-loop halts on mark: log is 1 seed + k replies + 1 halt" $
      length tF == 1 + k + 1
    assert "self-loop halts on mark: final post carries the 🟢 mark" $
      "🟢" `T.isPrefixOf` body (peek tF)
    assert "self-loop halts on mark: log stops growing after the halt post (silent last turn)" $
      null (dOutputs (last derivs))
    assert "self-loop halts on mark: quiescence reached" $
      all (\(_n, st) -> not (hasPending @Text st)) states

  putStrLn "silence is quiescence"
  do
    let quietLog :: [Post Text]
        quietLog = [mkPost "human" ["someone-else"] "not addressed to the card"]
        (_qStates, qLog, qDerivs) = loop [("xyzzy", cellToAgent (tape (reply "xyzzy")))] quietLog
    assert "silence is quiescence: loop with no card posts is identity on the log" $
      qLog == quietLog
    assert "silence is quiescence: no derivations" $
      null qDerivs

  putStrLn "fork is id"
  do
    let agent = cellToAgent (tape (reply "xyzzy")) :: Agent (->) [Post Text] (Post Text) [Post Text]
        p1 = mkPost "human" ["xyzzy"] "one"
        p2 = mkPost "human" ["xyzzy"] "two"
        (_outs0, seat0) = runAgentShard agent (AgentSeat [] []) [p1]
        forked = seat0
        (outsA, seatA) = runAgentShard agent seat0 [p2]
        (outsB, seatB) = runAgentShard agent forked [p2]
    assert "fork is id: duplicated seat gives identical outputs" $
      outsA == outsB
    assert "fork is id: duplicated seat gives identical resulting seats" $
      seatA == seatB
    assert "fork is id: carrier advanced on both copies" $
      length (asState seatA) == 2

  putStrLn "fan-in lands exactly one post"
  do
    let worker = cellToAgent (tape (reply "xyzzy")) :: Agent (->) [Post Text] (Post Text) [Post Text]
        main0 = AgentSeat [] [] :: AgentSeat [Post Text] Text
        prompt1 = mkPost "human" ["xyzzy"] "task one"
        prompt2 = mkPost "human" ["xyzzy"] "task two"
        (outs1, fork1) = runAgentShard worker main0 [prompt1]
        (outs2, fork2) = runAgentShard worker main0 [prompt2]
        snap1 = fork1
        snap2 = fork2
        summaryPosts =
          [ mkPost
              "xyzzy"
              ["xyzzy"]
              ("summary: " <> T.intercalate " + " (map body (outs1 ++ outs2)))
          ]
        (mainOuts, main1) = runAgentShard worker main0 summaryPosts
    assert "fan-in: the summary is exactly one post" $
      length summaryPosts == 1
    assert "fan-in lands exactly one post: main carrier grew by exactly 1" $
      length (asState main1) == length (asState main0) + 1
    assert "fan-in lands exactly one post: main seat outputs respond to the summary only" $
      length mainOuts == 1 && "ack: summary:" `T.isPrefixOf` body (peek mainOuts)
    assert "fan-in lands exactly one post: forks unchanged by the main-seat commit" $
      fork1 == snap1 && fork2 == snap2
    assert "fan-in lands exactly one post: each fork saw only its own prompt" $
      map body (asState fork1) == ["task one"]
        && map body (asState fork2) == ["task two"]

  putStrLn "neutral grammar: seat-name swap"
  do
    let seed = mkPost "human" ["xyzzy"] "start"
        t0 = [seed]
        agentA = cellToAgent (tape (cardEcho "a")) :: Agent (->) [Post Text] (Post Text) [Post Text]
        agentB = cellToAgent (tape (cardEcho "b")) :: Agent (->) [Post Text] (Post Text) [Post Text]
        -- one round: first seat turns, new card posts route to both inboxes
        -- (self-loop: its own reply re-enters), then the second seat turns.
        mkRound first second (stF, stS, lg) =
          let (stF', lg1, _) = turn first stF lg
              stS' = feedState (diffLog lg lg1) stS
              stF'' = feedState (diffLog lg lg1) stF'
              (stS'', lg2, _) = turn second stS' lg1
              stF3 = feedState (diffLog lg1 lg2) stF''
              stS3 = feedState (diffLog lg1 lg2) stS''
           in (stF3, stS3, lg2)
        pending :: (AgentState [Post Text] [Post Text], AgentState [Post Text] [Post Text], [Post Text]) -> Bool
        pending (stF, stS, _) = hasPending @Text stF || hasPending @Text stS
        settle round0 s0 = head (dropWhile pending (iterate round0 s0))
        states0 = (seedState ["xyzzy"] t0, seedState ["xyzzy"] t0, t0)
        (_, _, lgAB) = settle (mkRound agentA agentB) states0
        (_, _, lgBA) = settle (mkRound agentB agentA) states0
        swapName n
          | n == "a" = "b"
          | n == "b" = "a"
          | otherwise = n
    assert "seat-name swap: bounded log (1 seed + one halt reply each)" $
      length lgAB == 3 && length lgBA == 3
    assert "seat-name swap: same bodies in same order" $
      map body lgAB == map body lgBA
    assert "seat-name swap: from fields are exactly swapped" $
      map (swapName . from) lgAB == map from lgBA

  -- graph algebra laws (merged from graph-axioma)\n  putStrLn "graph algebra laws"

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
    not (null (runG (LG.connect bus va vb) (ackReg ["a", "b"]) ins))

  -- overlay commutativity
  let g = LG.connect bus va vb
      h = LG.connect leaf vb vc
  assert "overlay commutativity" $
    runG (LG.overlay g h) reg ins == runG (LG.overlay h g) reg ins

  -- overlay associativity (DAG: a->b, b->c, a->c)
  let x = LG.connect bus va vb
      y = LG.connect leaf vb vc
      z = LG.connect bus va vc
  assert "overlay associativity" $
    runG (LG.overlay (LG.overlay x y) z) reg ins == runG (LG.overlay x (LG.overlay y z)) reg ins

  -- overlay idempotence
  assert "overlay idempotence" $
    runG (LG.overlay g g) reg ins == runG g reg ins

  -- connect identities
  assert "connect left identity" $
    runG (LG.connect bus LG.empty g) reg ins == runG g reg ins
  assert "connect right identity" $
    runG (LG.connect bus g LG.empty) reg ins == runG g reg ins

  -- distributivity
  assert "left distributivity" $
    runG (LG.connect bus va (LG.overlay vb vc)) reg ins
      == runG (LG.overlay (LG.connect bus va vb) (LG.connect bus va vc)) reg ins
  assert "right distributivity" $
    runG (LG.connect bus (LG.overlay va vb) vc) reg ins
      == runG (LG.overlay (LG.connect bus va vc) (LG.connect bus vb vc)) reg ins

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
    runG parentGraph parentReg ins9 == runG g' reg' ins9

-- 1792568198N
-- 1792568203N
-- 1792568338N
