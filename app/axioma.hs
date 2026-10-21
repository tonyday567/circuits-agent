{-# LANGUAGE OverloadedStrings #-}

-- | circuits-agent oracle tests — thin dispatcher over the 'Axioma' topics.
--
-- The accretion monolith is split into topic modules on the circuits canon
-- model: one command per topic plus @all@.  The topic modules are the
-- curation; oracle IDs (A0/A1, O1/O2, S0a, Q1-Q5, M1-M3, S1-S6, T1) are
-- kept where wave journals reference them.
module Main (main) where

import Axioma.Delivery (deliveryTopic)
import Axioma.Framing (framingTopic)
import Axioma.Graph (graphTopic)
import Axioma.Loops (loopsTopic)
import Axioma.Marks (marksTopic)
import Axioma.Ports (portsTopic)
import Axioma.ShardTensors (shardTensorsTopic)
import Axioma.Shards (shardsTopic)
import Axioma.Tape (tapeTopic)
import Axioma.Tensors (tensorsTopic)
import Axioma.Turns (turnsTopic)
import Options.Applicative
import Prelude hiding (id, (.))

data Topic
  = All
  | Tape
  | Delivery
  | Turns
  | Shards
  | Ports
  | Graph
  | Tensors
  | Loops
  | Marks
  | ShardTensors
  | Framing
  deriving (Show, Eq, Bounded, Enum)

topicName :: Topic -> String
topicName All = "all"
topicName Tape = "tape"
topicName Delivery = "delivery"
topicName Turns = "turns"
topicName Shards = "shards"
topicName Ports = "ports"
topicName Graph = "graph"
topicName Tensors = "tensors"
topicName Loops = "loops"
topicName Marks = "marks"
topicName ShardTensors = "shardtensors"
topicName Framing = "framing"

topicDesc :: Topic -> String
topicDesc All = "run all topics"
topicDesc Tape = "tape/behaviour laws: A0/A1, O1/O2/S3, compaction, run1 monologue (M3)"
topicDesc Delivery = "addressed-log delivery laws: semiring/FinRel matrices, Chu spaces, S0b/G1"
topicDesc Turns = "turn and meeting laws: turn integrity, loop quiescence, multi-seat cards"
topicDesc Shards = "shard combinators, agent-as-shard, branch agent, token ports"
topicDesc Ports = "process ports: death honesty (S1-S3/S5/S6), merged stdio (S4), nonce turns (T1)"
topicDesc Graph = "wiring-graph oracles and graph-algebra laws (graph-axioma merged)"
topicDesc Tensors = "race/await tensors at every level, STM rung, S/X agents"
topicDesc Loops = "self-loops: S-agent, spikes, Loop Either citizen"
topicDesc Marks = "the mark grammar, halt oracles, content-decided turns"
topicDesc ShardTensors = "shard-level tensor laws"
topicDesc Framing = "framing, query adapters, ancestry oracles, cursors"

topicParser :: Parser Topic
topicParser =
  subparser $
    foldr
      (<>)
      (commandGroup "Topics:")
      [ command
          (topicName t)
          (info (pure t <**> helper) (progDesc (topicDesc t)))
      | t <- [minBound .. maxBound],
        t /= All
      ]
      <> command
        "all"
        (info (pure All <**> helper) (progDesc (topicDesc All)))

opts :: ParserInfo Topic
opts =
  info
    (topicParser <**> helper)
    ( fullDesc
        <> progDesc "Run circuits-agent oracles by topic"
        <> header "circuits-agent-axioma — topic-selectable axiom oracles"
    )

runTopic :: Topic -> IO ()
runTopic All = mapM_ runTopic (filter (/= All) [minBound .. maxBound])
runTopic Tape = tapeTopic
runTopic Delivery = deliveryTopic
runTopic Turns = turnsTopic
runTopic Shards = shardsTopic
runTopic Ports = portsTopic
runTopic Graph = graphTopic
runTopic Tensors = tensorsTopic
runTopic Loops = loopsTopic
runTopic Marks = marksTopic
runTopic ShardTensors = shardTensorsTopic
runTopic Framing = framingTopic

main :: IO ()
main = do
  putStrLn "circuits-agent oracle tests"
  topic <- execParser opts
  runTopic topic
  putStrLn "All tests passed"
-- 1792562305N
-- 1792562336N
