{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | QuickCheck oracles for the algebraic graph wiring of agent meetings.
module Main (main) where

import Algebra.Graph.Labelled qualified as LG
import Circuit.Agent
  ( Agent,
    Post (..),
    tape,
  )
import Circuit.Agent.Graph
  ( AgentGraph,
    AgentNode (..),
    AgentRegistry,
    ChannelSet,
    atomic,
    channel,
    flatten,
    nested,
    runGraph,
    toAgent,
  )
import Data.List (sortOn)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Test.QuickCheck
  ( Arbitrary (..),
    Gen,
    Property,
    Testable,
    chatty,
    counterexample,
    elements,
    forAll,
    forAllBlind,
    isSuccess,
    listOf,
    listOf1,
    oneof,
    quickCheckWithResult,
    resize,
    sized,
    stdArgs,
    vectorOf,
    (===),
  )

-------------------------------------------------------------------------
-- Generators
-------------------------------------------------------------------------

allNames :: [Text]
allNames = ["a", "b", "c"]

allChannels :: [Text]
allChannels = ["bus", "leaf"]

genName :: Gen Text
genName = elements allNames

genChannel :: Gen Text
genChannel = elements allChannels

genChannelSet :: Gen ChannelSet
genChannelSet = Set.fromList <$> listOf genChannel

genGraph :: Gen AgentGraph
genGraph = sized go
  where
    go 0 = oneof [pure LG.empty, LG.vertex <$> genName]
    go n =
      resize (n `div` 2) $
        oneof
          [ LG.vertex <$> genName,
            LG.overlay <$> go (n - 1) <*> go (n - 1),
            LG.connect <$> genChannelSet <*> go (n - 1) <*> go (n - 1)
          ]

instance Arbitrary AgentGraph where
  arbitrary = resize 4 genGraph
  shrink = const []

data Policy = Echo | Tag Text | Const Text
  deriving (Eq, Show)

policyAgent :: Policy -> Agent (->) [Post Text] (Post Text) [Post Text]
policyAgent Echo = tape $ \hist ->
  let p = head hist
   in [p {from = "agent", to = [], body = "ack:" <> body p}]
policyAgent (Tag name) = tape $ \hist ->
  let p = head hist
   in [p {from = name, to = [], body = name <> ":" <> body p}]
policyAgent (Const txt) =
  tape $
    const
      [Post {from = "agent", to = [], thread = Nothing, body = txt}]

genPolicy :: Gen Policy
genPolicy =
  oneof
    [ pure Echo,
      Tag <$> genName,
      Const <$> elements ["one", "two", "three"]
    ]

genRegistry :: AgentGraph -> Gen AgentRegistry
genRegistry g = do
  let names = Set.toList (LG.vertexSet g)
  policies <- vectorOf (length names) genPolicy
  pure (Map.fromList (zip names (map (atomic . policyAgent) policies)))

genPost :: Gen (Post Text)
genPost = do
  sender <- genName
  ch <- genChannel
  b <- elements ["one", "two", "three"]
  pure (Post {from = sender, to = [ch], thread = Nothing, body = b})

genInputs :: Gen [Post Text]
genInputs = listOf1 genPost

-------------------------------------------------------------------------
-- Running and comparing
-------------------------------------------------------------------------

run :: AgentGraph -> AgentRegistry -> [Post Text] -> [Post Text]
run g reg ins = sortOn (\p -> (from p, body p)) (runGraph g reg ins)

-------------------------------------------------------------------------
-- Algebraic laws
-------------------------------------------------------------------------

data Triple = Triple AgentGraph AgentGraph AgentGraph
  deriving (Show)

instance Arbitrary Triple where
  arbitrary = Triple <$> arbitrary <*> arbitrary <*> arbitrary
  shrink = const []

data GraphChannel = GraphChannel AgentGraph ChannelSet
  deriving (Show)

instance Arbitrary GraphChannel where
  arbitrary = GraphChannel <$> arbitrary <*> genChannelSet
  shrink = const []

data GraphPair = GraphPair AgentGraph AgentGraph
  deriving (Show)

instance Arbitrary GraphPair where
  arbitrary = GraphPair <$> arbitrary <*> arbitrary
  shrink = const []

-- | A parent graph with one nested vertex containing a single inner agent.
data NestedGraph = NestedGraph AgentGraph AgentRegistry

instance Show NestedGraph where
  show (NestedGraph g _reg) = "NestedGraph (" ++ show (LG.vertexSet g) ++ ")"

instance Arbitrary NestedGraph where
  arbitrary = do
    innerPolicy <- genPolicy
    outerPolicy <- genPolicy
    let innerGraph = LG.vertex "x"
        innerReg = Map.fromList [("x", atomic (policyAgent innerPolicy))]
        parentGraph = LG.connect (channel "outer") (LG.vertex "nested") (LG.vertex "a")
        parentReg =
          Map.fromList
            [ ("nested", nested innerGraph innerReg),
              ("a", atomic (policyAgent outerPolicy))
            ]
    pure (NestedGraph parentGraph parentReg)
  shrink = const []

prop_overlay_comm :: GraphPair -> Property
prop_overlay_comm (GraphPair g h) =
  forAllBlind (genRegistry (LG.overlay g h)) $ \reg ->
    forAll genInputs $ \ins ->
      run (LG.overlay g h) reg ins === run (LG.overlay h g) reg ins

prop_overlay_assoc :: Triple -> Property
prop_overlay_assoc (Triple x y z) =
  let g = LG.overlay (LG.overlay x y) z
      h = LG.overlay x (LG.overlay y z)
   in forAllBlind (genRegistry g) $ \reg ->
        forAll genInputs $ \ins ->
          run g reg ins === run h reg ins

prop_overlay_idemp :: AgentGraph -> Property
prop_overlay_idemp g =
  forAllBlind (genRegistry g) $ \reg ->
    forAll genInputs $ \ins ->
      run (LG.overlay g g) reg ins === run g reg ins

prop_connect_left_identity :: GraphChannel -> Property
prop_connect_left_identity (GraphChannel g chs) =
  forAllBlind (genRegistry g) $ \reg ->
    forAll genInputs $ \ins ->
      run (LG.connect chs LG.empty g) reg ins === run g reg ins

prop_connect_right_identity :: GraphChannel -> Property
prop_connect_right_identity (GraphChannel g chs) =
  forAllBlind (genRegistry g) $ \reg ->
    forAll genInputs $ \ins ->
      run (LG.connect chs g LG.empty) reg ins === run g reg ins

prop_left_distributivity :: Triple -> Property
prop_left_distributivity (Triple x y z) =
  forAll genChannelSet $ \chs ->
    let g = LG.connect chs x (LG.overlay y z)
        h = LG.overlay (LG.connect chs x y) (LG.connect chs x z)
     in forAllBlind (genRegistry (LG.overlay g h)) $ \reg ->
          forAll genInputs $ \ins ->
            run g reg ins === run h reg ins

prop_right_distributivity :: Triple -> Property
prop_right_distributivity (Triple x y z) =
  forAll genChannelSet $ \chs ->
    let g = LG.connect chs (LG.overlay x y) z
        h = LG.overlay (LG.connect chs x z) (LG.connect chs y z)
     in forAllBlind (genRegistry (LG.overlay g h)) $ \reg ->
          forAll genInputs $ \ins ->
            run g reg ins === run h reg ins

prop_decomposition :: Triple -> Property
prop_decomposition (Triple x y z) =
  forAll genChannelSet $ \chs ->
    let g = LG.connect chs (LG.connect chs x y) z
        h =
          LG.overlay
            (LG.connect chs x y)
            (LG.overlay (LG.connect chs x z) (LG.connect chs y z))
     in forAllBlind (genRegistry (LG.overlay g h)) $ \reg ->
          forAll genInputs $ \ins ->
            run g reg ins === run h reg ins

-- | Orchestrator law: a nested vertex expands to the same behaviour as the
-- flattened graph.
prop_orchestrator_flatten :: NestedGraph -> Property
prop_orchestrator_flatten (NestedGraph g reg) =
  forAll genInputs $ \ins ->
    let (g', reg') = flatten g reg
     in run g reg ins === run g' reg' ins

-------------------------------------------------------------------------
-- Test runner
-------------------------------------------------------------------------

check :: (Testable prop) => String -> prop -> IO Bool
check name p = do
  putStrLn ("  " ++ name)
  result <- quickCheckWithResult (stdArgs {chatty = False}) p
  if isSuccess result
    then pure True
    else do
      putStrLn ("    FAIL: " ++ show result)
      pure False

main :: IO ()
main = do
  putStrLn "circuits-agent graph-law oracles"
  ok <-
    and
      <$> sequence
        [ check "overlay commutativity" prop_overlay_comm,
          check "overlay associativity" prop_overlay_assoc,
          check "overlay idempotence" prop_overlay_idemp,
          check "connect left identity" prop_connect_left_identity,
          check "connect right identity" prop_connect_right_identity,
          check "left distributivity" prop_left_distributivity,
          check "right distributivity" prop_right_distributivity,
          check "decomposition" prop_decomposition,
          check "orchestrator flattening" prop_orchestrator_flatten
        ]
  if ok
    then putStrLn "All graph-law oracles passed"
    else error "graph-law oracle failure"
