{-# LANGUAGE OverloadedStrings #-}

-- | Algebraic wiring of agent meetings.
--
-- Vertices are agent names; edges are labelled with sets of channels
-- (names in 'Post.to'). The algebra is borrowed from @algebraic-graphs@:
--
-- * 'LG.empty' — no agents.
-- * 'LG.vertex' — a single agent.
-- * 'LG.overlay' — independent subgraphs (no new delivery edges).
-- * 'LG.connect' — every agent on the left may post to the channel(s);
--   every agent on the right subscribes to them.
--
-- This captures broadcast buses, stars, chains, and (via a registry that maps
-- a name to a whole subgraph) hierarchical orchestrators.
module Circuit.Agent.Graph
  ( -- * Graph of agents
    AgentGraph,
    ChannelSet,
    AgentNode (..),
    AgentRegistry,
    GraphAgent,

    -- * Construction
    channel,
    bus,
    star,
    chain,
    atomic,
    nested,

    -- * Interpretation
    channelMap,
    toRoster,
    runGraph,
    toAgent,
    flatten,
  )
where

import Algebra.Graph.Labelled qualified as LG
import Circuit.Agent
  ( Agent,
    AgentSeat (..),
    AgentState (..),
    Name,
    Post (..),
    appendInbox,
    emptyInbox,
    loopWith,
    runAgentShard,
    watch,
  )
import Circuit.Poly (System (..))
import Data.List (foldl')
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Prelude hiding (lookup)

-- | A channel is just a 'Name' that appears in 'Post.to'.
type Channel = Name

-- | A set of channels carried by one graph edge.
type ChannelSet = Set Channel

-- | Wiring graph: vertices are agent names, edges are sets of channels.
type AgentGraph = LG.Graph ChannelSet Name

-- | A registry entry is either an atomic pure agent or a nested subgraph.
data AgentNode
  = AtomicAgent (Agent (->) [Post] Post [Post])
  | NestedAgent AgentGraph AgentRegistry

-- | Registry of agents.  Names map to atomic agents or whole subgraphs.
type AgentRegistry = Map Name AgentNode

-- | Smart constructor for an atomic registry entry.
atomic :: Agent (->) [Post] Post [Post] -> AgentNode
atomic = AtomicAgent

-- | Smart constructor for a nested registry entry.
nested :: AgentGraph -> AgentRegistry -> AgentNode
nested = NestedAgent

-- | An agent after graph routing has been applied: the carrier holds the
-- original history plus the output associated with the current state.
type GraphAgent = Agent (->) ([Post], Maybe [Post]) Post [Post]

-- | A single channel as an edge label.
channel :: Channel -> ChannelSet
channel = Set.singleton

-- | Every named agent posts to and subscribes to @ch@.
--
-- This is the public-bus configuration.
bus :: [Name] -> Channel -> AgentGraph
bus names ch =
  let vs = LG.vertices names
   in LG.connect (channel ch) vs vs

-- | A hub agent that posts to @hubCh@; leaf agents post to @leafCh@.
star :: Name -> [Name] -> Channel -> Channel -> AgentGraph
star hub leaves hubCh leafCh =
  let hubV = LG.vertex hub
      leafV = LG.vertices leaves
   in LG.connect (channel hubCh) hubV leafV
        `LG.overlay` LG.connect (channel leafCh) leafV hubV

-- | Chain agents left-to-right on a single channel.
chain :: [Name] -> Channel -> AgentGraph
chain names ch =
  case names of
    [] -> LG.empty
    (n : ns) -> go (LG.vertex n) ns
  where
    go g [] = g
    go g (n : ns) = go (LG.connect (channel ch) g (LG.vertex n)) ns

-- | Per-vertex incoming and outgoing channel sets.
data VertexInfo = VertexInfo
  { viIn :: ChannelSet,
    viOut :: ChannelSet
  }

emptyInfo :: VertexInfo
emptyInfo = VertexInfo Set.empty Set.empty

mergeInfo :: VertexInfo -> VertexInfo -> VertexInfo
mergeInfo (VertexInfo i1 o1) (VertexInfo i2 o2) =
  VertexInfo (Set.union i1 i2) (Set.union o1 o2)

-- | Compute subscriptions and addressing for every agent in the graph.
channelMap :: AgentGraph -> Map Name VertexInfo
channelMap = LG.foldg Map.empty singleton connectInfo
  where
    singleton n = Map.singleton n emptyInfo
    connectInfo chs left right =
      let addOut = Map.map (\info -> info {viOut = Set.union chs (viOut info)})
          addIn = Map.map (\info -> info {viIn = Set.union chs (viIn info)})
          left' = if Set.null chs || Map.null right then left else addOut left
          right' = if Set.null chs || Map.null left then right else addIn right
       in Map.unionWith mergeInfo left' right'

-- | Wrap an agent so its emitted posts are addressed to the given channels.
--
-- The outer carrier is @(innerHistory, lastOutput)@. Moore output is read from
-- the state, so we store the routed output produced by the most recent input
-- and return it on the next observation.
routeAgent :: ChannelSet -> Agent (->) [Post] Post [Post] -> GraphAgent
routeAgent outChs inner =
  System $ \((hist, mout), d) ->
    case d of
      Left _ -> ((hist, mout), (fromMaybe [] mout, ()))
      Right inp ->
        let (outs, seat') = runAgentShard inner (AgentSeat hist []) [inp]
            routed = map (\p -> p {to = Set.toList outChs}) outs
         in ((asState seat', Just routed), (fromMaybe [] mout, ()))

-- | Inject parent-imposed channels into a subgraph.  Every internal vertex
-- receives the incoming channels and gains the outgoing channels, so that
-- hierarchical interpretation (nested agent) and flattening agree.
injectChannels :: ChannelSet -> ChannelSet -> AgentGraph -> AgentGraph
injectChannels ins outs g =
  LG.overlay (LG.connect ins LG.empty g) (LG.connect outs g LG.empty)

-- | Interpret a graph as a single agent.  The carrier is the input history;
-- each new post is fed to the graph and the freshly generated posts are
-- emitted.
toAgent :: AgentGraph -> AgentRegistry -> Agent (->) [Post] Post [Post]
toAgent graph registry =
  System $ \(hist, d) ->
    case d of
      Left _ -> (hist, ([], ()))
      Right inp ->
        let hist' = hist ++ [inp]
            logBefore = runGraph graph registry hist
            logAfter = runGraph graph registry hist'
            newPosts = drop (length logBefore) logAfter
         in (hist', (newPosts, ()))

-- | Resolve a registry entry into a pure agent.  Nested agents are
-- interpreted as agents over their subgraph with parent channels injected.
resolveNode :: ChannelSet -> ChannelSet -> AgentNode -> Agent (->) [Post] Post [Post]
resolveNode _ _ (AtomicAgent a) = a
resolveNode ins outs (NestedAgent g r) = toAgent (injectChannels ins outs g) r

-- | Build a roster from the graph by routing each agent's outputs along its
-- outgoing edges and subscribing it to its incoming edges.
toRoster :: AgentGraph -> AgentRegistry -> [(Name, GraphAgent)]
toRoster graph registry =
  [ (n, routeAgent (viOut info) (resolveNode (viIn info) (viOut info) node))
  | (n, info) <- Map.toList (channelMap graph),
    Just node <- [Map.lookup n registry]
  ]

-- | Seed a graph-wrapped agent state: inbox sees addressed posts, carrier is
-- empty.
seedGraphState :: [Name] -> [Post] -> AgentState ([Post], Maybe [Post]) [Post]
seedGraphState subs inputs =
  AgentState ([], Nothing) (foldl' (flip appendInbox) (emptyInbox subs) (watch subs inputs))

-- | Run the wired agents against an initial log.
runGraph ::
  AgentGraph ->
  AgentRegistry ->
  [Post] ->
  [Post]
runGraph graph registry inputs =
  let roster = toRoster graph registry
      info = channelMap graph
      subs n = Set.toList (viIn (fromMaybe emptyInfo (Map.lookup n info)))
      states = [(n, seedGraphState (subs n) inputs) | (n, _) <- roster]
   in case loopWith roster states inputs of
        (_, log', _) -> log'

-- | Map over vertex names.
gmapVertices :: (Name -> Name) -> AgentGraph -> AgentGraph
gmapVertices f = LG.foldg LG.empty (LG.vertex . f) LG.connect

-- | Flatten a graph by expanding nested vertices into their subgraphs.
-- Returns a graph whose vertices are all atomic and a registry of those atoms.
-- Nested names are prefixed to avoid collisions.
flatten :: AgentGraph -> AgentRegistry -> (AgentGraph, AgentRegistry)
flatten graph registry = LG.foldg emptyM vertexM connectM graph
  where
    emptyM = (LG.empty, Map.empty)
    vertexM name =
      case Map.lookup name registry of
        Just (NestedAgent g r) ->
          let (g', r') = flatten g r
              prefix = name <> "/"
              g'' = gmapVertices (prefix <>) g'
              r'' = Map.mapKeys (prefix <>) r'
           in (g'', r'')
        Just (AtomicAgent a) -> (LG.vertex name, Map.singleton name (AtomicAgent a))
        Nothing -> (LG.vertex name, Map.empty)
    connectM chs (gl, regL) (gr, regR) =
      (LG.connect chs gl gr, Map.union regL regR)
