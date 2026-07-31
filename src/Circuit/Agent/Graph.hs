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
    AgentRegistry,
    GraphAgent,

    -- * Construction
    channel,
    bus,
    star,
    chain,

    -- * Interpretation
    channelMap,
    toRoster,
    runGraph,
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

-- | Registry of pure agents, all using the common log carrier @[Post]@.
type AgentRegistry = Map Name (Agent (->) [Post] Post [Post])

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

-- | Build a roster from the graph by routing each agent's outputs along its
-- outgoing edges and subscribing it to its incoming edges.
toRoster :: AgentGraph -> AgentRegistry -> [(Name, GraphAgent)]
toRoster graph registry =
  [ (n, routeAgent (viOut info) inner)
  | (n, info) <- Map.toList (channelMap graph),
    Just inner <- [Map.lookup n registry]
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
