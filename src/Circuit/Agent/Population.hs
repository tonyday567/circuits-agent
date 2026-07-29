{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Population churn: discrete birth and death of agents.
--
-- This is S3 of agent-grad: continuous weight updates on edges and discrete
-- node birth/death are kept separate in the API.  A population schedule
-- describes which agents exist during each meeting; events are applied
-- *between* meetings, so the roster and its wiring type can change from one
-- meeting to the next.
module Circuit.Agent.Population
  ( -- * Homogeneous-carrier population
    PopEvent (..),
    applyPopEvents,
    loopPop,
    loopsPop,
    -- * Heterogeneous-carrier population
    HPopAgent (..),
    HPopEvent (..),
    birthHPopAgent,
    loopHPop,
    loopsHPop,
  )
where

import Circuit.Agent
  ( Agent,
    AgentState (..),
    Derivation,
    Log,
    Post,
    appendInbox,
    deliversTo,
    emptyAgentState,
    emptyInbox,
    hasPending,
    loopWith,
    turn,
    watch,
  )
import Circuit.Stream (Cons, Snoc, These (..), Uncons, snocNil, uncons)
import Data.List (foldl')
import Data.Text (Text)

-- | A discrete population event.
--
-- * 'Birth' adds an agent with an optional initial carrier.  Its inbox is
--   seeded from the current log, so it sees posts already addressed to it.
--   If the name already exists, the old agent and its state are dropped and
--   replaced — i.e. 'Birth' on a live name is a silent respawn.
-- * 'Death' removes an agent and its state.
data PopEvent s
  = Birth Text (Agent s) (Maybe s)
  | Death Text

-- | Apply a list of population events to a roster and agent states.
--
-- The current log is used to seed the inbox of any born agent.
applyPopEvents ::
  forall s f.
  (Snoc s Post, Snoc f Post, Uncons f Post) =>
  Log f ->
  [(Text, Agent s)] ->
  [(Text, AgentState s f)] ->
  [PopEvent s] ->
  ([(Text, Agent s)], [(Text, AgentState s f)])
applyPopEvents lg roster states events =
  let (roster', states') = foldl' applyEvent (roster, states) events
   in (roster', states')
  where
    applyEvent (r, st) (Death name) =
      (filter ((/= name) . fst) r, filter ((/= name) . fst) st)
    applyEvent (r, st) (Birth name agent mcarrier) =
      let r' = filter ((/= name) . fst) r ++ [(name, agent)]
          st' = filter ((/= name) . fst) st
          carrier = case mcarrier of
            Just s -> s
            Nothing -> asCarrier (emptyAgentState @s @f name)
          inbox = foldl' (flip appendInbox) (emptyInbox @f name) (watch name lg)
          st'' = st' ++ [(name, AgentState carrier inbox)]
       in (r', st'')

-- | Run a sequence of meetings, applying population events before each one.
--
-- The first meeting runs with the initial roster/states; @events !! 0@ is
-- applied before the second meeting, @events !! 1@ before the third, etc.
-- An empty schedule runs zero meetings and returns the initial
-- roster/states/log with no derivations.
loopPop ::
  forall s f.
  (Snoc s Post, Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, Agent s)] ->
  [(Text, AgentState s f)] ->
  Log f ->
  [[PopEvent s]] ->
  ([(Text, Agent s)], [(Text, AgentState s f)], Log f, [Derivation])
loopPop roster0 states0 log0 schedules =
  last (loopsPop roster0 states0 log0 schedules)

-- | Transitive unfolding of population meetings.
--
-- Returns the state after each meeting (including the initial state before any
-- events are applied).  The derivation list is cumulative: element @k@ contains
-- every derivation produced up to and including meeting @k@.
loopsPop ::
  forall s f.
  (Snoc s Post, Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, Agent s)] ->
  [(Text, AgentState s f)] ->
  Log f ->
  [[PopEvent s]] ->
  [([(Text, Agent s)], [(Text, AgentState s f)], Log f, [Derivation])]
loopsPop roster0 states0 log0 schedules =
  (roster0, states0, log0, []) : go roster0 states0 log0 [] schedules
  where
    go _ _ _ _ [] = []
    go roster states lg derivs (events : rest) =
      let (roster', states', lg', derivs') = step (roster, states, lg, derivs) events
       in (roster', states', lg', derivs') : go roster' states' lg' derivs' rest

    step (roster, states, lg, derivs) events =
      let (roster', states') = applyPopEvents lg roster states events
          (states'', lg', derivs') = loopWith roster' states' lg
       in (roster', states'', lg', derivs ++ derivs')

-- ---------------------------------------------------------------------------
-- Heterogeneous-carrier population
--
-- The homogeneous API above forces every agent in a roster to share the same
-- carrier type @s@.  The API below hides each agent's carrier in an
-- existential, so a single population can mix agents with different carriers
-- (e.g. one agent with carrier @[Post]@ and another with carrier @(Bool,
-- [Post])@).  This is the population-level analogue of the behavioural
-- quotient used elsewhere: the roster is a list of named agents, but the
-- meeting runner no longer knows the carrier type of any entry.
-- ---------------------------------------------------------------------------

-- | An agent bundled with its own state, hiding the carrier type.
data HPopAgent f where
  HPopAgent :: Agent s -> AgentState s f -> HPopAgent f

-- | A discrete population event for a heterogeneous roster.
--
-- * 'HBirth' adds a named agent already bundled with its state.  Use
--   'birthHPopAgent' to construct the bundle so the inbox is seeded from the
--   current log.
-- * 'HDeath' removes an agent and its state.
data HPopEvent f
  = HBirth Text (HPopAgent f)
  | HDeath Text

-- | Construct a bundled agent for a heterogeneous roster.
--
-- The carrier is taken from the optional argument, or started empty.  The
-- inbox is seeded from the current log, so a newborn sees posts already
-- addressed to it.
birthHPopAgent ::
  forall s f.
  (Snoc s Post, Snoc f Post, Uncons f Post) =>
  Text ->
  Agent s ->
  Maybe s ->
  Log f ->
  HPopAgent f
birthHPopAgent name agent mcarrier lg =
  let carrier = case mcarrier of
        Just s -> s
        Nothing -> snocNil @s @Post
      inbox = foldl' (flip appendInbox) (emptyInbox @f name) (watch name lg)
   in HPopAgent agent (AgentState carrier inbox)

-- | Apply a list of heterogeneous population events to a roster.
applyHPopEvents ::
  forall f.
  Log f ->
  [(Text, HPopAgent f)] ->
  [HPopEvent f] ->
  [(Text, HPopAgent f)]
applyHPopEvents _lg roster events = foldl' applyEvent roster events
  where
    applyEvent r (HDeath name) = filter ((/= name) . fst) r
    applyEvent r (HBirth name ha) = filter ((/= name) . fst) r ++ [(name, ha)]

-- | Run a sequence of heterogeneous meetings, applying events before each one.
loopHPop ::
  forall f.
  (Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, HPopAgent f)] ->
  Log f ->
  [[HPopEvent f]] ->
  ([(Text, HPopAgent f)], Log f, [Derivation])
loopHPop roster0 log0 schedules =
  last (loopsHPop roster0 log0 schedules)

-- | Transitive unfolding of heterogeneous population meetings.
loopsHPop ::
  forall f.
  (Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, HPopAgent f)] ->
  Log f ->
  [[HPopEvent f]] ->
  [([(Text, HPopAgent f)], Log f, [Derivation])]
loopsHPop roster0 log0 schedules =
  (roster0, log0, []) : go roster0 log0 [] schedules
  where
    go _ _ _ [] = []
    go roster lg derivs (events : rest) =
      let roster' = applyHPopEvents lg roster events
          (roster'', lg', derivs') = hMeetingPass roster' lg derivs
       in (roster'', lg', derivs') : go roster'' lg' derivs' rest

-- | One heterogeneous meeting: round-robin turns until quiescence.
hMeetingPass ::
  forall f.
  (Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, HPopAgent f)] ->
  Log f ->
  [Derivation] ->
  ([(Text, HPopAgent f)], Log f, [Derivation])
hMeetingPass roster0 lg0 derivs0 = go roster0 lg0 derivs0
  where
    go roster lg derivs
      | not (any (hasPendingH . snd) roster) = (roster, lg, derivs)
      | otherwise =
          let (roster', lg', derivs') = hPass roster lg derivs
           in go roster' lg' derivs'

    hasPendingH (HPopAgent _ st) = hasPending st

    hPass roster lg derivs = foldl' step (roster, lg, derivs) roster
      where
        step (rs, l, ds) (name, _) =
          case lookup name rs of
            Nothing -> (rs, l, ds)
            Just (HPopAgent agent sti)
              | hasPending sti ->
                  let (st', l', md) = turn agent sti l
                      newCount = streamLengthPost l' - streamLengthPost l
                      newPosts = takeStreamPost newCount l'
                      replaced = map (replaceState name agent st') rs
                      rs' = foldl' routePost replaced newPosts
                      ds' = maybe ds (\d -> ds ++ [d]) md
                   in (rs', l', ds')
              | otherwise -> (rs, l, ds)

        replaceState name' agent' st' (n, ha)
          | n == name' = (n, HPopAgent agent' st')
          | otherwise = (n, ha)

        routePost rs p = map (routeAgent p) rs

        routeAgent p (n, HPopAgent agent st)
          | deliversTo p n = (n, HPopAgent agent (st {asInbox = appendInbox p (asInbox st)}))
          | otherwise = (n, HPopAgent agent st)

-- | Length of a post stream, used to detect how many posts one turn appended.
streamLengthPost :: forall f. (Uncons f Post) => f -> Int
streamLengthPost s = go 0 s
  where
    go :: Int -> f -> Int
    go n stream =
      case uncons @f @Post stream of
        That _ -> n
        This _ -> n + 1
        These _ rest -> go (n + 1) rest

-- | Take the first @n@ posts from a stream, oldest first.
takeStreamPost :: forall f. (Uncons f Post) => Int -> f -> [Post]
takeStreamPost n s = go n s []
  where
    go :: Int -> f -> [Post] -> [Post]
    go 0 _ acc = acc
    go n' stream acc =
      case uncons @f @Post stream of
        That _ -> acc
        This x -> x : acc
        These x rest -> go (n' - 1) rest (x : acc)
