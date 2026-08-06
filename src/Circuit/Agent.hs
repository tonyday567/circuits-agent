{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Moore agents on a shared, addressed log; opaque shards for effects.
--
-- Pure agent shape:
--
-- @
-- type Agent arr s a b = System arr s (Mono a b)
-- @
--
-- Free carrier @s@ is required by the pretense (tape vs summary).  The common
-- log case is @Agent (->) [Post] Post [Post]@ — state is the received stream.
-- That carrier is a parse of the tape: each committed @Post@ is one token.
--
-- Effectful boundary (preferred pin):
--
-- @
-- type Shard m a b = Ends (Kleisli m) a b
-- @
--
-- Symmetric in the common log case: commit a list of posts, emit a list of
-- posts.  One-post reality (hit enter) is not another type — lift with @(:[])@
-- on the commit side (@prefixIn@).  'LogEnds' is the same shape (dual seat on
-- the log).  Opacity is commit\/emit only; no interior.
--
-- Change of base (circuits-parser sense): 'agentShard' reinterprets a pure
-- 'Agent' at @Kleisli m@ ends — same Moore citizen, effectful interface.
-- Direct shards (hermes session, muster-agent) skip the pure coalgebra and
-- inhabit 'Shard' only.
--
-- Token seat around a list shard (parser dual): stream @f = [Post]@, token
-- @s = Post@.  'batchEnds' snocs tokens into a stream (build @f@); 'unbatchEnds'
-- peels with the same coalgebra as 'Uncons' on lists.  Compose with the
-- shard via @('>:>')@:
--
-- @
-- portShard = batchEnds … >:> shard >:> unbatchEnds …
--   :: Shard m Post [Post] >:> Shard m [Post] [Post] >:> Shard m [Post] Post
--   :: Port m
-- @
--
-- Queue ends ('openSTM' \/'openIO') are the effectful token wire of the same
-- shape when you need a bare @Post\/@Post@ channel without a shard.
--
-- Design card: @coffee\/loom\/agent.md@.
module Circuit.Agent
  ( -- * Posts and the log
    Post (..),
    PostId,
    mkPost,
    replyTo,
    synthesis,
    sortNub,
    branches,
    cone,
    Log,
    emptyLog,
    Name,

    -- * Pure agents
    Agent,
    AgentState (..),
    emptyAgentState,
    tape,
    selfrec,

    -- * Inbox
    Inbox,
    emptyInbox,
    appendInbox,
    unconsInbox,
    inboxWho,
    inboxSubs,

    -- * Delivery
    deliversTo,

    -- * Effectful ends (symmetric streams)
    Shard,
    LogEnds,
    shard,
    logEnds,

    -- * Agent as Shard (change of base into Kleisli)
    AgentSeat (..),
    feedAgent,
    flushOutbox,
    agentShard,
    runAgentShard,

    -- * Token seat (stream buffers around a Shard)
    Port,
    Snoc (..),
    snocPost,
    batchEnds,
    unbatchEnds,
    portShard,

    -- * Forces
    watch,
    post,
    turn,
    hasPending,
    loop,
    loopWith,
    loops,
    loopHetero,
    meetingLoop,
    seedAgentState,

    -- * Derivations
    Derivation (..),

    -- * Session assembly
    session,

    -- * Running one step
    run1,

    -- * Effectful agents
    agentM,
    runAgentM,

    -- * STM agents (S) and IO-bound agents (X)
    AgentS,
    AgentX,
    agentX,
    awaitS,
    raceS,
    raceIO,
    stepS,
    stepsS,
    runAgentS,
    readEndSTM,
    writeEndSTM,
    agentLoopS,
    selfLoopS,
    agentLoopL,
    selfLoopL,

    -- * Container dial (Bag / Seq log algebra)
    Bag (..),
    TurnLog,
    emptyBag,
    singletonBag,
    insertBag,
    toBag,
    fromBag,

    -- * Behaviour (stream semantics)
    Beh,
    beh,
    after,

    -- * Choice (level-1 grammar fragment)
    branchAgent,

    -- * Seat-level tensors (product / await, coproduct / race)
    awaitA,
    raceA,

    -- * Re-exports for end construction
    Ends (..),
    close,
    endsK,
    prefixIn,
    Queue (..),
    openSTM,
    openIO,

    -- * Shard combinators
    prefixShard,
    suffixShard,
    codecShard,
    composeShard,
    (>:>),
  )
where

import Circuit
  ( Ends (..),
    Queue (..),
    close,
    commit,
    composeEnds,
    dimapEnds,
    emit,
    endsK,
    lmapEnds,
    openIO,
    openSTM,
    prefixIn,
    rmapEnds,
    trace,
    (>:>),
  )
import Circuit.Loop (Loop (..))
import Circuit.Layer (run)
import Circuit.Poly (Eval (..), Mono, System (..), fromEvalSystem, monoDir, monoIn)
import Circuit.Poly.Process (after, runSystem)
import "circuits" Circuit.Stream (Cons (..), Snoc (..), These (..), Uncons (..))
import Control.Arrow (Kleisli (..))
import Control.Concurrent (threadDelay)
import Control.Concurrent.Async (async, cancel, race, wait)
import Control.Concurrent.STM (STM, atomically, orElse)
import Data.Foldable (traverse_)
import Data.List (find, foldl', genericIndex, genericTake, nub, sort)
import Data.Map (Map)
import Numeric.Natural (Natural)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Text (Text, empty)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Circuit.Agent
-- >>> import Circuit.Poly.Process (iterateSystem)

-- | Agent name on the shared log.
type Name = Text

-- | Absolute post identity.  In the stamped log this is the line id assigned
-- by the single writer; in pure meeting logs it is the positional index in
-- the oldest-first log that 'branches' resolves against.
type PostId = Natural

-- | A single entry on the shared log, polymorphic in payload.
--
-- Routing is by name list: a post delivers to every agent whose name appears
-- in 'to' (the audience).  'thread' is the ancestry edges: @[]@ for a root
-- post, otherwise the 'PostId's of the posts being replied to or synthesised
-- from.  Parents are a set (duplicates discarded) in normalised (sorted)
-- order — the smart constructors keep it so.
data Post a = Post
  { from :: Name,
    to :: [Name],
    thread :: [PostId],
    body :: a
  }
  deriving (Show, Eq, Ord, Functor)

-- | A fresh root post (no parents).
mkPost :: Name -> [Name] -> a -> Post a
mkPost f t b = Post f t [] b

-- | A reply: the audience is the parent's sender plus the rest of the
-- parent's audience (minus self); the sole thread edge cites the parent's
-- 'PostId'.
replyTo :: Name -> PostId -> Post a -> b -> Post b
replyTo who parentId p b =
  Post
    { from = who,
      to = from p : filter (/= who) (to p),
      thread = [parentId],
      body = b
    }

-- | A synthesis: one descendant of several parents — the object-level
-- wire-merge dual to merging agents.  The ancestry cites every parent id as
-- a normalised set (sorted, duplicates discarded).
synthesis :: Name -> [Name] -> [PostId] -> b -> Post b
synthesis who audience parentIds b =
  Post
    { from = who,
      to = audience,
      thread = sortNub parentIds,
      body = b
    }

-- | Sorted, duplicate-free.  The normalised-set primitive of the thread
-- design: parent sets, audiences, and cones are all kept in this form.
sortNub :: (Ord a) => [a] -> [a]
sortNub = nub . sort

-- | The label-branches from a post to its conversation roots, resolved
-- against the posts prior to it (oldest first).  Each thread edge is a
-- 'PostId' interpreted as a positional index into the prior log; a dangling
-- id is an error (ids are expected to be valid).  A root post has one trivial
-- branch; every parent edge contributes its own path.  Branches of replies
-- are pure cons:
--
-- prop> branches prior (replyTo who i p b) == map (who :) (branches (take i prior) p)
branches :: [Post a] -> Post a -> [[Name]]
branches prior p0 = go prior p0
  where
    go pre p =
      case thread p of
        [] -> [[from p]]
        is -> concatMap (step pre p) is

    step pre p i =
      let q = pre `genericIndex` i
       in map (from p :) (go (genericTake i pre) q)

-- | The ancestry cone: every name appearing on any branch from a post to
-- its roots, as a normalised set — the "who contributed to this" query,
-- free with the log.  Includes the post's own sender.
--
-- Cone-union law:
--
-- prop> cone prior (synthesis who aud is b) == sortNub (who : concatMap (cone (take i prior)) (map (prior !!) is))
cone :: [Post a] -> Post a -> [Name]
cone prior p = sortNub (concat (branches prior p))

-- | The shared append-only log, newest first.
--
-- The log is a stream of 'Post's.  Common case: @Log [Post]@.  Generalizing to
-- any @f@ with 'Cons' and 'Uncons' lets the same delivery machinery run over
-- other stream representations while keeping the addressed read as a list.
type Log f = f

-- | A bag: finite multiset.  Order is forgotten; multiplicity is kept.
newtype Bag a = Bag (Map a Int)
  deriving (Eq, Show)

-- | The empty bag.
emptyBag :: Bag a
emptyBag = Bag Map.empty

-- | One element.
singletonBag :: a -> Bag a
singletonBag a = Bag (Map.singleton a 1)

-- | Insert one element.
insertBag :: (Ord a) => a -> Bag a -> Bag a
insertBag a (Bag m) = Bag (Map.insertWith (+) a 1 m)

-- | Fold a list into a bag, forgetting order.
toBag :: (Ord a) => [a] -> Bag a
toBag = foldr insertBag emptyBag

-- | Expand a bag into a list in some deterministic order.
fromBag :: Bag a -> [a]
fromBag (Bag m) = concatMap (\(a, n) -> replicate n a) (Map.toList m)

-- | Log algebra: a sequence of bags, one bag per turn.
type TurnLog a = Seq (Bag a)

-- | Agent: a Moore machine with free carrier, polymorphic in the base arrow.
--
-- @System arr s (Mono a b) ≅ arr (s, a) (s, b)@ after collapsing unit
-- positions.  Common log case: @Agent (->) s (Post a) [Post a]@ (input = one post,
-- output = list of posts).  @Agent (Kleisli m) s a b@ is the monadic Moore
-- machine.
type Agent arr s a b = System arr s (Mono a b)

-- | Opaque effectful ends: commit an @a@, emit a @b@.
--
-- Common log case: @Shard m [Post] [Post]@.  Pipeline speaks a stream on
-- commit and emit.  Keyboard one-shot:
--
-- @
-- prefixIn (:[])  -- Post -> [Post] on the conjoint
-- @
--
-- Emit is an onslaught of posts (empty = quiet \/ done for that poll).
type Shard m a b = Ends (Kleisli m) a b

-- | Same ends shape as 'Shard' — dual seat on the log (journal 013).
type LogEnds m a b = Shard m a b

-- | Build a 'Shard' from monadic commit and emit actions.
shard :: (Monad m) => (a -> m ()) -> m a -> Shard m a a
shard = endsK

-- | Build log ends (same as 'shard'; dual seat).
logEnds :: (Monad m) => (a -> m ()) -> m a -> LogEnds m a a
logEnds = endsK

-- | Born empty, conses each received input onto its history.
--
-- >>> iterateSystem (tape length) [] [1,2,3 :: Int]
-- [1,2,3]
tape :: ([i] -> o) -> Agent (->) [i] i o
tape f = System $ \(hist, d) -> (monoDir d : hist, (f hist, ()))

-- | Like 'tape', but also conses the agent's own output onto its history.
--
-- This is the internal-monologue construction: an agent's outputs are on the
-- same log as its percepts, visible to its own future turns.
selfrec :: ([i] -> i) -> Agent (->) [i] i i
selfrec f = System $ \(hist, d) ->
  let i = monoDir d
      h' = i : hist
   in (f h' : h', (f hist, ()))

-- | Addressed stream of unread posts for one agent.
--
-- The 'Inbox' owns a list of subscribed names and the unread stream.  Only
-- posts whose 'to' list intersects the subscription list are peeled by
-- 'unconsInbox'.  The common case is a singleton subscription @[agentName]@;
-- multi-cast wires list several names.
newtype Inbox f = Inbox {unInbox :: ([Name], f)}
  deriving (Show, Eq)

-- | Primary owner of the inbox (head of the subscription list).
inboxWho :: Inbox f -> Name
inboxWho = fromMaybe empty . listToMaybe . fst . unInbox

-- | Full subscription list for the inbox.
inboxSubs :: Inbox f -> [Name]
inboxSubs = fst . unInbox

-- | Empty inbox for the subscribed agent(s).
emptyInbox :: forall a f. (Uncons f (Post a)) => [Name] -> Inbox f
emptyInbox subs = Inbox (subs, nil @f @(Post a))

-- | Append a post to the right of the inbox.
appendInbox :: (Snoc f (Post a)) => Post a -> Inbox f -> Inbox f
appendInbox p (Inbox (subs, f)) = Inbox (subs, snoc f p)

-- | Lightweight delivery predicate.
--
-- A post delivers when any of the subscribed names appears in the post's 'to'
-- list.  Multi-cast is direct: a post addressed to several names reaches each
-- subscriber.  A post with @to = ["all"]@ broadcasts to every subscriber;
-- @to = []@ and @to = [""]@ deliver to no one (discard).  This predicate is a
-- small stepping stone toward a relational copy/discard delivery model
-- ('FinRel'); the full wiring is future work.
deliversTo :: Post a -> [Name] -> Bool
deliversTo p subs =
  case to p of
    [] -> False
    [t] | t == empty -> False
    ts -> ("all" :: Text) `elem` ts || any (`elem` ts) subs

-- | Peel the oldest addressed post from the inbox, returning the rest.
--
-- Non-matching posts are skipped and discarded.  An empty or exhausted inbox
-- returns 'That' with an empty inbox.
unconsInbox :: forall a f. (Uncons f (Post a)) => Inbox f -> These (Post a) (Inbox f)
unconsInbox (Inbox (subs, f)) = go f
  where
    go stream = case uncons stream of
      That rest -> That (Inbox (subs, rest))
      This p
        | deliversTo p subs -> This p
        | otherwise -> That (emptyInbox @a subs)
      These p rest
        | deliversTo p subs -> These p (Inbox (subs, rest))
        | otherwise -> go rest

-- | State for a pure agent in delivery: free carrier plus an addressed inbox.
data AgentState s f = AgentState
  { asCarrier :: s,
    asInbox :: Inbox f
  }
  deriving (Show, Eq)

-- | A node in the meeting's derivation tree.
--
-- 'dChildren' is kept flat (empty) in this pass.  Building the causal child
-- tree from routed outputs is future work.
data Derivation a = Derivation
  { dAgent :: Name,
    dInput :: Post a,
    dOutputs :: [Post a],
    dChildren :: [Derivation a]
  }
  deriving (Show, Eq)

-- | Empty carrier and empty inbox for the named agent.
emptyAgentState :: forall a s f. (Snoc s (Post a), Uncons f (Post a)) => [Name] -> AgentState s f
emptyAgentState subs = AgentState (snocNil @s @(Post a)) (emptyInbox @a subs)

-- | Seed an inbox with all posts addressed to any subscription from the log,
-- oldest first.
seedInbox :: forall a f. (Snoc f (Post a), Uncons f (Post a)) => [Name] -> Log f -> Inbox f
seedInbox subs lg = foldl' (flip appendInbox) (emptyInbox @a subs) (watch @a subs lg)

-- | Empty carrier and an inbox seeded from the log for the subscribed agent(s).
seedAgentState :: forall a s f. (Snoc s (Post a), Snoc f (Post a), Uncons f (Post a)) => [Name] -> Log f -> AgentState s f
seedAgentState subs lg = AgentState (snocNil @s @(Post a)) (seedInbox @a subs lg)

-- | Empty log.
emptyLog :: forall a f. (Cons f (Post a)) => Log f
emptyLog = consNil @f @(Post a)

-- | Read end of the log: all posts matching any subscription, oldest first.
--
-- Traversal is newest-to-oldest; matching posts are prepended, so the
-- accumulator is already oldest-first.
watch :: forall a f. (Uncons f (Post a)) => [Name] -> Log f -> [Post a]
watch subs t = go t []
  where
    go stream acc =
      case uncons stream of
        That _ -> acc
        This p -> if deliversTo p subs then p : acc else acc
        These p rest -> go rest (if deliversTo p subs then p : acc else acc)

-- | Write end of the log: commit a post.
post :: (Cons f (Post a)) => Post a -> Log f -> Log f
post = cons

-- | Per-agent session assembly: the bodies an agent actually sees.
session :: (Uncons f (Post a)) => [Name] -> Log f -> [a]
session subs = map body . watch subs

-- | One delivery round: peel one addressed post, step the machine, 'post' each output.
--
-- The 'AgentState' carries the free carrier @s@ and an addressed inbox.  Only
-- one post is consumed per call; repeated calls drain the inbox.  Outputs are
-- committed newest-first via 'post'.  When a post is processed, the returned
-- 'Derivation' records the agent name, the input post, and the emitted outputs.
turn ::
  forall a s f.
  (Cons f (Post a), Uncons f (Post a)) =>
  Agent (->) s (Post a) [Post a] ->
  AgentState s f ->
  Log f ->
  (AgentState s f, Log f, Maybe (Derivation a))
turn sys st log0 =
  let who = inboxWho (asInbox st)
      subs = inboxSubs (asInbox st)
   in case unconsInbox @a (asInbox st) of
        That _ -> (st, log0, Nothing)
        This p ->
          let (os, seen') = run1 sys (asCarrier st) p
           in (AgentState seen' (emptyInbox @a subs), foldl' (flip post) log0 os, Just (Derivation who p os []))
        These p rest ->
          let (os, seen') = run1 sys (asCarrier st) p
           in (AgentState seen' rest, foldl' (flip post) log0 os, Just (Derivation who p os []))

-- | Whether the agent's inbox has an addressed post waiting.
hasPending :: forall a s f. (Uncons f (Post a)) => AgentState s f -> Bool
hasPending st = case unconsInbox @a (asInbox st) of That _ -> False; _ -> True

-- | Stream length via 'Uncons'.
streamLength :: forall f a. (Uncons f a) => f -> Int
streamLength = go 0
  where
    go :: Int -> f -> Int
    go n stream =
      case uncons @f @a stream of
        That _ -> n
        This _ -> n + 1
        These _ rest -> go (n + 1) rest

-- | Take the first @n@ tokens from a stream, returning them as a list in
-- reverse order (oldest-first when the stream itself is newest-first).
takeStream :: forall f a. (Uncons f a) => Int -> f -> [a]
takeStream n s = go n s []
  where
    go :: Int -> f -> [a] -> [a]
    go 0 _ acc = acc
    go n' stream acc =
      case uncons @f @a stream of
        That _ -> acc
        This x -> x : acc
        These x rest -> go (n' - 1) rest (x : acc)

-- | Round-robin turn-loop until no agent has pending deliveries (quiescence).
--
-- Roster order is the schedule.  Each pass runs 'turn' for every agent that
-- still has pending work at its slot.  Passes repeat until a pass starts with
-- nobody pending.  Carriers start empty for every name.
loop ::
  forall a s f.
  (Snoc s (Post a), Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, Agent (->) s (Post a) [Post a])] ->
  Log f ->
  ([(Name, AgentState s f)], Log f, [Derivation a])
loop roster log0 = loopWith roster [(n, seedAgentState @a @s @f [n] log0) | (n, _) <- roster] log0

-- | Resumable 'loop': supply the initial states and inboxes.
--
-- Implemented as an 'Either' trace over the roster: each pass is one
-- iteration of the feedback channel, quiescence returns a 'Right' result.
loopWith ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, Agent (->) s (Post a) [Post a])] ->
  [(Name, AgentState s f)] ->
  Log f ->
  ([(Name, AgentState s f)], Log f, [Derivation a])
loopWith roster states0 log0 = trace body ()
  where
    bundle0 = (states0, log0, []) :: ([(Name, AgentState s f)], Log f, [Derivation a])
    body (Right ()) =
      if any (hasPending @a . snd) states0
        then Left bundle0
        else Right bundle0
    body (Left bundle) =
      let bundle' = meetingPass roster bundle
       in if any (hasPending @a . snd) (fst3 bundle')
            then Left bundle'
            else Right bundle'
    fst3 (x, _, _) = x

-- | The same meeting as a 'Loop' value: 'Knot' body over the 'Either'
-- tensor, quiescence returned as a 'Right' payload.
meetingLoop ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, Agent (->) s (Post a) [Post a])] ->
  Loop Either (->) ([(Name, AgentState s f)], Log f, [Derivation a]) ([(Name, AgentState s f)], Log f, [Derivation a])
meetingLoop roster = Knot body
  where
    body (Right bundle@(states, _, _)) =
      if any (hasPending @a . snd) states
        then Left bundle
        else Right bundle
    body (Left bundle) =
      let bundle'@(states', _, _) = meetingPass roster bundle
       in if any (hasPending @a . snd) states'
            then Left bundle'
            else Right bundle'

-- | One roster pass: schedule every agent that has pending work.
meetingPass ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, Agent (->) s (Post a) [Post a])] ->
  ([(Name, AgentState s f)], Log f, [Derivation a]) ->
  ([(Name, AgentState s f)], Log f, [Derivation a])
meetingPass roster (states, lg, derivs) = foldl' step (states, lg, derivs) roster
  where
    step (st, l, ds) (name, agent) =
      case lookup name st of
        Nothing -> (st, l, ds)
        Just sti
          | hasPending @a sti ->
              let (st', l', md) = turn agent sti l
                  newCount = streamLength @f @(Post a) l' - streamLength @f @(Post a) l
                  newPosts = takeStream @f @(Post a) newCount l'
                  st'' = foldl' routePost (updateState name st' st) newPosts
                  ds' = maybe ds (\d -> ds ++ [d]) md
               in (st'', l', ds')
          | otherwise -> (st, l, ds)

    updateState name st' = map (\(n, s) -> if n == name then (n, st') else (n, s))

    routePost states' p =
      map
        ( \(n, st) ->
            if deliversTo p [n]
              then (n, st {asInbox = appendInbox p (asInbox st)})
              else (n, st)
        )
        states'

-- | Transitive unfolding of a meeting.
--
-- Each element is one state of the round-robin schedule.  Divergence becomes
-- observable (the list is infinite) and 'loop' is simply the last quiescent
-- element.  The third component collects one 'Derivation' for every post that
-- was processed by 'turn' across the schedule.
loops ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, Agent (->) s (Post a) [Post a])] ->
  [(Name, AgentState s f)] ->
  Log f ->
  [([(Name, AgentState s f)], Log f, [Derivation a])]
loops roster states0 log0 = (states0, log0, []) : go states0 log0 []
  where
    go :: [(Name, AgentState s f)] -> Log f -> [Derivation a] -> [([(Name, AgentState s f)], Log f, [Derivation a])]
    go states lg derivs
      | not (any (hasPending @a . snd) states) = []
      | otherwise =
          let (states', lg', derivs') = foldl' step (states, lg, derivs) roster
           in (states', lg', derivs') : go states' lg' derivs'

    step :: ([(Name, AgentState s f)], Log f, [Derivation a]) -> (Name, Agent (->) s (Post a) [Post a]) -> ([(Name, AgentState s f)], Log f, [Derivation a])
    step (states, lg, derivs) (name, agent) =
      case lookup name states of
        Nothing -> (states, lg, derivs)
        Just st
          | hasPending @a st ->
              let (st', lg', md) = turn agent st lg
                  newCount = streamLength @f @(Post a) lg' - streamLength @f @(Post a) lg
                  newPosts = takeStream @f @(Post a) newCount lg'
                  states'' = foldl' routePost (updateState name st' states) newPosts
                  derivs' = maybe derivs (\d -> derivs ++ [d]) md
               in (states'', lg', derivs')
          | otherwise -> (states, lg, derivs)

    updateState :: Name -> AgentState s f -> [(Name, AgentState s f)] -> [(Name, AgentState s f)]
    updateState name st' = map (\(n, s) -> if n == name then (n, st') else (n, s))

    routePost :: [(Name, AgentState s f)] -> Post a -> [(Name, AgentState s f)]
    routePost states p =
      map
        ( \(n, st) ->
            if deliversTo p [n]
              then (n, st {asInbox = appendInbox p (asInbox st)})
              else (n, st)
        )
        states

-- | Resumable 'loop' with a heterogeneous roster: each agent supplies its own
-- initial carrier, while inboxes are still seeded from the shared log.
loopHetero ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, s, Agent (->) s (Post a) [Post a])] ->
  Log f ->
  ([(Name, AgentState s f)], Log f, [Derivation a])
loopHetero roster log0 =
  loopWith (map (\(n, _, a') -> (n, a')) roster) (map (\(n, s, _) -> (n, AgentState s (seedInbox @a [n] log0))) roster) log0

-- | Run a monomial system for one step.
--
-- Consume @i@, then extract the output from the successor state (Process /
-- 'iterateSystem' timing).
run1 :: Agent (->) s i o -> s -> i -> (o, s)
run1 sys s i =
  let s' = snd (runSystem sys s) i
      (o, _) = runSystem sys s'
   in (o, s')

-- | Lift a pure agent into the 'Kleisli' arrow of any functor.
--
-- This is the change of base from @(->)@ to @Kleisli m@ on the agent itself:
-- the same Moore coalgebra, but each step now lives in @m@.
agentM :: (Applicative m) => Agent (->) s a b -> Agent (Kleisli m) s a b
agentM (System f) = System (Kleisli (pure . f))

-- | Run one step of a monadic agent.
runAgentM :: (Monad m) => Agent (Kleisli m) s a b -> s -> a -> m (b, s)
runAgentM (System (Kleisli f)) s a =
  f (s, monoIn a) >>= \(s', (b, ())) -> pure (b, s')

-- | STM agent: state is handled transparently inside an STM transaction.
type AgentS s a = Agent (Kleisli STM) s a [a]

-- | IO agent: the STM boundary has been crossed; state is no longer
-- transparently handled.
type AgentX s a = Agent (Kleisli IO) s a [a]

-- | Cross from the transparent STM world into the IO boundary.
agentX :: AgentS s a -> AgentX s a
agentX (System (Kleisli f)) = System (Kleisli (\(s, d) -> atomically (f (s, d))))

-- | Seat-level product / await in STM.
awaitS :: AgentS s1 a -> AgentS s2 a -> AgentS (s1, s2) a
awaitS (System (Kleisli f1)) (System (Kleisli f2)) =
  System $ Kleisli $ \((s1, s2), d) -> do
    (s1', (o1, ())) <- f1 (s1, d)
    (s2', (o2, ())) <- f2 (s2, d)
    pure ((s1', s2'), (o1 <> o2, ()))

-- | Seat-level coproduct / race in STM.
raceS :: AgentS s1 a -> AgentS s2 a -> AgentS (s1, s2) a
raceS (System (Kleisli f1)) (System (Kleisli f2)) =
  System $ Kleisli $ \((s1, s2), d) -> do
    (s1', (o1, ())) <- f1 (s1, d)
    (s2', (o2, ())) <- f2 (s2, d)
    let o = if null o1 then o2 else o1
    pure ((s1', s2'), (o, ()))

-- | Temporal race under IO: run both branches concurrently, return the first
-- branch to emit a non-empty output, and cancel the loser. If the first branch
-- to finish emits nothing, wait for the other branch. If both emit nothing, the
-- right branch's (empty) result is returned.
--
-- This is the honest Kleisli-IO refinement of 'raceS': the winner is whichever
-- step produces a mark first, not the left-biased deterministic rule.
raceIO :: AgentX s1 a -> AgentX s2 a -> AgentX (s1, s2) a
raceIO (System (Kleisli f1)) (System (Kleisli f2)) =
  System $ Kleisli $ \((s1, s2), d) ->
    raceFirst (f1 (s1, d)) (f2 (s2, d)) >>= \case
      Left (s1', outs) -> pure ((s1', s2), (outs, ()))
      Right (s2', outs) -> pure ((s1, s2'), (outs, ()))
  where
    raceFirst act1 act2 = do
      a1 <- async act1
      a2 <- async act2
      let finishLeft s1' outs = cancel a2 >> pure (Left (s1', outs))
          finishRight s2' outs = cancel a1 >> pure (Right (s2', outs))
      race (wait a1) (wait a2) >>= \case
        Left (s1', (outs1, ()))
          | not (null outs1) -> finishLeft s1' outs1
          | otherwise -> do
              (s2', (outs2, ())) <- wait a2
              finishRight s2' outs2
        Right (s2', (outs2, ()))
          | not (null outs2) -> finishRight s2' outs2
          | otherwise -> do
              (s1', (outs1, ())) <- wait a1
              finishLeft s1' outs1

-- | Run one step of an STM agent.
stepS :: AgentS s a -> s -> a -> STM (s, [a])
stepS (System (Kleisli f)) s i = do
  (s', (outs, ())) <- f (s, monoIn i)
  pure (s', outs)

-- | Fold an STM agent over a bundle of inputs within one transaction.
--
-- This is the bundle-at-a-time step: one frame consumes a whole @[a]@ and
-- produces the concatenated replies.  Factor of 'runAgentS' that stays in
-- 'STM' so it can sit inside a larger transaction (e.g. a self-loop frame).
stepsS :: AgentS s a -> s -> [a] -> STM (s, [a])
stepsS sys s0 ins = go s0 ins
  where
    go s [] = pure (s, [])
    go s (i : is) = do
      (s', outs) <- stepS sys s i
      (sFinal, rest) <- go s' is
      pure (sFinal, outs ++ rest)

-- | Run an STM agent over a list of inputs, crossing into IO at the boundary.
runAgentS :: AgentS s a -> s -> [a] -> IO ([a], s)
runAgentS sys s0 ins = (\(s, os) -> (os, s)) <$> atomically (stepsS sys s0 ins)

-- | Unit ends for lifting single-token reads/writes out of an 'Ends' value.
unitEndsSTM :: Ends (Kleisli STM) () ()
unitEndsSTM = endsK (const (pure ())) (pure ())

-- | Read one token from an STM end.
readEndSTM :: Ends (Kleisli STM) a a -> STM a
readEndSTM ends = runKleisli (emit (companion ends) (conjoint unitEndsSTM)) ()

-- | Write one token to an STM end.
writeEndSTM :: Ends (Kleisli STM) a a -> a -> STM ()
writeEndSTM ends a = runKleisli (commit (conjoint ends) (companion unitEndsSTM)) a

-- | Wire an STM agent between an inbox and an outbox, running until
-- quiescence.  Quiescence is detected via 'orElse': if the inbox is empty
-- (retry), the loop returns the current state.
agentLoopS :: AgentS s a -> s -> Ends (Kleisli STM) a a -> Ends (Kleisli STM) a a -> STM s
agentLoopS agent s0 inbox outbox = go s0
  where
    go s =
      ( do
          a <- readEndSTM inbox
          (s', outs) <- stepS agent s a
          traverse_ (writeEndSTM outbox) outs
          go s'
      )
        `orElse` pure s

-- | Self-loop: the agent reads from and writes to the same STM end.
selfLoopS :: AgentS s a -> s -> Ends (Kleisli STM) a a -> STM s
selfLoopS agent s0 ends = agentLoopS agent s0 ends ends

-- | One frame of the bundle self-loop, expressed in the Either-trace halt
-- alphabet: 'Left' = continue, 'Right' = quiesce and return this state.
selfLoopFrame ::
  AgentS s a ->
  Ends (Kleisli STM) [a] [a] ->
  Ends (Kleisli STM) [a] [a] ->
  Kleisli STM (Either s s) (Either s s)
selfLoopFrame agent inbox outbox = Kleisli $ \case
  Right s -> step s
  Left s -> step s
  where
    step s = do
      mIns <- (Just <$> readEndSTM inbox) `orElse` pure Nothing
      case mIns of
        Nothing -> pure (Right s)
        Just ins -> do
          (s', outs) <- stepsS agent s ins
          if null outs
            then pure (Right s')
            else do
              writeEndSTM outbox outs
              pure (Left s')

-- | Wire an STM agent between an inbox and an outbox, running until
-- quiescence, expressed as a 'Loop Either' value.
agentLoopL ::
  AgentS s a ->
  Ends (Kleisli STM) [a] [a] ->
  Ends (Kleisli STM) [a] [a] ->
  Loop Either (Kleisli STM) s s
agentLoopL agent inbox outbox = trace (Lift (selfLoopFrame agent inbox outbox))

-- | Self-loop as a 'Loop Either' citizen.
selfLoopL ::
  AgentS s a ->
  s ->
  Ends (Kleisli STM) [a] [a] ->
  STM s
selfLoopL agent s0 ends = runKleisli (run (agentLoopL agent ends ends)) s0

-- | Agent behaviour: a pure function from an input stream to an output stream.
--
-- Each input post is stepped through the agent; the per-step output lists are
-- concatenated into a single output stream.  This is the stream semantics of
-- the Moore coalgebra, independent of any effectful boundary.
type Beh a = [Post a] -> [Post a]

-- | Run an agent from an initial carrier to obtain its 'Beh'aviour.
beh :: Agent (->) s (Post a) [Post a] -> s -> Beh a
beh _sys _s0 [] = []
beh sys s0 (i : ins) =
  let (os, s') = run1 sys s0 i
   in os ++ beh sys s' ins

-- | Conditional agent: branch between two agents based on the current state.
--
-- This is a level-1 grammar fragment: the carrier can carry a mode, and the
-- agent dispatches to one of two Moore machines depending on that mode. The
-- predicate is evaluated on the carrier before the input is consumed, which
-- is the honest Moore shape: output is a function of state, and the chosen
-- branch's update function determines the next state.
branchAgent :: (s -> Bool) -> Agent (->) s a b -> Agent (->) s a b -> Agent (->) s a b
branchAgent cond (System left) (System right) =
  System $ \(state, d) ->
    if cond state then left (state, d) else right (state, d)

-- | Seat-level product / await: both agents run on the same input; states are
-- paired; emits are concatenated left-to-right.
awaitA ::
  Agent (->) s1 (Post a) [Post a] ->
  Agent (->) s2 (Post a) [Post a] ->
  Agent (->) (s1, s2) (Post a) [Post a]
awaitA sys1 sys2 = System $ \((s1, s2), d) ->
  let dir = monoDir d
      (o1, next1) = runSystem sys1 s1
      (o2, next2) = runSystem sys2 s2
   in ((next1 dir, next2 dir), (o1 <> o2, ()))

-- | Seat-level coproduct / race: both agents run on the same input; states are
-- paired; the left emit wins if non-empty, otherwise the right emit wins.
raceA ::
  Agent (->) s1 (Post a) [Post a] ->
  Agent (->) s2 (Post a) [Post a] ->
  Agent (->) (s1, s2) (Post a) [Post a]
raceA sys1 sys2 = System $ \((s1, s2), d) ->
  let dir = monoDir d
      (o1, next1) = runSystem sys1 s1
      (o2, next2) = runSystem sys2 s2
      o = if null o1 then o2 else o1
   in ((next1 dir, next2 dir), (o, ()))

-- ---------------------------------------------------------------------------
-- Agent as Shard — change of base into Kleisli Ends
-- ---------------------------------------------------------------------------

-- | State behind an 'agentShard': free carrier plus a pending emit queue.
--
-- Commit parses inputs into the carrier and enqueues one output list per
-- input (the Moore step).  Emit flushes the queue — empty means quiet.
data AgentSeat s a = AgentSeat
  { asState :: s,
    -- | Pending outputs, oldest first.
    asOutbox :: [Post a]
  }
  deriving (Show, Eq)

-- | Pure parse step: fold committed posts through the coalgebra.
feedAgent :: Agent (->) s (Post a) [Post a] -> [Post a] -> AgentSeat s a -> AgentSeat s a
feedAgent sys ins (AgentSeat s0 outs0) =
  let (outs1, s1) =
        foldl'
          ( \(outs, s) i ->
              let (os, s') = run1 sys s i
               in (outs ++ os, s')
          )
          ([], s0)
          ins
   in AgentSeat s1 (outs0 ++ outs1)

-- | Take the outbox; leave carrier unchanged.
flushOutbox :: AgentSeat s a -> ([Post a], AgentSeat s a)
flushOutbox (AgentSeat s outs) = (outs, AgentSeat s [])

-- | Reinterpret a pure 'Agent' as a list 'Shard'.
--
-- @
-- agentShard get put sys  ::  Shard m [Post] [Post]
-- @
--
-- is the change of base from @(->)@ (the Moore coalgebra) into
-- @Kleisli m@ ends: commit = parse inputs, emit = flush replies.  The
-- interior stays opaque at the 'Shard' boundary — only @[Post]@ in and out.
--
-- @get@ \/ @put@ hold the 'AgentSeat' (e.g. 'Data.IORef' in @IO@, or
-- @State@ in tests).  Example — reply agent over @State@:
--
-- @
-- let sys = tape (\\hist -> (peek hist) { from = "j", to = [from (peek hist)], body = "ack: " <> body (peek hist) })
--     sh  = agentShard get put sys  :: Shard (State (AgentSeat [Post])) [Post] [Post]
-- in  evalState (runKleisli (close (conjoint sh) (companion sh)) [humanPost]) (AgentSeat [] [])
-- @
agentShard ::
  (Monad m) =>
  m (AgentSeat s a) ->
  (AgentSeat s a -> m ()) ->
  Agent (->) s (Post a) [Post a] ->
  Shard m [Post a] [Post a]
agentShard getSeat putSeat sys =
  shard
    ( \ins -> do
        seat <- getSeat
        putSeat (feedAgent sys ins seat)
    )
    ( do
        seat <- getSeat
        let (outs, seat') = flushOutbox seat
        putSeat seat'
        pure outs
    )

-- | One closed turn of an agent-as-shard: commit @ins@, emit replies, new seat.
--
-- Pure form of @close@ on 'agentShard' without choosing a monad:
--
-- @runAgentShard sys seat ins = runState (close (agentShard get put sys) ins) seat@
runAgentShard :: Agent (->) s (Post a) [Post a] -> AgentSeat s a -> [Post a] -> ([Post a], AgentSeat s a)
runAgentShard sys seat ins =
  let seat1 = feedAgent sys ins seat
      (outs, seat2) = flushOutbox seat1
   in (outs, seat2)

-- ---------------------------------------------------------------------------
-- Token seat — stream coalgebra around a list Shard (parser dual)
-- ---------------------------------------------------------------------------

-- | Single-post ends: keyboard \/ one-out seat.
--
-- Obtained by buffering a list 'Shard' on both sides, or by a bare queue
-- ('openSTM' \/ 'openIO').
--
-- A /tool call/ from an agent is just a 'Post': the 'to' list names the
-- tool, 'body' carries the arguments. No extra type — emit that 'Post' on a
-- 'Port' (or post it on the log for the tool agent to 'watch').
type Port m a = Ends (Kleisli m) (Post a) (Post a)

-- 'Snoc' is re-exported from 'Circuit.Stream' (construction dual of 'Uncons').

-- | Snoc a 'Post' onto a post stream. Specialized alias for 'snoc'.
snocPost :: [Post a] -> Post a -> [Post a]
snocPost = snoc

-- | @Ends s f@: commit snocs a token; emit flushes the whole stream
-- (parser @takeRest@ — drain policy is "the stream", not a count).
--
-- @get@ \/ @put@ hold the stream buffer.
batchEnds ::
  forall f s m.
  (Monad m, Snoc f s) =>
  m f ->
  (f -> m ()) ->
  Shard m s f
batchEnds getBuf putBuf =
  endsK
    ( \x -> do
        xs <- getBuf
        putBuf (snoc xs x)
    )
    ( do
        xs <- getBuf
        putBuf (snocNil @f @s)
        pure xs
    )

-- | @Ends f s@: commit appends a stream; emit peels one token
-- (parser @next@ \/ 'uncons'). Empty stream is quiet — the buffer is left
-- empty and the returned token is 'undefined' because the polymorphic token
-- type has no empty value.  In practice the list 'Shard' layer ensures quiet
-- periods are represented by an empty stream, so this case should not be
-- reached.
--
-- @get@ \/ @put@ hold the stream buffer.
unbatchEnds ::
  forall f s m.
  (Monad m, Semigroup f, Uncons f s) =>
  m f ->
  (f -> m ()) ->
  Shard m f s
unbatchEnds getBuf putBuf =
  endsK
    ( \ys -> do
        xs <- getBuf
        putBuf (xs <> ys)
    )
    ( do
        xs <- getBuf
        case uncons xs of
          That _ -> do
            putBuf (nil @f @s)
            pure (undefined :: s)
          This x -> do
            putBuf (nil @f @s)
            pure x
          These x rest -> do
            putBuf rest
            pure x
    )

-- | Token seat around a list 'Shard': buffer on both ends via stream coalgebra.
--
-- @
-- portShard getIn putIn getOut putOut sh
--   = batchEnds getIn putIn >:> sh >:> unbatchEnds getOut putOut
-- @
--
-- Flush\/drain is not a separate policy knob — it /is/ build-stream ('snoc')
-- and peel-stream ('uncons'), the same syntax as parsers over @[s]@.
portShard ::
  (Monad m) =>
  m [Post a] ->
  ([Post a] -> m ()) ->
  m [Post a] ->
  ([Post a] -> m ()) ->
  Shard m [Post a] [Post a] ->
  Port m a
portShard getIn putIn getOut putOut sh =
  batchEnds getIn putIn >:> sh >:> unbatchEnds getOut putOut

-- ---------------------------------------------------------------------------
-- Shard combinators
-- ---------------------------------------------------------------------------

-- | Adapt a shard on the commit side (contravariant).
--
-- Transform the input before it is committed.  One common use is
-- session assembly: @prefixShard session@ changes the payload that the
-- shard posts.
prefixShard :: (Monad m) => (a' -> a) -> Shard m a b -> Shard m a' b
prefixShard f = lmapEnds (Kleisli $ pure . f)

-- | Adapt a shard on the emit side (covariant).
--
-- Transform the output after it is emitted.  One common use is a
-- transport envelope: @suffixShard (map addHeader)@ decorates every
-- emitted post.
suffixShard :: (Monad m) => (b -> b') -> Shard m a b -> Shard m a b'
suffixShard g = rmapEnds (Kleisli $ pure . g)

-- | Adapt both sides of a shard at once.
--
-- @codecShard f g = prefixShard f . suffixShard g@.
codecShard :: (Monad m) => (a' -> a) -> (b -> b') -> Shard m a b -> Shard m a' b'
codecShard f g = dimapEnds (Kleisli $ pure . f) (Kleisli $ pure . g)

-- | Sequential composition of shards.
--
-- The output of the first shard feeds the input of the second.  This is
-- the same shape as connecting two effectful agents in series.
composeShard :: (Monad m) => Shard m a b -> Shard m b c -> Shard m a c
composeShard = composeEnds
