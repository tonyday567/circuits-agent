{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Moore agents on a shared, addressed log; opaque shards for effects.
--
-- Pure agent shape:
--
-- @
-- type Agent arr s a b = Moore (,) arr s (Mono a b)
-- @
--
-- Free carrier @s@ is required by the pretense (tape vs summary).  The common
-- log case is @Agent (->) [Post] Post [Post]@ — state is the received stream.
-- That carrier is a parse of the tape: each committed @Post@ is one token.
--
-- Effectful boundary (preferred pin):
--
-- @
-- type Shard m a b = Ends (K m) a b
-- @
--
-- Symmetric in the common log case: commit a list of posts, emit a list of
-- posts.  One-post reality (hit enter) is not another type — lift with @(:[])@
-- on the commit side (@prefixIn@).  'LogEnds' is the same shape (dual seat on
-- the log).  Opacity is commit\/emit only; no interior.
--
-- Change of base (circuits-parser sense): 'agentShard' reinterprets a pure
-- 'Agent' at @K m@ ends — same Moore citizen, effectful interface.
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
    indexToIdMap,
    branches,
    branchesByIndex,
    cone,
    coneByIndex,
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

    -- * Agent as Shard (change of base into K)
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
    turnAs,
    hasPending,
    loop,
    loopSubs,
    loopWith,
    loopWithSubs,
    loops,
    loopsSubs,
    loopHetero,
    loopHeteroSubs,
    meetingLoop,
    meetingLoopSubs,
    seedAgentState,
    RosterEntry,

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
    Poles (..),
    close,
    polesK,
    prefixIn,
    Queue (..),
    ChannelPolicy (..),
    openChannel,
    openChannelSTM,
    openLinearChannel,
    openLinearChannelSTM,
    HaltChannel (..),
    IsLinear,
    openHaltChannel,
    writeHaltChannel,
    readHaltChannel,
    openSTM,
    openIO,
    pipeEnds,

    -- * Shard combinators
    prefixShard,
    suffixShard,
    codecShard,
    composeShard,
    (>:>),
  )
where

import Circuit hiding (eval, race, (.))
import Circuit.Agent.Ends (ChannelPolicy (..), HaltChannel (..), IsLinear, Queue (..), openChannel, openChannelSTM, openHaltChannel, openIO, openLinearChannel, openLinearChannelSTM, openSTM, pipeEnds, readHaltChannel, writeHaltChannel)
import Circuit.Category (K (..))
import Circuit.Moore (Moore (..), fromEvalMoore, monoDir, monoIn, moore, mooreMorphism, runMooreMono)
import Circuit.Moore qualified as Moore
import Circuit.Poles (compose, imap, iomap, omap)
import Circuit.Poly (Eval (..), Mono)
import Circuit.Process (after)
import Circuit.Syntax (eval)
import Circuit.Trace (Trace, base)
import Circuit.Traced (yank)
import Control.Concurrent (threadDelay)
import Control.Concurrent.Async (async, cancel, race, wait)
import Control.Concurrent.STM (STM, atomically, orElse)
import Data.Foldable (traverse_)
import Data.List (find, foldl', genericIndex, genericTake, nub, sort)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Text (Text, empty)
import Numeric.Natural (Natural)
import "circuits" Circuit.Stream (Cons (..), Snoc (..), These (..), Uncons (..))

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Circuit.Agent
-- >>> import Circuit.Moore (mooreAsProcess)
-- >>> import Circuit.Process (scan)

-- | Agent name on the shared log.
type Name = Text

-- | Absolute post identity.  In the stamped log this is the line id assigned
-- by the single writer.  In pure meeting logs it is the position in the
-- oldest-first log, but 'branches' and 'cone' resolve by the id itself, not by
-- position in the passed-in list.  Use 'indexToIdMap' to assign ids [0..] from
-- a chronological list.
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
mkPost f t = Post f t []

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

-- | Assign positional ids @[0..]@ to a chronological list of posts.  This is
-- the convenience bridge from list-shaped logs to the id-resolved
-- 'branches'/'cone' API.
indexToIdMap :: [Post a] -> Map PostId (Post a)
indexToIdMap = Map.fromList . zip [0 ..]

-- | The next id after the largest key in the map, or @0@ if empty.
nextId :: Map PostId (Post a) -> PostId
nextId m = if Map.null m then 0 else fst (Map.findMax m) + 1

-- | The label-branches from a post to its conversation roots, resolved by
-- exact 'PostId'.  The current post is not in the map; its id is inferred as
-- the id after the largest key in the prior map.  Only thread edges strictly
-- less than the current id are resolved (ancestors must be prior posts).  A
-- dangling or future id is silently ignored.  A root post has one trivial
-- branch; every parent edge contributes its own path.  Branches of replies
-- are pure cons:
--
-- > branches (indexToIdMap prior) (replyTo who i p b)
--     == map (who :) (branches (Map.filterWithKey (\k _ -> k < i) (indexToIdMap prior)) p)
--
-- >>> let p1 = mkPost "tony" ["grok"] "hi" :: Post String; p2 = mkPost "grok" ["tony"] "hello"; r = replyTo "kimi" 1 p2 "a" in branchesByIndex [p1, p2] r == map ("kimi" :) (branchesByIndex [p1, p2] p2)
-- True
--
-- >>> let p1 = mkPost "tony" ["grok"] "hi" :: Post String; p2 = mkPost "grok" ["tony"] "hello"; r1 = replyTo "kimi" 1 p2 "a"; r2 = replyTo "tony" 2 r1 "b" in branchesByIndex [p1, p2, r1] r2
-- [["tony","kimi","grok"]]
branches :: Map PostId (Post a) -> Post a -> [[Name]]
branches priorMap = go (nextId priorMap)
  where
    go selfId p =
      case thread p of
        [] -> [[from p]]
        is -> concatMap (branchStep selfId p) is

    branchStep selfId p i =
      if i >= selfId
        then []
        else case Map.lookup i priorMap of
          Nothing -> []
          Just q -> map (from p :) (go i q)

-- | Convenience wrapper: resolve branches from a chronological list, assigning
-- ids @[0..]@.
branchesByIndex :: [Post a] -> Post a -> [[Name]]
branchesByIndex prior = branches (indexToIdMap prior)

-- | The ancestry cone: every name appearing on any branch from a post to
-- its roots, as a normalised set — the "who contributed to this" query,
-- free with the log.  Includes the post's own sender.
--
-- Cone-union law:
--
-- > cone (indexToIdMap prior) (synthesis who aud is b)
--     == sortNub (who : concatMap (cone (Map.filterWithKey (\k _ -> k < i) (indexToIdMap prior)) . (priorMap Map.!)) is)
--
-- >>> let p1 = mkPost "tony" ["grok"] "hi" :: Post String; p2 = mkPost "grok" ["tony"] "hello"; r1 = replyTo "kimi" 1 p2 "a"; prior = [p2, p1, r1] in coneByIndex prior (synthesis "sum" [] [2, 0] "Σ") == sortNub ("sum" : concatMap (coneByIndex prior) [r1, p2])
-- True
--
-- >>> let p1 = mkPost "tony" ["grok"] "hi" :: Post String; p2 = mkPost "grok" ["tony"] "hello"; r1 = replyTo "kimi" 1 p2 "a"; prior = [p2, p1, r1] in coneByIndex prior (synthesis "sum" [] [2, 0] "Σ")
-- ["grok","kimi","sum","tony"]
cone :: Map PostId (Post a) -> Post a -> [Name]
cone priorMap p = sortNub (concat (branches priorMap p))

-- | Convenience wrapper: resolve cone from a chronological list, assigning ids
-- @[0..]@.
coneByIndex :: [Post a] -> Post a -> [Name]
coneByIndex prior = cone (indexToIdMap prior)

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
-- @Moore (,) arr s (Mono a b) ≅ arr (s, a) (s, b)@ after collapsing unit
-- positions.  Common log case: @Agent (->) s (Post a) [Post a]@ (input = one post,
-- output = list of posts).  @Agent (K m) s a b@ is the monadic Moore
-- machine.
type Agent arr s a b = Moore (,) s arr (Mono a b)

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
type Shard m a b = Poles (K m) a b

-- | Same ends shape as 'Shard' — dual seat on the log (journal 013).
type LogEnds m a b = Shard m a b

-- | Build a 'Shard' from monadic commit and emit actions.
shard :: (Monad m) => (a -> m ()) -> m a -> Shard m a a
shard = polesK

-- | Build log ends (same as 'shard'; dual seat).
logEnds :: (Monad m) => (a -> m ()) -> m a -> LogEnds m a a
logEnds = polesK

-- | Born empty, conses each received input onto its history.
--
-- >>> scan (mooreAsProcess (tape length) []) [1,2,3 :: Int]
-- [1,2,3]
tape :: ([i] -> o) -> Agent (->) [i] i o
tape f = moore $ \(hist, d) -> (monoDir d : hist, (f hist, ()))

-- | Like 'tape', but also conses the agent's own output onto its history.
--
-- This is the internal-monologue construction: an agent's outputs are on the
-- same log as its percepts, visible to its own future turns.
selfrec :: ([i] -> i) -> Agent (->) [i] i i
selfrec f = moore $ \(hist, d) ->
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
--
-- 'turnAs' lets the caller supply the agent identity used in the derivation;
-- this matters when an inbox has multiple subscriptions (card-addressing) and
-- the first subscription is not the agent's own name.
turnAs ::
  forall a s f.
  (Cons f (Post a), Uncons f (Post a)) =>
  -- | Agent identity recorded in the derivation.
  Name ->
  Agent (->) s (Post a) [Post a] ->
  AgentState s f ->
  Log f ->
  (AgentState s f, Log f, Maybe (Derivation a))
turnAs who sys st log0 =
  let subs = inboxSubs (asInbox st)
   in case unconsInbox @a (asInbox st) of
        That _ -> (st, log0, Nothing)
        This p ->
          let (os, seen') = run1 sys (asCarrier st) p
           in (AgentState seen' (emptyInbox @a subs), foldl' (flip post) log0 os, Just (Derivation who p os []))
        These p rest ->
          let (os, seen') = run1 sys (asCarrier st) p
           in (AgentState seen' rest, foldl' (flip post) log0 os, Just (Derivation who p os []))

-- | 'turn' with the agent identity taken from the inbox's first subscription.
--
-- For single-subscription inboxes this is the agent's own name; for
-- multi-subscription inboxes use 'turnAs'.
turn ::
  forall a s f.
  (Cons f (Post a), Uncons f (Post a)) =>
  Agent (->) s (Post a) [Post a] ->
  AgentState s f ->
  Log f ->
  (AgentState s f, Log f, Maybe (Derivation a))
turn sys st = turnAs (inboxWho (asInbox st)) sys st

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

-- | A roster entry with explicit subscriptions: agent name, subscription names,
-- and the agent itself.  The subscription list is the set of names whose posts
-- the agent's inbox should receive; the agent's own name need not be in it.
type RosterEntry s a = (Name, [Name], Agent (->) s (Post a) [Post a])

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
loop roster = loopSubs [(n, [n], a) | (n, a) <- roster]

-- | Multi-seat-card variant of 'loop': each agent carries its own subscription
-- list, so several agents can share a card name.
loopSubs ::
  forall a s f.
  (Snoc s (Post a), Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [RosterEntry s a] ->
  Log f ->
  ([(Name, AgentState s f)], Log f, [Derivation a])
loopSubs roster log0 = loopWithSubs roster [(n, seedAgentState @a @s @f subs log0) | (n, subs, _) <- roster] log0

-- | Resumable 'loop': supply the initial states and inboxes.
--
-- Implemented as an 'Either' trace over the roster: each pass is one
-- iteration of the feedback channel, quiescence returns a 'Right' result.
--
-- Backwards-compatible wrapper; for explicit subscriptions use 'loopWithSubs'.
loopWith ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, Agent (->) s (Post a) [Post a])] ->
  [(Name, AgentState s f)] ->
  Log f ->
  ([(Name, AgentState s f)], Log f, [Derivation a])
loopWith roster = loopWithSubs [(n, [n], a) | (n, a) <- roster]

-- | Multi-seat-card variant of 'loopWith'.
loopWithSubs ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [RosterEntry s a] ->
  [(Name, AgentState s f)] ->
  Log f ->
  ([(Name, AgentState s f)], Log f, [Derivation a])
loopWithSubs roster states0 log0 = yank body ()
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

-- | The same meeting as a 'Trace' value: 'yank' body over the 'Either'
-- tensor, quiescence returned as a 'Right' payload.
--
-- Backwards-compatible wrapper; for explicit subscriptions use 'meetingLoopSubs'.
meetingLoop ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, Agent (->) s (Post a) [Post a])] ->
  Trace Either (->) ([(Name, AgentState s f)], Log f, [Derivation a]) ([(Name, AgentState s f)], Log f, [Derivation a])
meetingLoop roster = meetingLoopSubs [(n, [n], a) | (n, a) <- roster]

-- | Multi-seat-card variant of 'meetingLoop'.
meetingLoopSubs ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [RosterEntry s a] ->
  Trace Either (->) ([(Name, AgentState s f)], Log f, [Derivation a]) ([(Name, AgentState s f)], Log f, [Derivation a])
meetingLoopSubs roster = yank (base body)
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
--
-- The roster carries explicit subscriptions; posts are routed to every agent
-- whose subscriptions intersect the post's 'to' list.
meetingPass ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [RosterEntry s a] ->
  ([(Name, AgentState s f)], Log f, [Derivation a]) ->
  ([(Name, AgentState s f)], Log f, [Derivation a])
meetingPass roster (states, lg, derivs) = foldl' meetingStep (states, lg, derivs) roster
  where
    subMap = Map.fromList [(n, subs) | (n, subs, _) <- roster]

    meetingStep (st, l, ds) (name, _subs, agent) =
      case lookup name st of
        Nothing -> (st, l, ds)
        Just sti
          | hasPending @a sti ->
              let (st', l', md) = turnAs name agent sti l
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
            if deliversTo p (Map.findWithDefault [n] n subMap)
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
--
-- Backwards-compatible wrapper; for explicit subscriptions use 'loopsSubs'.
loops ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, Agent (->) s (Post a) [Post a])] ->
  [(Name, AgentState s f)] ->
  Log f ->
  [([(Name, AgentState s f)], Log f, [Derivation a])]
loops roster = loopsSubs [(n, [n], a) | (n, a) <- roster]

-- | Multi-seat-card variant of 'loops'.
loopsSubs ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [RosterEntry s a] ->
  [(Name, AgentState s f)] ->
  Log f ->
  [([(Name, AgentState s f)], Log f, [Derivation a])]
loopsSubs roster states0 log0 = (states0, log0, []) : go states0 log0 []
  where
    subMap = Map.fromList [(n, subs) | (n, subs, _) <- roster]

    go :: [(Name, AgentState s f)] -> Log f -> [Derivation a] -> [([(Name, AgentState s f)], Log f, [Derivation a])]
    go states lg derivs
      | not (any (hasPending @a . snd) states) = []
      | otherwise =
          let (states', lg', derivs') = foldl' runStep (states, lg, derivs) roster
           in (states', lg', derivs') : go states' lg' derivs'

    runStep :: ([(Name, AgentState s f)], Log f, [Derivation a]) -> RosterEntry s a -> ([(Name, AgentState s f)], Log f, [Derivation a])
    runStep (states, lg, derivs) (name, _subs, agent) =
      case lookup name states of
        Nothing -> (states, lg, derivs)
        Just st
          | hasPending @a st ->
              let (st', lg', md) = turnAs name agent st lg
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
            if deliversTo p (Map.findWithDefault [n] n subMap)
              then (n, st {asInbox = appendInbox p (asInbox st)})
              else (n, st)
        )
        states

-- | Resumable 'loop' with a heterogeneous roster: each agent supplies its own
-- initial carrier, while inboxes are still seeded from the shared log.
--
-- Backwards-compatible wrapper; for explicit subscriptions use 'loopHeteroSubs'.
loopHetero ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, s, Agent (->) s (Post a) [Post a])] ->
  Log f ->
  ([(Name, AgentState s f)], Log f, [Derivation a])
loopHetero roster = loopHeteroSubs [(n, s, [n], a) | (n, s, a) <- roster]

-- | Multi-seat-card variant of 'loopHetero'.
loopHeteroSubs ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, s, [Name], Agent (->) s (Post a) [Post a])] ->
  Log f ->
  ([(Name, AgentState s f)], Log f, [Derivation a])
loopHeteroSubs roster log0 =
  loopWithSubs
    [(n, subs, a) | (n, _, subs, a) <- roster]
    [(n, AgentState s (seedInbox @a subs log0)) | (n, s, subs, _) <- roster]
    log0

-- | Run a monomial system for one step.
--
-- Consume @i@, then extract the output from the successor state (Process /
-- post-input timing).
run1 :: Agent (->) s i o -> s -> i -> (o, s)
run1 sys s i =
  let s' = snd (Moore.runMooreMono sys s) i
      (o, _) = Moore.runMooreMono sys s'
   in (o, s')

-- | Lift a pure agent into the 'K' arrow of any functor.
--
-- This is the change of base from @(->)@ to @K m@ on the agent itself:
-- the same Moore coalgebra, but each step now lives in @m@.
agentM :: (Applicative m) => Agent (->) s a b -> Agent (K m) s a b
agentM sys = moore (K (pure . mooreMorphism sys))

-- | Run one step of a monadic agent.
runAgentM :: (Monad m) => Agent (K m) s a b -> s -> a -> m (b, s)
runAgentM sys s a =
  runK (mooreMorphism sys) (s, monoIn a) >>= \(s', (b, ())) -> pure (b, s')

-- | STM agent: state is handled transparently inside an STM transaction.
type AgentS s a = Agent (K STM) s a [a]

-- | IO agent: the STM boundary has been crossed; state is no longer
-- transparently handled.
type AgentX s a = Agent (K IO) s a [a]

-- | Cross from the transparent STM world into the IO boundary.
agentX :: AgentS s a -> AgentX s a
agentX sys = moore (K (\(s, d) -> atomically (runK (mooreMorphism sys) (s, d))))

-- | Seat-level product / await in STM.
awaitS :: AgentS s1 a -> AgentS s2 a -> AgentS (s1, s2) a
awaitS sys1 sys2 =
  moore $ K $ \((s1, s2), d) -> do
    (s1', (o1, ())) <- runK (mooreMorphism sys1) (s1, d)
    (s2', (o2, ())) <- runK (mooreMorphism sys2) (s2, d)
    pure ((s1', s2'), (o1 <> o2, ()))

-- | Seat-level coproduct / race in STM.
raceS :: AgentS s1 a -> AgentS s2 a -> AgentS (s1, s2) a
raceS sys1 sys2 =
  moore $ K $ \((s1, s2), d) -> do
    (s1', (o1, ())) <- runK (mooreMorphism sys1) (s1, d)
    (s2', (o2, ())) <- runK (mooreMorphism sys2) (s2, d)
    let o = if null o1 then o2 else o1
    pure ((s1', s2'), (o, ()))

-- | Temporal race under IO: run both branches concurrently, return the first
-- branch to emit a non-empty output, and cancel the loser. If the first branch
-- to finish emits nothing, wait for the other branch. If both emit nothing, the
-- right branch's (empty) result is returned.
--
-- This is the honest K-IO refinement of 'raceS': the winner is whichever
-- step produces a mark first, not the left-biased deterministic rule.
raceIO :: AgentX s1 a -> AgentX s2 a -> AgentX (s1, s2) a
raceIO sys1 sys2 =
  moore $ K $ \((s1, s2), d) ->
    raceFirst (runK (mooreMorphism sys1) (s1, d)) (runK (mooreMorphism sys2) (s2, d)) >>= \case
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
stepS sys s i = do
  (s', (outs, ())) <- runK (mooreMorphism sys) (s, monoIn i)
  pure (s', outs)

-- | Fold an STM agent over a bundle of inputs within one transaction.
--
-- This is the bundle-at-a-time step: one frame consumes a whole @[a]@ and
-- produces the concatenated replies.  Factor of 'runAgentS' that stays in
-- 'STM' so it can sit inside a larger transaction (e.g. a self-loop frame).
stepsS :: AgentS s a -> s -> [a] -> STM (s, [a])
stepsS sys = go
  where
    go s [] = pure (s, [])
    go s (i : is) = do
      (s', outs) <- stepS sys s i
      (sFinal, rest) <- go s' is
      pure (sFinal, outs ++ rest)

-- | Run an STM agent over a list of inputs, crossing into IO at the boundary.
runAgentS :: AgentS s a -> s -> [a] -> IO ([a], s)
runAgentS sys s0 ins = (\(s, os) -> (os, s)) <$> atomically (stepsS sys s0 ins)

-- | Unit poles for lifting single-token reads/writes out of a 'Poles' value.
unitEndsSTM :: Poles (K STM) () ()
unitEndsSTM = polesK (const (pure ())) (pure ())

-- | Read one token from an STM pole.
readEndSTM :: Poles (K STM) a a -> STM a
readEndSTM ends = runK (emit (companion ends) (conjoint unitEndsSTM)) ()

-- | Write one token to an STM pole.
writeEndSTM :: Poles (K STM) a a -> a -> STM ()
writeEndSTM ends = runK (commit (conjoint ends) (companion unitEndsSTM))

-- | Wire an STM agent between an inbox and an outbox, running until
-- quiescence.  Quiescence is detected via 'orElse': if the inbox is empty
-- (retry), the loop returns the current state.
agentLoopS :: AgentS s a -> s -> Poles (K STM) a a -> Poles (K STM) a a -> STM s
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
selfLoopS :: AgentS s a -> s -> Poles (K STM) a a -> STM s
selfLoopS agent s0 ends = agentLoopS agent s0 ends ends

-- | One frame of the bundle self-loop, expressed in the Either-trace halt
-- alphabet: 'Left' = continue, 'Right' = quiesce and return this state.
selfLoopFrame ::
  AgentS s a ->
  Poles (K STM) [a] [a] ->
  Poles (K STM) [a] [a] ->
  K STM (Either s s) (Either s s)
selfLoopFrame agent inbox outbox = K $ \case
  Right s -> loopStep s
  Left s -> loopStep s
  where
    loopStep s = do
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
-- quiescence, expressed as a 'Trace Either' value.
agentLoopL ::
  AgentS s a ->
  Poles (K STM) [a] [a] ->
  Poles (K STM) [a] [a] ->
  Trace Either (K STM) s s
agentLoopL agent inbox outbox = yank (base (selfLoopFrame agent inbox outbox))

-- | Self-loop as a 'Trace Either' citizen.
selfLoopL ::
  AgentS s a ->
  s ->
  Poles (K STM) [a] [a] ->
  STM s
selfLoopL agent s0 ends = runK (eval (agentLoopL agent ends ends)) s0

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
branchAgent cond sys1 sys2 =
  moore $ \(state, d) ->
    if cond state then mooreMorphism sys1 (state, d) else mooreMorphism sys2 (state, d)

-- | Seat-level product / await: both agents run on the same input; states are
-- paired; emits are concatenated left-to-right.
awaitA ::
  Agent (->) s1 (Post a) [Post a] ->
  Agent (->) s2 (Post a) [Post a] ->
  Agent (->) (s1, s2) (Post a) [Post a]
awaitA sys1 sys2 = moore $ \((s1, s2), d) ->
  let (s1', (o1, ())) = mooreMorphism sys1 (s1, d)
      (s2', (o2, ())) = mooreMorphism sys2 (s2, d)
   in ((s1', s2'), (o1 <> o2, ()))

-- | Seat-level coproduct / race: both agents run on the same input; states are
-- paired; the left emit wins if non-empty, otherwise the right emit wins.
raceA ::
  Agent (->) s1 (Post a) [Post a] ->
  Agent (->) s2 (Post a) [Post a] ->
  Agent (->) (s1, s2) (Post a) [Post a]
raceA sys1 sys2 = moore $ \((s1, s2), d) ->
  let (s1', (o1, ())) = mooreMorphism sys1 (s1, d)
      (s2', (o2, ())) = mooreMorphism sys2 (s2, d)
      o = if null o1 then o2 else o1
   in ((s1', s2'), (o, ()))

-- ---------------------------------------------------------------------------
-- Agent as Shard — change of base into K Ends
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
-- @K m@ ends: commit = parse inputs, emit = flush replies.  The
-- interior stays opaque at the 'Shard' boundary — only @[Post]@ in and out.
--
-- @get@ \/ @put@ hold the 'AgentSeat' (e.g. 'Data.IORef' in @IO@, or
-- @State@ in tests).  Example — reply agent over @State@:
--
-- @
-- let sys = tape (\\hist -> (peek hist) { from = "j", to = [from (peek hist)], body = "ack: " <> body (peek hist) })
--     sh  = agentShard get put sys  :: Shard (State (AgentSeat [Post])) [Post] [Post]
-- in  evalState (runK (close (conjoint sh) (companion sh)) [humanPost]) (AgentSeat [] [])
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
type Port m a = Poles (K m) (Post a) (Post a)

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
  polesK
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
  polesK
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
  composeShard (composeShard (batchEnds getIn putIn) sh) (unbatchEnds getOut putOut)

-- ---------------------------------------------------------------------------
-- Shard combinators
-- ---------------------------------------------------------------------------

-- | Adapt a shard on the commit side (contravariant).
--
-- Transform the input before it is committed.  One common use is
-- session assembly: @prefixShard session@ changes the payload that the
-- shard posts.
prefixShard :: (Monad m) => (a' -> a) -> Shard m a b -> Shard m a' b
prefixShard f = imap (K $ pure . f)

-- | Adapt a shard on the emit side (covariant).
--
-- Transform the output after it is emitted.  One common use is a
-- transport envelope: @suffixShard (map addHeader)@ decorates every
-- emitted post.
suffixShard :: (Monad m) => (b -> b') -> Shard m a b -> Shard m a b'
suffixShard g = omap (K $ pure . g)

-- | Adapt both sides of a shard at once.
--
-- @codecShard f g = prefixShard f . suffixShard g@.
codecShard :: (Monad m) => (a' -> a) -> (b -> b') -> Shard m a b -> Shard m a' b'
codecShard f g = iomap (K $ pure . f) (K $ pure . g)

-- | Sequential composition of shards.
--
-- The output of the first shard feeds the input of the second.  This is
-- the same shape as connecting two effectful agents in series.
composeShard :: forall m a b c. (Monad m) => Shard m a b -> Shard m b c -> Shard m a c
composeShard = compose @(K m) @a @b @c @()
