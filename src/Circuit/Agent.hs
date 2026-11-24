{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}

-- | Body-shaped agents on a shared, addressed log.
--
-- Pure meeting body:
--
-- @
-- type PureAgent s a b = Body (,) (,) s s (->) a b
-- @
--
-- Free carrier @s@ is required by the pretense (tape vs summary).  The common
-- log case is @PureAgent [Post] Post [Post]@ — state is the received stream.
-- That carrier is a parse of the tape: each committed @Post@ is one token.
--
-- Effectful boundary (preferred pin):
--
-- @
-- type Agent s = Body (,) (,) (AgentChannel s) (AgentChannel s) (K IO) (Post Text) [Post Text]
-- @
--
-- Commit and emit are independent legs.  Several posts may be committed before
-- any output is emitted, and an emit may return zero, one, or many posts,
-- including a final batch beside 'Done'.  'runAgent' is the ordered
-- compatibility runner — birth from the first post, commit the rest, drain
-- emissions through 'Done'.
--
-- Symmetric in the common log case: commit a post, emit a list of posts.
-- One-post reality (hit enter) is not another type — lift with @(:[])@ on the
-- commit side.  Opacity is commit\/emit only; no interior.
--
-- Change of base (circuits-parser sense): 'agentPoles' reinterprets a pure
-- meeting body at @K m@ ends — same Moore citizen, effectful interface.
-- Direct seats (hermes session, muster-agent) skip the pure coalgebra and
-- inhabit 'Agent' only.
--
-- Token seat around an @Ends@ pair (parser dual): stream @f = [Post]@, token
-- @s = Post@.  'batchEnds' snocs tokens into a stream (build @f@); 'unbatchEnds'
-- peels with the same coalgebra as 'Uncons' on lists.  Compose with @'pipe'@:
--
-- @
-- batchEnds … `pipe` ends `pipe` unbatchEnds …
--   :: Poles () (K m) Post [Post] `pipe` Poles () (K m) [Post] [Post] `pipe` Poles () (K m) [Post] Post
--   :: Port m
-- @
--
-- Queue ends ('openSTM' \/'openIO') are the effectful token wire of the same
-- shape when you need a bare @Post\/@Post@ channel without buffering.
--
-- Design card: @coffee\/loom\/agent.md@.
module Circuit.Agent
  ( -- * Posts and the log
    Post,
    pattern Post,
    from,
    channel,
    to,
    thread,
    body,
    PostId,
    mkPost,
    mkChannelPost,
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

    -- * Effectful post agents
    Agent,
    AgentChannel (..),
    Lifecycle (..),
    ioAgent,
    drainAgent,
    runAgent,

    -- * Pure and effect-polymorphic meeting bodies
    PureAgent,
    AgentM,
    AgentState (..),
    emptyAgentState,
    tape,
    cellToAgent,
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

    -- * Buffered ends around a meeting body
    AgentSeat (..),
    feedAgent,
    flushOutbox,
    agentPoles,
    runAgentPoles,

    -- * Pure port turns
    PortSeat (..),
    runPort,

    -- * Token stream buffers
    Port,
    Snoc (..),
    snocPost,
    batchEnds,
    unbatchEnds,

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
    meetingLoop,
    meetingLoopSubs,
    seedAgentState,
    RosterEntry,

    -- * Derivations
    Derivation (..),

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

    -- * Container dial (Bag algebra)
    Bag (..),
    toBag,

    -- * Behaviour (stream semantics)
    Beh,
    beh,

    -- * Choice (level-1 grammar fragment)
    branchAgent,

    -- * Seat-level tensors (product / await, coproduct / race)
    awaitA,
    raceA,

    -- * Re-exports for end construction
    Poles (..),
    close,
    polesK,
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
  )
where

import Circuit.Agent.Ends (ChannelPolicy (..), HaltChannel (..), IsLinear, Queue (..), openChannel, openChannelSTM, openHaltChannel, openIO, openLinearChannel, openLinearChannelSTM, openSTM, pipeEnds, readHaltChannel, unitEndsSTM, writeHaltChannel)
import Circuit.Body (Body (Body), Poles (..), close, polesK)
import Circuit.Category (K (..))
import Circuit.Machine (Moore (Moore))
import Circuit.Post qualified as Core
import Circuit.Syntax (Syntax (Lift), eval)
import Circuit.Trace (FreeTrace)
import Circuit.Traced (trace)
import Control.Concurrent.Async (async, cancel, race, wait)
import Control.Concurrent.STM (STM, atomically, orElse)
import Control.Monad (foldM)
import Data.Foldable (traverse_)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Text (Text, empty)
import "circuits" Circuit.Stream (Cons (..), Snoc (..), These (..), Uncons (..))
import Prelude hiding (read)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Circuit.Agent
-- >>> import Circuit.Machine (MooreT (..), scan)

-- | Agent name on the shared log.
type Name = Text

-- | Absolute post identity.  In the stamped log this is the line id assigned
-- by the single writer.  In pure meeting logs it is the position in the
-- oldest-first log, but 'branches' and 'cone' resolve by the id itself, not by
-- position in the passed-in list.  Use 'indexToIdMap' to assign ids [0..] from
-- a chronological list.
type PostId = Core.PostId

-- | A single entry on the shared log, polymorphic in payload.
--
-- The structural post lives in 'Circuit.Post'; this alias specialises its
-- address type to 'Name' for the agent execution vocabulary.
type Post a = Core.Post Name a

pattern Post :: Name -> Maybe Name -> [Name] -> [PostId] -> a -> Post a
pattern Post {from, channel, to, thread, body} = Core.Post from channel to thread body

{-# COMPLETE Post #-}

-- | A fresh root post (no parents). No channel: address by the 'to' list.
mkPost :: Name -> [Name] -> a -> Post a
mkPost = Core.mkPost

-- | A fresh root post in a named channel. The channel is the address; the
-- 'to' list is the resolved membership at post time.
mkChannelPost :: Name -> Name -> [Name] -> a -> Post a
mkChannelPost = Core.mkChannelPost

-- | A reply: the audience is the parent's sender plus the rest of the
-- parent's audience (minus self); the sole thread edge cites the parent's
-- 'PostId'. The reply inherits the parent's channel: a reply lands in the
-- channel it answers.
replyTo :: Name -> PostId -> Post a -> b -> Post b
replyTo = Core.replyTo

-- | A synthesis: one descendant of several parents — the object-level
-- wire-merge dual to merging agents.  The ancestry cites every parent id as
-- a normalised set (sorted, duplicates discarded).  A synthesis is addressed
-- by its explicit audience and carries no channel: the constructor receives
-- the audience and the parent ids, never the parent posts, so there is no
-- channel to inherit.
synthesis :: Name -> [Name] -> [PostId] -> b -> Post b
synthesis = Core.synthesis

-- | Sorted, duplicate-free.  The normalised-set primitive of the thread
-- design: parent sets, audiences, and cones are all kept in this form.
sortNub :: (Ord a) => [a] -> [a]
sortNub = Core.sortNub

-- | Assign positional ids @[0..]@ to a chronological list of posts.  This is
-- the convenience bridge from list-shaped logs to the id-resolved
-- 'branches'/'cone' API.
indexToIdMap :: [Post a] -> Map PostId (Post a)
indexToIdMap = Core.indexToIdMap

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
branches = Core.branches

-- | Convenience wrapper: resolve branches from a chronological list, assigning
-- ids @[0..]@.
branchesByIndex :: [Post a] -> Post a -> [[Name]]
branchesByIndex = Core.branchesByIndex

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
cone = Core.cone

-- | Convenience wrapper: resolve cone from a chronological list, assigning ids
-- @[0..]@.
coneByIndex :: [Post a] -> Post a -> [Name]
coneByIndex = Core.coneByIndex

-- | The shared append-only log, newest first.
--
-- The log is a stream of 'Post's.  Common case: @Log [Post]@.  Generalizing to
-- any @f@ with 'Cons' and 'Uncons' lets the same delivery machinery run over
-- other stream representations while keeping the addressed read as a list.
type Log f = f

-- | A bag: finite multiset.  Order is forgotten; multiplicity is kept.
-- Used by the fleet's axioma oracles to compare output sets.
newtype Bag a = Bag (Map a Int)
  deriving (Eq, Show)

-- | Fold a list into a bag, forgetting order.
toBag :: (Ord a) => [a] -> Bag a
toBag = foldr insertBag emptyBag
  where
    insertBag x (Bag m) = Bag (Map.insertWith (+) x 1 m)
    emptyBag = Bag Map.empty

-- | Lifecycle reported by an effectful agent emission.
data Lifecycle = Continue | Done
  deriving (Eq, Show)

-- | The visible agent channel: client state and lifecycle in the same value.
data AgentChannel s = AgentChannel
  { agentState :: s,
    agentLifecycle :: Lifecycle
  }
  deriving (Eq, Show)

-- | An input-seeded effectful post agent. Emission is independent of commit:
-- it may return zero, one, or many posts, including a final batch beside
-- 'Done'. IO exceptions are the failure channel.
type Agent s = Body (,) (,) (AgentChannel s) (AgentChannel s) (K IO) (Post Text) [Post Text]

-- | A pure meeting body with the same commit/emit factorisation.
type PureAgent s a b = AgentM (->) s a b

-- | A meeting body polymorphic in its base arrow.
type AgentM arr s a b = Body (,) (,) s s arr a b

-- | Convert a Moore cell into the two-leg meeting body.
cellToAgent :: Moore (,) s (->) a b -> PureAgent s a b
cellToAgent (Moore j k o) = Body j k (\s -> (s, o s))

-- | Drain ordered emissions through the first 'Done'. The final emission is
-- always performed, even when the incoming channel already reports 'Done',
-- so final output cannot be lost.
drainAgent :: Agent s -> AgentChannel s -> IO (AgentChannel s, [Post Text])
drainAgent (Body _ _ emit') = go
  where
    go channel = do
      (channel', posts) <- runK emit' channel
      case agentLifecycle channel' of
        Done -> pure (channel', posts)
        Continue -> fmap (posts <>) <$> go channel'

-- | Compatibility runner: initialise from the first post, commit every later
-- post independently, then drain emissions through 'Done'. An empty input
-- batch has no birth event and therefore no output.
runAgent :: Agent s -> [Post Text] -> IO [Post Text]
runAgent _ [] = pure []
runAgent agent@(Body birth commit' _) (first : rest) = do
  born <- runK birth first
  committed <- foldM (\channel post_ -> runK commit' (channel, post_)) born rest
  snd <$> drainAgent agent committed

-- | A one-delivery agent from a batched IO action. The first emit returns
-- the action's posts beside 'Done'.
ioAgent :: ([Post Text] -> IO [Post Text]) -> Agent [Post Text]
ioAgent action =
  Body
    (K (\post_ -> pure (AgentChannel [post_] Continue)))
    (K (\(AgentChannel pending _, post_) -> pure (AgentChannel (pending <> [post_]) Continue)))
    ( K $ \(AgentChannel pending _) -> do
        posts <- action pending
        pure (AgentChannel [] Done, posts)
    )

-- | Born empty, conses each received input onto its history.
--
-- >>> scan (MooreT (tape length)) [1,2,3 :: Int]
-- [1,2,3]
tape :: ([i] -> o) -> Moore (,) [i] (->) i o
tape f = Moore (\i -> [i]) (\(hist, i) -> i : hist) f

-- | Like 'tape', but also conses the agent's own output onto its history.
--
-- This is the internal-monologue construction: an agent's outputs are on the
-- same log as its percepts, visible to its own future turns. The recorded
-- utterance is the emitted utterance — @f@ responds to the full history
-- including the current percept, and that response is both what the world
-- hears and what the monologue conses. Under 'run1' the pair stays honest:
-- output equals the head of the recorded history.
selfrec :: ([i] -> i) -> PureAgent [i] i i
selfrec f = Body (\i -> step ([], i)) step observe
  where
    step (hist, i) = let h' = i : hist in f h' : h'
    observe hist = (hist, case hist of r : _ -> r; [] -> error "selfrec: uninitialised channel")

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
-- A post delivers when its channel names one of the seat's subscriptions; a
-- post with no channel delivers when any of the subscribed names appears in
-- the post's 'to' list.  Multi-cast is direct: a post addressed to several
-- names reaches each subscriber.  There is no broadcast sentinel — a
-- broadcast is a channel whose resolved membership names every member, and
-- @to = []@ or @to = [""]@ delivers to no one (discard).  This predicate is a
-- small stepping stone toward a relational copy/discard delivery model
-- ('FinRel'); the full wiring is future work.
deliversTo :: Post a -> [Name] -> Bool
deliversTo = Core.deliversTo

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
  PureAgent s (Post a) [Post a] ->
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
  PureAgent s (Post a) [Post a] ->
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
type RosterEntry s a = (Name, [Name], PureAgent s (Post a) [Post a])

-- | Round-robin turn-loop until no agent has pending deliveries (quiescence).
--
-- Roster order is the schedule.  Each pass runs 'turn' for every agent that
-- still has pending work at its slot.  Passes repeat until a pass starts with
-- nobody pending.  Carriers start empty for every name.
loop ::
  forall a s f.
  (Snoc s (Post a), Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, PureAgent s (Post a) [Post a])] ->
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
  [(Name, PureAgent s (Post a) [Post a])] ->
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
loopWithSubs roster states0 log0 = trace body ()
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

-- | The same meeting as a 'FreeTrace' value: 'trace' body over the 'Either'
-- tensor, quiescence returned as a 'Right' payload.
--
-- Backwards-compatible wrapper; for explicit subscriptions use 'meetingLoopSubs'.
meetingLoop ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [(Name, PureAgent s (Post a) [Post a])] ->
  FreeTrace Either (->) ([(Name, AgentState s f)], Log f, [Derivation a]) ([(Name, AgentState s f)], Log f, [Derivation a])
meetingLoop roster = meetingLoopSubs [(n, [n], a) | (n, a) <- roster]

-- | Multi-seat-card variant of 'meetingLoop'.
meetingLoopSubs ::
  forall a s f.
  (Snoc f (Post a), Cons f (Post a), Uncons f (Post a)) =>
  [RosterEntry s a] ->
  FreeTrace Either (->) ([(Name, AgentState s f)], Log f, [Derivation a]) ([(Name, AgentState s f)], Log f, [Derivation a])
meetingLoopSubs roster = trace (Lift body)
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

-- | Run a monomial system for one step.
--
-- One coalgebra step: the coalgebra's own output, paired with its
-- successor state. Stepping twice here would report what the agent would
-- emit /next/ against a state that only took one turn — for a
-- self-recording agent, the monologue then remembers an utterance other
-- than the one the world heard.
run1 :: PureAgent s i o -> s -> i -> (o, s)
run1 (Body _ k e) s i =
  let (s', o) = e (k (s, i))
   in (o, s')

-- | Lift every leg of a pure meeting body into an applicative base.
agentM :: (Applicative m) => PureAgent s a b -> AgentM (K m) s a b
agentM (Body j k e) =
  Body
    (K (pure . j))
    (K (pure . k))
    (K (pure . e))

-- | Run one commit and its independent emit.
runAgentM :: (Monad m) => AgentM (K m) s a b -> s -> a -> m (b, s)
runAgentM (Body _ k e) s a = do
  committed <- runK k (s, a)
  (s', b) <- runK e committed
  pure (b, s')

-- | STM meeting body: state is handled transparently inside a transaction.
type AgentS s a = AgentM (K STM) s a [a]

-- | IO meeting body: the STM boundary has been crossed.
type AgentX s a = AgentM (K IO) s a [a]

-- | Cross from the transparent STM world into the IO boundary.
agentX :: AgentS s a -> AgentX s a
agentX (Body j k e) =
  Body
    (K (atomically . runK j))
    (K (atomically . runK k))
    (K (atomically . runK e))

-- | Seat-level product / await in STM.
awaitS :: AgentS s1 a -> AgentS s2 a -> AgentS (s1, s2) a
awaitS (Body j1 k1 e1) (Body j2 k2 e2) =
  Body
    (K (\a -> (,) <$> runK j1 a <*> runK j2 a))
    ( K $ \((s1, s2), a) -> do
        s1' <- runK k1 (s1, a)
        s2' <- runK k2 (s2, a)
        pure (s1', s2')
    )
    ( K $ \(s1, s2) -> do
        (s1', o1) <- runK e1 s1
        (s2', o2) <- runK e2 s2
        pure ((s1', s2'), o1 <> o2)
    )

-- | Seat-level coproduct / race in STM: the left non-empty emit wins.
raceS :: AgentS s1 a -> AgentS s2 a -> AgentS (s1, s2) a
raceS (Body j1 k1 e1) (Body j2 k2 e2) =
  Body
    (K (\a -> (,) <$> runK j1 a <*> runK j2 a))
    ( K $ \((s1, s2), a) -> do
        s1' <- runK k1 (s1, a)
        s2' <- runK k2 (s2, a)
        pure (s1', s2')
    )
    ( K $ \(s1, s2) -> do
        (s1', o1) <- runK e1 s1
        (s2', o2) <- runK e2 s2
        pure ((s1', s2'), if null o1 then o2 else o1)
    )

-- | Temporal race under IO: commits initialise both channels; the emit leg
-- returns the first non-empty output and cancels the losing observation.
raceIO :: AgentX s1 a -> AgentX s2 a -> AgentX (s1, s2) a
raceIO (Body j1 k1 e1) (Body j2 k2 e2) =
  Body
    (K (\a -> (,) <$> runK j1 a <*> runK j2 a))
    ( K $ \((s1, s2), a) -> do
        s1' <- runK k1 (s1, a)
        s2' <- runK k2 (s2, a)
        pure (s1', s2')
    )
    (K (\(s1, s2) -> raceFirst s1 s2 (runK e1 s1) (runK e2 s2)))
  where
    raceFirst s1 s2 act1 act2 = do
      a1 <- async act1
      a2 <- async act2
      let finishLeft (s1', outs) = cancel a2 >> pure ((s1', s2), outs)
          finishRight (s2', outs) = cancel a1 >> pure ((s1, s2'), outs)
      race (wait a1) (wait a2) >>= \case
        Left (s1', outs1)
          | not (null outs1) -> finishLeft (s1', outs1)
          | otherwise -> wait a2 >>= finishRight
        Right (s2', outs2)
          | not (null outs2) -> finishRight (s2', outs2)
          | otherwise -> wait a1 >>= finishLeft

-- | Run one step of an STM agent.
stepS :: AgentS s a -> s -> a -> STM (s, [a])
stepS sys s i = do
  (outs, s') <- runAgentM sys s i
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

-- | Read one token from an STM pole.
readEndSTM :: Poles () (K STM) a a -> STM a
readEndSTM ends = runK (close (Poles (commit unitEndsSTM) (commit unitEndsSTM) (emit ends))) ()

-- | Write one token to an STM pole.
writeEndSTM :: Poles () (K STM) a a -> a -> STM ()
writeEndSTM ends = runK (close (Poles (commit ends) (commit ends) (emit unitEndsSTM)))

-- | Wire an STM agent between an inbox and an outbox, running until
-- quiescence.  Quiescence is detected via 'orElse': if the inbox is empty
-- (retry), the loop returns the current state.
agentLoopS :: AgentS s a -> s -> Poles () (K STM) a a -> Poles () (K STM) a a -> STM s
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
selfLoopS :: AgentS s a -> s -> Poles () (K STM) a a -> STM s
selfLoopS agent s0 ends = agentLoopS agent s0 ends ends

-- | One frame of the bundle self-loop, expressed in the Either-trace halt
-- alphabet: 'Left' = continue, 'Right' = quiesce and return this state.
selfLoopFrame ::
  AgentS s a ->
  Poles () (K STM) [a] [a] ->
  Poles () (K STM) [a] [a] ->
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
-- quiescence, expressed as a 'FreeTrace Either' value.
agentLoopL ::
  AgentS s a ->
  Poles () (K STM) [a] [a] ->
  Poles () (K STM) [a] [a] ->
  FreeTrace Either (K STM) s s
agentLoopL agent inbox outbox = trace (Lift (selfLoopFrame agent inbox outbox))

-- | Self-loop as a 'FreeTrace Either' citizen.
selfLoopL ::
  AgentS s a ->
  s ->
  Poles () (K STM) [a] [a] ->
  STM s
selfLoopL agent s0 ends = runK (eval (agentLoopL agent ends ends)) s0

-- | Agent behaviour: a pure function from an input stream to an output stream.
--
-- Each input post is stepped through the agent; the per-step output lists are
-- concatenated into a single output stream.  This is the stream semantics of
-- the Moore coalgebra, independent of any effectful boundary.
type Beh a = [Post a] -> [Post a]

-- | Run an agent from an initial carrier to obtain its 'Beh'aviour.
beh :: PureAgent s (Post a) [Post a] -> s -> Beh a
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
branchAgent :: (s -> Bool) -> PureAgent s a b -> PureAgent s a b -> PureAgent s a b
branchAgent cond (Body i1 c1 e1) (Body _i2 c2 e2) =
  Body
    i1
    (\(state, a) -> if cond state then c1 (state, a) else c2 (state, a))
    (\state -> if cond state then e1 state else e2 state)

-- | Seat-level product / await: both agents run on the same input; states are
-- paired; emits are concatenated left-to-right.
awaitA ::
  PureAgent s1 (Post a) [Post a] ->
  PureAgent s2 (Post a) [Post a] ->
  PureAgent (s1, s2) (Post a) [Post a]
awaitA (Body i1 c1 e1) (Body i2 c2 e2) =
  Body
    (\a -> (i1 a, i2 a))
    (\((s1, s2), a) -> (c1 (s1, a), c2 (s2, a)))
    ( \(s1, s2) ->
        let (s1', o1) = e1 s1
            (s2', o2) = e2 s2
         in ((s1', s2'), o1 <> o2)
    )

-- | Seat-level coproduct / race: both agents run on the same input; states are
-- paired; the left emit wins if non-empty, otherwise the right emit wins.
raceA ::
  PureAgent s1 (Post a) [Post a] ->
  PureAgent s2 (Post a) [Post a] ->
  PureAgent (s1, s2) (Post a) [Post a]
raceA (Body i1 c1 e1) (Body i2 c2 e2) =
  Body
    (\a -> (i1 a, i2 a))
    (\((s1, s2), a) -> (c1 (s1, a), c2 (s2, a)))
    ( \(s1, s2) ->
        let (s1', o1) = e1 s1
            (s2', o2) = e2 s2
         in ((s1', s2'), if null o1 then o2 else o1)
    )

-- ---------------------------------------------------------------------------
-- Agent as Ends — change of base into K
-- ---------------------------------------------------------------------------

-- | State behind an 'agentPoles': free carrier plus a pending emit queue.
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
feedAgent :: PureAgent s (Post a) [Post a] -> [Post a] -> AgentSeat s a -> AgentSeat s a
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

-- | Reinterpret a pure meeting body as an @Ends@ pair.
--
-- @
-- agentPoles get put sys  ::  Poles () (K m) [Post] [Post]
-- @
--
-- is the change of base from @(->)@ (the Moore coalgebra) into
-- @K m@ ends: commit = parse inputs, emit = flush replies.  The
-- interior stays opaque at the @Ends@ boundary — only @[Post]@ in and out.
--
-- @get@ \/ @put@ hold the 'AgentSeat' (e.g. 'Data.IORef' in @IO@, or
-- @State@ in tests).  Example — reply agent over @State@:
--
-- @
-- let sys = tape (\\hist -> (peek hist) { from = "j", to = [from (peek hist)], body = "ack: " <> body (peek hist) })
--     ends = agentPoles get put sys  :: Poles () (K (State (AgentSeat [Post]))) [Post] [Post]
-- in  evalState (runK (close ends) [humanPost]) (AgentSeat [] [])
-- @
agentPoles ::
  (Monad m) =>
  m (AgentSeat s a) ->
  (AgentSeat s a -> m ()) ->
  PureAgent s (Post a) [Post a] ->
  Poles () (K m) [Post a] [Post a]
agentPoles getSeat putSeat sys =
  polesK
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

-- | One closed turn of a meeting body as @Ends@: commit @ins@, emit replies,
-- new seat.
--
-- Pure form of @close@ on 'agentPoles' without choosing a monad:
--
-- @runAgentPoles sys seat ins = runState (close (agentPoles get put sys) ins) seat@
runAgentPoles :: PureAgent s (Post a) [Post a] -> AgentSeat s a -> [Post a] -> ([Post a], AgentSeat s a)
runAgentPoles sys seat ins =
  let seat1 = feedAgent sys ins seat
      (outs, seat2) = flushOutbox seat1
   in (outs, seat2)

-- | Pure carrier for a 'Port' turn: the agent seat plus both stream
-- buffers of the @batchEnds@ \/ @Ends@ \/ @unbatchEnds@ composition.
data PortSeat s a = PortSeat
  { psAgent :: AgentSeat s a,
    -- | Pending commit batch (drained by each 'runPort' turn).
    psIn :: [Post a],
    -- | Pending emit queue — replies not yet peeled (drained oldest first).
    psOut :: [Post a]
  }
  deriving (Show, Eq)

-- | One closed token turn of a pure port: commit the token, emit the reply
-- token. The pure form of @close@ on a @batchEnds@ \/ @Ends@ \/
-- @unbatchEnds@ composition without choosing a monad:
--
-- @
-- runPort sys (PortSeat seat [] []) p
-- @
--
-- batches the token into the in-buffer, folds the batch through the agent
-- ('feedAgent'), flushes replies into the out-buffer ('flushOutbox'), and
-- peels one reply — the same build-stream \/ peel-stream discipline as
-- 'batchEnds' \/ 'unbatchEnds'. 'Nothing' models a quiet agent: the composed
-- emit would block, and quiet is observable here as absence instead.
runPort ::
  PureAgent s (Post a) [Post a] ->
  PortSeat s a ->
  Post a ->
  (Maybe (Post a), PortSeat s a)
runPort sys (PortSeat seat _ _) p =
  let seat1 = feedAgent sys [p] seat
      (replies, seat2) = flushOutbox seat1
   in case replies of
        [] -> (Nothing, PortSeat seat2 [] [])
        (r : rest) -> (Just r, PortSeat seat2 [] rest)

-- ---------------------------------------------------------------------------
-- Token seat — stream coalgebra around an @Ends@ pair (parser dual)
-- ---------------------------------------------------------------------------

-- | Single-post ends: keyboard \/ one-out seat.
--
-- Obtained by buffering a @Poles () (K m) [Post] [Post]@ pair on both sides, or
-- by a bare queue ('openSTM' \/ 'openIO').
--
-- A /tool call/ from an agent is just a 'Post': the 'to' list names the
-- tool, 'body' carries the arguments. No extra type — emit that 'Post' on a
-- 'Port' (or post it on the log for the tool agent to 'watch').
type Port m a = Poles () (K m) (Post a) (Post a)

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
  Poles () (K m) s f
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
-- (parser @next@ \/ 'uncons'). An empty stream blocks: the buffer is
-- re-read until a token is available — quiet is not an opinion, matching
-- the blocking read poles of the process ports. In practice the list
-- buffer ensures quiet periods are represented by an empty stream,
-- so a composed port only blocks when its upstream genuinely has nothing
-- to say.
--
-- @get@ \/ @put@ hold the stream buffer.
unbatchEnds ::
  forall f s m.
  (Monad m, Semigroup f, Uncons f s) =>
  m f ->
  (f -> m ()) ->
  Poles () (K m) f s
unbatchEnds getBuf putBuf =
  polesK
    ( \ys -> do
        xs <- getBuf
        putBuf (xs <> ys)
    )
    ( let await = do
            xs <- getBuf
            case uncons xs of
              That _ -> await
              This x -> do
                putBuf (nil @f @s)
                pure x
              These x rest -> do
                putBuf rest
                pure x
       in await
    )
