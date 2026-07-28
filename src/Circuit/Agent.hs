-- | Moore agents on a shared, addressed log; opaque shards for effects.
--
-- Pure agent shape:
--
-- @
-- type Agent s = System s (Mono Post Post)
-- @
--
-- Free carrier @s@ is required by the pretense (tape vs summary).  The common
-- log case is @Agent [Post]@ — state is the received stream.  That carrier is
-- a parse of the tape: each committed @Post@ is one token.
--
-- Effectful boundary (preferred pin):
--
-- @
-- type Shard m = Ends (Kleisli m) [Post] [Post]
-- @
--
-- Symmetric: commit a list of posts, emit a list of posts.  One-post reality
-- (hit enter) is not another type — lift with @(:[])@ on the commit side
-- (@prefixIn@).  'LogEnds' is the same shape (dual seat on the log).
-- Opacity is commit\/emit only; no interior.
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
--   :: Ends (Kleisli m) Post Post
-- @
--
-- Queue ends ('openSTM' \/ 'openIO') are the effectful token wire of the same
-- shape when you need a bare @Post@\/@Post@ channel without a shard.
--
-- Design card: @coffee\/loom\/agent.md@.
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Circuit.Agent
  ( -- * Posts and the log
    Post (..),
    Log,

    -- * Pure agents
    Agent,
    AgentState (..),
    emptyAgentState,
    tape,
    selfrec,

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

    -- * Session assembly
    session,

    -- * Running one step
    run1,

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
    composeEnds,
    dimapEnds,
    endsK,
    lmapEnds,
    openIO,
    openSTM,
    prefixIn,
    rmapEnds,
    (>:>),
  )
import Circuit.Stream (These (..), Snoc (..), Uncons (..))
import Circuit.Poly (Eval (..), Mono, System)
import Circuit.Poly.Process (runSystem)
import Control.Arrow (Kleisli (..))
import Data.List (foldl')
import Data.Text (Text)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Circuit.Agent
-- >>> import Circuit.Poly.Process (iterateSystem)

-- | A single entry on the shared log.
data Post = Post
  { author :: Text,
    addr :: Text,
    channel :: Text,
    body :: Text
  }
  deriving (Show, Eq)

-- | The shared append-only log, newest first.
type Log = [Post]

-- | Pure agent: a Moore machine over posts, free carrier.
--
-- @System s (Mono Post Post) ≅ s -> (Post, Post -> s)@.
-- Common log case: @Agent [Post]@ (state = received stream).
type Agent s = System s (Mono Post Post)

-- | Opaque effectful ends: stream @f@ both ways.
--
-- Common case: @Shard m [Post]@.  Pipeline speaks a stream on commit and
-- emit.  Keyboard one-shot:
--
-- @
-- prefixIn (:[])  -- Post -> [Post] on the conjoint
-- @
--
-- Emit is an onslaught of posts (empty = quiet \/ done for that poll).
type Shard m f = Ends (Kleisli m) f f

-- | Same ends shape as 'Shard' — dual seat on the log (journal 013).
type LogEnds m f = Shard m f

-- | Build a 'Shard' from monadic commit and emit actions.
shard :: (Monad m) => (f -> m ()) -> m f -> Shard m f
shard = endsK

-- | Build log ends (same as 'shard'; dual seat).
logEnds :: (Monad m) => (f -> m ()) -> m f -> LogEnds m f
logEnds = endsK

-- | Born empty, conses each received input onto its history.
--
-- >>> iterateSystem (tape length) [] [1,2,3 :: Int]
-- [1,2,3]
tape :: ([i] -> o) -> System [i] (Mono o i)
tape f hist = EP (EK (f hist), EE (: hist))

-- | Like 'tape', but also conses the agent's own output onto its history.
--
-- This is the internal-monologue construction: an agent's outputs are on the
-- same log as its percepts, visible to its own future turns.
selfrec :: ([i] -> i) -> System [i] (Mono i i)
selfrec f hist = EP (EK (f hist), EE (\i -> let h' = i : hist in f h' : h'))

-- | State for a pure agent in delivery: free carrier plus a count of posts
-- already received from the log.
--
-- The carrier @s@ is opaque to the delivery bookkeeping; only 'Snoc' is needed
-- to append each newly delivered post.  The count keeps the cursor into the
-- addressed stream without requiring the carrier to be a list.
data AgentState s = AgentState
  { asCarrier :: s,
    -- | Number of posts addressed to this agent already consumed from the log.
    asSeen :: Int
  }
  deriving (Show, Eq)

-- | Empty carrier and zero seen count.
emptyAgentState :: forall s. (Snoc s Post) => AgentState s
emptyAgentState = AgentState (snocNil @s @Post) 0

-- | Read end of the log: all posts addressed to @who@, oldest first.
watch :: Text -> Log -> [Post]
watch who t = reverse (filter ((== who) . addr) t)

-- | Write end of the log: commit a post.
post :: Post -> Log -> Log
post = (:)

-- | Per-agent session assembly: the bodies an agent actually sees.
session :: Text -> Log -> [Text]
session who = map body . watch who

-- | One delivery round: 'watch' unread posts, step the machine, 'post' each output.
--
-- The 'AgentState' carries the free carrier @s@ and a count of already-received
-- posts.  Only 'Snoc' is required on @s@, so the carrier need not be a list.
turn ::
  Text ->
  Agent s ->
  AgentState s ->
  Log ->
  (AgentState s, Log)
turn who sys (AgentState seen n) log0 =
  foldl'
    ( \(AgentState seen' n', log') i ->
        let (o, seen'') = run1 sys seen' i
         in (AgentState seen'' (n' + 1), post o log')
    )
    (AgentState seen n, log0)
    (drop n (watch who log0))

-- | Whether @who@ has addressed posts not yet consumed.
--
-- Matches 'turn''s delivery bookkeeping: unread = drop (asSeen st) (watch who lg).
hasPending :: Text -> AgentState s -> Log -> Bool
hasPending who st lg = not (null (drop (asSeen st) (watch who lg)))

-- | Round-robin turn-loop until no agent has pending deliveries (quiescence).
--
-- Roster order is the schedule.  Each pass runs 'turn' for every agent that
-- still has pending work at its slot.  Passes repeat until a pass starts with
-- nobody pending.  Carriers start empty for every name.
loop ::
  forall s.
  (Snoc s Post) =>
  [(Text, Agent s)] ->
  Log ->
  ([(Text, AgentState s)], Log)
loop roster log0 = go [(n, emptyAgentState @s) | (n, _) <- roster] log0
  where
    go states lg
      | not (any (\(n, st) -> hasPending n st lg) states) = (states, lg)
      | otherwise =
          let (states', lg') = foldl' step (states, lg) roster
           in go states' lg'
    step (states, lg) (name, agent) =
      case lookup name states of
        Nothing -> (states, lg)
        Just st
          | hasPending name st lg ->
              let (st', lg') = turn name agent st lg
               in (setSeen name st' states, lg')
          | otherwise -> (states, lg)

setSeen :: Text -> AgentState s -> [(Text, AgentState s)] -> [(Text, AgentState s)]
setSeen name st = map (\(n, s) -> if n == name then (n, st) else (n, s))

-- | Run a monomial system for one step.
--
-- Consume @i@, then extract the output from the successor state (Process /
-- 'iterateSystem' timing).
run1 :: System s (Mono o i) -> s -> i -> (o, s)
run1 sys s i =
  let s' = snd (runSystem sys s) i
      (o, _) = runSystem sys s'
   in (o, s')

-- ---------------------------------------------------------------------------
-- Agent as Shard — change of base into Kleisli Ends
-- ---------------------------------------------------------------------------

-- | State behind an 'agentShard': free carrier plus a pending emit queue.
--
-- Commit parses inputs into the carrier and enqueues one output 'Post' per
-- input (the Moore step).  Emit flushes the queue — empty means quiet.
data AgentSeat s = AgentSeat
  { asState :: s,
    -- | Pending outputs, oldest first.
    asOutbox :: [Post]
  }
  deriving (Show, Eq)

-- | Pure parse step: fold committed posts through the coalgebra.
feedAgent :: Agent s -> [Post] -> AgentSeat s -> AgentSeat s
feedAgent sys ins (AgentSeat s0 outs0) =
  let (outs1, s1) =
        foldl'
          ( \(outs, s) i ->
              let (o, s') = run1 sys s i
               in (outs ++ [o], s')
          )
          ([], s0)
          ins
   in AgentSeat s1 (outs0 ++ outs1)

-- | Take the outbox; leave carrier unchanged.
flushOutbox :: AgentSeat s -> ([Post], AgentSeat s)
flushOutbox (AgentSeat s outs) = (outs, AgentSeat s [])

-- | Reinterpret a pure 'Agent' as a list 'Shard'.
--
-- @
-- agentShard get put sys  ::  Shard m [Post]
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
-- let sys = tape (\\hist -> (peek hist) { author = "j", addr = author (peek hist), body = "ack: " <> body (peek hist) })
--     sh  = agentShard get put sys  :: Shard (State (AgentSeat [Post])) [Post]
-- in  evalState (runKleisli (close (conjoint sh) (companion sh)) [humanPost]) (AgentSeat [] [])
-- @
agentShard ::
  (Monad m) =>
  m (AgentSeat s) ->
  (AgentSeat s -> m ()) ->
  Agent s ->
  Shard m [Post]
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
-- @runAgentShard sys seat ins = runState (closeShard (agentShard get put sys) ins) seat@
runAgentShard :: Agent s -> AgentSeat s -> [Post] -> ([Post], AgentSeat s)
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
-- A /tool call/ from an agent is just a 'Post': @addr@ names the tool,
-- @body@ carries the arguments. No extra type — emit that 'Post' on a
-- 'Port' (or post it on the log for the tool agent to 'watch').
type Port m = Ends (Kleisli m) Post Post

-- 'Snoc' is re-exported from 'Circuit.Stream' (construction dual of 'Uncons').

-- | Snoc a 'Post' onto a post stream. Specialized alias for 'snoc'.
snocPost :: [Post] -> Post -> [Post]
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
  Ends (Kleisli m) s f
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
-- (parser @next@ \/ 'uncons'). Empty stream is a programming error at emit —
-- quiet belongs at the list 'Shard' layer (@[]@), not at the token seat.
--
-- @get@ \/ @put@ hold the stream buffer.
unbatchEnds ::
  forall f s m.
  (Monad m, Semigroup f, Uncons f s) =>
  m f ->
  (f -> m ()) ->
  Ends (Kleisli m) f s
unbatchEnds getBuf putBuf =
  endsK
    ( \ys -> do
        xs <- getBuf
        putBuf (xs <> ys)
    )
    ( do
        xs <- getBuf
        case uncons xs of
          That _ ->
            error "unbatchEnds: empty stream (no token to emit)"
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
  m [Post] ->
  ([Post] -> m ()) ->
  m [Post] ->
  ([Post] -> m ()) ->
  Shard m [Post] ->
  Port m
portShard getIn putIn getOut putOut sh =
  batchEnds getIn putIn >:> sh >:> unbatchEnds getOut putOut

-- ---------------------------------------------------------------------------
-- Shard combinators
-- ---------------------------------------------------------------------------

-- | Adapt a shard on the commit side (contravariant).
--
-- Transform the @[Post]@ before it is committed.  One common use is
-- session assembly: @prefixShard session@ changes the payload that the
-- shard posts.
prefixShard :: (Monad m) => (f -> f) -> Shard m f -> Shard m f
prefixShard f = lmapEnds (Kleisli $ pure . f)

-- | Adapt a shard on the emit side (covariant).
--
-- Transform the stream after it is emitted.  One common use is a
-- transport envelope: @suffixShard (map addHeader)@ decorates every
-- emitted post.
suffixShard :: (Monad m) => (f -> f) -> Shard m f -> Shard m f
suffixShard g = rmapEnds (Kleisli $ pure . g)

-- | Adapt both sides of a shard at once.
--
-- @codecShard f g = prefixShard f . suffixShard g@.
codecShard :: (Monad m) => (f -> f) -> (f -> f) -> Shard m f -> Shard m f
codecShard f g = dimapEnds (Kleisli $ pure . f) (Kleisli $ pure . g)

-- | Sequential composition of shards.
--
-- The output stream of the first shard feeds the input stream of the
-- second.  This is the same shape as connecting two effectful agents
-- in series.
composeShard :: (Monad m) => Shard m f -> Shard m f -> Shard m f
composeShard = composeEnds
