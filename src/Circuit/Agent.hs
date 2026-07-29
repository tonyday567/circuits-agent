-- | Moore agents on a shared, addressed log; opaque shards for effects.
--
-- Pure agent shape:
--
-- @
-- type Agent s = System s (Mono [Post] Post)
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
-- Queue ends ('openSTM' \/'openIO') are the effectful token wire of the same
-- shape when you need a bare @Post\/@Post@ channel without a shard.
--
-- Design card: @coffee\/loom\/agent.md@.
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Circuit.Agent
  ( -- * Posts and the log
    Post (..),
    Log,
    emptyLog,

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

    -- * Derivations
    Derivation (..),

    -- * Session assembly
    session,

    -- * Running one step
    run1,

    -- * Behaviour (stream semantics)
    Beh,
    beh,
    after,

    -- * Choice (level-1 grammar fragment)
    branchAgent,

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
    trace,
    (>:>),
  )
import Circuit.Agent.Delivery (deliversToSemiring)
import Circuit.Loop (Loop (..))
import Circuit.Stream (Cons (..), These (..), Snoc (..), Uncons (..))
import Circuit.Poly (Eval (..), Mono, System (..), fromEvalSystem, monoDir)
import Circuit.Poly.Process (after, runSystem)
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
--
-- The log is a stream of 'Post's.  Common case: @Log [Post]@.  Generalizing to
-- any @f@ with 'Cons' and 'Uncons' lets the same delivery machinery run over
-- other stream representations while keeping the addressed read as a list.
type Log f = f

-- | Pure agent: a Moore machine over posts, free carrier.
--
-- @System (->) s (Mono [Post] Post) ≅ s -> ([Post], Post -> s)@.
-- Common log case: @Agent [Post]@ (state = received stream).
type Agent s = System (->) s (Mono [Post] Post)

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
tape :: ([i] -> o) -> System (->) [i] (Mono o i)
tape f = System $ \(hist, d) -> (monoDir d : hist, (f hist, ()))

-- | Like 'tape', but also conses the agent's own output onto its history.
--
-- This is the internal-monologue construction: an agent's outputs are on the
-- same log as its percepts, visible to its own future turns.
selfrec :: ([i] -> i) -> System (->) [i] (Mono i i)
selfrec f = System $ \(hist, d) ->
  let i = monoDir d
      h' = i : hist
   in (f h' : h', (f hist, ()))

-- | Addressed stream of unread posts for one agent.
--
-- The 'Inbox' owns both the agent's name and the unread stream.  Only posts
-- whose 'addr' matches the owner are peeled by 'unconsInbox'.
newtype Inbox f = Inbox {unInbox :: (Text, f)}
  deriving (Show, Eq)

-- | Owner of the inbox.
inboxWho :: Inbox f -> Text
inboxWho = fst . unInbox

-- | Empty inbox for the named agent.
emptyInbox :: forall f. (Uncons f Post) => Text -> Inbox f
emptyInbox who = Inbox (who, nil @f @Post)

-- | Append a post to the right of the inbox.
appendInbox :: (Snoc f Post) => Post -> Inbox f -> Inbox f
appendInbox p (Inbox (who, f)) = Inbox (who, snoc f p)

-- | Lightweight delivery predicate.
--
-- A post delivers to @who@ when its 'addr' matches @who@.  If the post's
-- 'channel' is @\"broadcast\"@, it delivers to every recipient.  An empty
-- 'channel' keeps the unicast default.  This predicate is a small stepping
-- stone toward a relational copy/discard delivery model ('FinRel'); the full
-- wiring is future work.
deliversTo :: Post -> Text -> Bool
deliversTo p who = deliversToSemiring (addr p) (channel p) who

-- | Peel the oldest addressed post from the inbox, returning the rest.
--
-- Non-matching posts are skipped and discarded.  An empty or exhausted inbox
-- returns 'That' with an empty inbox.
unconsInbox :: (Uncons f Post) => Inbox f -> These Post (Inbox f)
unconsInbox (Inbox (who, f)) = go f
  where
    go stream = case uncons stream of
      That rest -> That (Inbox (who, rest))
      This p
        | deliversTo p who -> This p
        | otherwise -> That (emptyInbox who)
      These p rest
        | deliversTo p who -> These p (Inbox (who, rest))
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
data Derivation = Derivation
  { dAgent :: Text,
    dInput :: Post,
    dOutputs :: [Post],
    dChildren :: [Derivation]
  }
  deriving (Show, Eq)

-- | Empty carrier and empty inbox for the named agent.
emptyAgentState :: forall s f. (Snoc s Post, Uncons f Post) => Text -> AgentState s f
emptyAgentState who = AgentState (snocNil @s @Post) (emptyInbox who)

-- | Seed an inbox with all posts addressed to @who@ from the log, oldest first.
seedInbox :: (Snoc f Post, Uncons f Post) => Text -> Log f -> Inbox f
seedInbox who lg = foldl' (flip appendInbox) (emptyInbox who) (watch who lg)

-- | Empty carrier and an inbox seeded from the log for the named agent.
seedAgentState :: forall s f. (Snoc s Post, Snoc f Post, Uncons f Post) => Text -> Log f -> AgentState s f
seedAgentState who lg = AgentState (snocNil @s @Post) (seedInbox who lg)

-- | Empty log.
emptyLog :: forall f. (Cons f Post) => Log f
emptyLog = consNil @f @Post

-- | Read end of the log: all posts addressed to @who@, oldest first.
--
-- Traversal is newest-to-oldest; matching posts are prepended, so the
-- accumulator is already oldest-first.
watch :: (Uncons f Post) => Text -> Log f -> [Post]
watch who t = go t []
  where
    go stream acc =
      case uncons stream of
        That _ -> acc
        This p -> if addr p == who then p : acc else acc
        These p rest -> go rest (if addr p == who then p : acc else acc)

-- | Write end of the log: commit a post.
post :: (Cons f Post) => Post -> Log f -> Log f
post = cons

-- | Per-agent session assembly: the bodies an agent actually sees.
session :: (Uncons f Post) => Text -> Log f -> [Text]
session who = map body . watch who

-- | One delivery round: peel one addressed post, step the machine, 'post' each output.
--
-- The 'AgentState' carries the free carrier @s@ and an addressed inbox.  Only
-- one post is consumed per call; repeated calls drain the inbox.  Outputs are
-- committed newest-first via 'post'.  When a post is processed, the returned
-- 'Derivation' records the agent name, the input post, and the emitted outputs.
turn ::
  (Cons f Post, Uncons f Post) =>
  Agent s ->
  AgentState s f ->
  Log f ->
  (AgentState s f, Log f, Maybe Derivation)
turn sys st log0 =
  let who = inboxWho (asInbox st)
   in case unconsInbox (asInbox st) of
        That _ -> (st, log0, Nothing)
        This p ->
          let (os, seen') = run1 sys (asCarrier st) p
           in (AgentState seen' (emptyInbox who), foldl' (flip post) log0 os, Just (Derivation who p os []))
        These p rest ->
          let (os, seen') = run1 sys (asCarrier st) p
           in (AgentState seen' rest, foldl' (flip post) log0 os, Just (Derivation who p os []))

-- | Whether the agent's inbox has an addressed post waiting.
hasPending :: (Uncons f Post) => AgentState s f -> Bool
hasPending st = case unconsInbox (asInbox st) of That _ -> False; _ -> True

-- | Stream length via 'Uncons'.
streamLength :: forall f a. (Uncons f a) => f -> Int
streamLength s = go 0 s
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
  forall s f.
  (Snoc s Post, Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, Agent s)] ->
  Log f ->
  ([(Text, AgentState s f)], Log f, [Derivation])
loop roster log0 = loopWith roster [(n, seedAgentState @s @f n log0) | (n, _) <- roster] log0

-- | Resumable 'loop': supply the initial states and inboxes.
--
-- Implemented as an 'Either' trace over the roster: each pass is one
-- iteration of the feedback channel, quiescence returns a 'Right' result.
loopWith ::
  forall s f.
  (Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, Agent s)] ->
  [(Text, AgentState s f)] ->
  Log f ->
  ([(Text, AgentState s f)], Log f, [Derivation])
loopWith roster states0 log0 = trace body ()
  where
    bundle0 = (states0, log0, []) :: ([(Text, AgentState s f)], Log f, [Derivation])
    body (Right ()) =
      if any (hasPending . snd) states0
        then Left bundle0
        else Right bundle0
    body (Left bundle) =
      let bundle' = meetingPass roster bundle
       in if any (hasPending . snd) (fst3 bundle')
            then Left bundle'
            else Right bundle'
    fst3 (x, _, _) = x

-- | The same meeting as a 'Loop' value: 'Knot' body over the 'Either'
-- tensor, quiescence returned as a 'Right' payload.
meetingLoop ::
  forall s f.
  (Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, Agent s)] ->
  Loop Either (->) ([(Text, AgentState s f)], Log f, [Derivation]) ([(Text, AgentState s f)], Log f, [Derivation])
meetingLoop roster = Knot body
  where
    body (Right bundle@(states, _, _)) =
      if any (hasPending . snd) states
        then Left bundle
        else Right bundle
    body (Left bundle) =
      let bundle'@(states', _, _) = meetingPass roster bundle
       in if any (hasPending . snd) states'
            then Left bundle'
            else Right bundle'

-- | One roster pass: schedule every agent that has pending work.
meetingPass ::
  forall s f.
  (Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, Agent s)] ->
  ([(Text, AgentState s f)], Log f, [Derivation]) ->
  ([(Text, AgentState s f)], Log f, [Derivation])
meetingPass roster (states, lg, derivs) = foldl' step (states, lg, derivs) roster
  where
    step (st, l, ds) (name, agent) =
      case lookup name st of
        Nothing -> (st, l, ds)
        Just sti
          | hasPending sti ->
              let (st', l', md) = turn agent sti l
                  newCount = streamLength @f @Post l' - streamLength @f @Post l
                  newPosts = takeStream newCount l'
                  st'' = foldl' routePost (updateState name st' st) newPosts
                  ds' = maybe ds (\d -> ds ++ [d]) md
               in (st'', l', ds')
          | otherwise -> (st, l, ds)

    updateState name st' = map (\(n, s) -> if n == name then (n, st') else (n, s))

    routePost states' p =
      map
        ( \(n, st) ->
            if deliversTo p n
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
  forall s f.
  (Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, Agent s)] ->
  [(Text, AgentState s f)] ->
  Log f ->
  [([(Text, AgentState s f)], Log f, [Derivation])]
loops roster states0 log0 = (states0, log0, []) : go states0 log0 []
  where
    go :: [(Text, AgentState s f)] -> Log f -> [Derivation] -> [([(Text, AgentState s f)], Log f, [Derivation])]
    go states lg derivs
      | not (any (hasPending . snd) states) = []
      | otherwise =
          let (states', lg', derivs') = foldl' step (states, lg, derivs) roster
           in (states', lg', derivs') : go states' lg' derivs'

    step :: ([(Text, AgentState s f)], Log f, [Derivation]) -> (Text, Agent s) -> ([(Text, AgentState s f)], Log f, [Derivation])
    step (states, lg, derivs) (name, agent) =
      case lookup name states of
        Nothing -> (states, lg, derivs)
        Just st
          | hasPending st ->
              let (st', lg', md) = turn agent st lg
                  newCount = streamLength @f @Post lg' - streamLength @f @Post lg
                  newPosts = takeStream newCount lg'
                  states'' = foldl' routePost (updateState name st' states) newPosts
                  derivs' = maybe derivs (\d -> derivs ++ [d]) md
               in (states'', lg', derivs')
          | otherwise -> (states, lg, derivs)

    updateState :: Text -> AgentState s f -> [(Text, AgentState s f)] -> [(Text, AgentState s f)]
    updateState name st' = map (\(n, s) -> if n == name then (n, st') else (n, s))

    routePost :: [(Text, AgentState s f)] -> Post -> [(Text, AgentState s f)]
    routePost states p =
      map
        ( \(n, st) ->
            if deliversTo p n
              then (n, st {asInbox = appendInbox p (asInbox st)})
              else (n, st)
        )
        states

-- | Resumable 'loop' with a heterogeneous roster: each agent supplies its own
-- initial carrier, while inboxes are still seeded from the shared log.
loopHetero ::
  forall s f.
  (Snoc f Post, Cons f Post, Uncons f Post) =>
  [(Text, s, Agent s)] ->
  Log f ->
  ([(Text, AgentState s f)], Log f, [Derivation])
loopHetero roster log0 =
  loopWith (map (\(n, _, a) -> (n, a)) roster) (map (\(n, s, _) -> (n, AgentState s (seedInbox n log0))) roster) log0

-- | Run a monomial system for one step.
--
-- Consume @i@, then extract the output from the successor state (Process /
-- 'iterateSystem' timing).
run1 :: System (->) s (Mono o i) -> s -> i -> (o, s)
run1 sys s i =
  let s' = snd (runSystem sys s) i
      (o, _) = runSystem sys s'
   in (o, s')

-- | Agent behaviour: a pure function from an input stream to an output stream.
--
-- Each input post is stepped through the agent; the per-step output lists are
-- concatenated into a single output stream.  This is the stream semantics of
-- the Moore coalgebra, independent of any effectful boundary.
type Beh = [Post] -> [Post]

-- | Run an agent from an initial carrier to obtain its 'Beh'aviour.
beh :: Agent s -> s -> Beh
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
branchAgent :: (s -> Bool) -> Agent s -> Agent s -> Agent s
branchAgent cond (System left) (System right) =
  System $ \(state, d) ->
    if cond state then left (state, d) else right (state, d)

-- ---------------------------------------------------------------------------
-- Agent as Shard — change of base into Kleisli Ends
-- ---------------------------------------------------------------------------

-- | State behind an 'agentShard': free carrier plus a pending emit queue.
--
-- Commit parses inputs into the carrier and enqueues one output list per
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
              let (os, s') = run1 sys s i
               in (outs ++ os, s')
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
