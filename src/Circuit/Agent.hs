-- | Moore agents on a shared, addressed log; opaque shards for effects.
--
-- Pure agent shape:
--
-- @
-- type Agent s = System s (Mono Post Post)
-- @
--
-- Free carrier @s@ is required by the pretense (tape vs summary).  The common
-- log case is @Agent [Post]@ — state is the received stream.
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
-- Design card: @coffee\/loom\/agent.md@.  Sketch witnesses:
-- @circuits-poly\/examples\/agent-sketch.md@.
module Circuit.Agent
  ( -- * Posts and the log
    Post (..),
    Log,

    -- * Pure agents
    Agent,
    tape,
    selfrec,

    -- * Effectful ends (symmetric lists)
    Shard,
    LogEnds,
    shard,
    logEnds,

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
    close,
    composeEnds,
    dimapEnds,
    endsK,
    lmapEnds,
    prefixIn,
    rmapEnds,
    (>:>),
  )
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

-- | Opaque effectful ends: lists both ways.
--
-- Pipeline speaks @[Post]@ on commit and emit.  Keyboard one-shot:
--
-- @
-- prefixIn (:[])  -- Post -> [Post] on the conjoint
-- @
--
-- Emit is an onslaught of posts (empty = quiet \/ done for that poll).
type Shard m = Ends (Kleisli m) [Post] [Post]

-- | Same ends shape as 'Shard' — dual seat on the log (journal 013).
type LogEnds m = Shard m

-- | Build a 'Shard' from monadic commit and emit actions.
shard :: (Monad m) => ([Post] -> m ()) -> m [Post] -> Shard m
shard = endsK

-- | Build log ends (same as 'shard'; dual seat).
logEnds :: (Monad m) => ([Post] -> m ()) -> m [Post] -> LogEnds m
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
-- The first component of the input pair is the agent's received stream so
-- far; the second is the shared log.  The force tracks delivery by counting
-- already-received posts.  Specialized to the received-stream carrier.
turn :: Text -> Agent [Post] -> ([Post], Log) -> ([Post], Log)
turn who sys (seen, log0) =
  foldl'
    (\(seen', log') i -> let (o, seen'') = run1 sys seen' i in (seen'', post o log'))
    (seen, log0)
    (drop (length seen) (watch who log0))

-- | Whether @who@ has addressed posts not yet in @seen@.
--
-- Matches 'turn''s delivery bookkeeping: unread = drop (length seen) (watch who lg).
hasPending :: Text -> [Post] -> Log -> Bool
hasPending who seen lg = not (null (drop (length seen) (watch who lg)))

-- | Round-robin turn-loop until no agent has pending deliveries (quiescence).
--
-- Roster order is the schedule.  Each pass runs 'turn' for every agent that
-- still has pending work at its slot.  Passes repeat until a pass starts with
-- nobody pending.  Received streams start empty for every name.
--
-- Pure v0: only 'Agent' [@Post@]; shards join later.
loop :: [(Text, Agent [Post])] -> Log -> ([(Text, [Post])], Log)
loop roster log0 = go [(n, []) | (n, _) <- roster] log0
  where
    go seens lg
      | not (any (\(n, s) -> hasPending n s lg) seens) = (seens, lg)
      | otherwise =
          let (seens', lg') = foldl' step (seens, lg) roster
           in go seens' lg'
    step (seens, lg) (name, agent) =
      case lookup name seens of
        Nothing -> (seens, lg)
        Just seen
          | hasPending name seen lg ->
              let (seen', lg') = turn name agent (seen, lg)
               in (setSeen name seen' seens, lg')
          | otherwise -> (seens, lg)

setSeen :: Text -> [Post] -> [(Text, [Post])] -> [(Text, [Post])]
setSeen name seen = map (\(n, s) -> if n == name then (n, seen) else (n, s))

-- | Run a monomial system for one step.
run1 :: System s (Mono o i) -> s -> i -> (o, s)
run1 sys s i =
  let s' = snd (runSystem sys s) i
   in (fst (runSystem sys s'), s')

-- ---------------------------------------------------------------------------
-- Shard combinators
-- ---------------------------------------------------------------------------

-- | Adapt a shard on the commit side (contravariant).
--
-- Transform the @[Post]@ before it is committed.  One common use is
-- session assembly: @prefixShard session@ changes the payload that the
-- shard posts.
prefixShard :: (Monad m) => ([Post] -> [Post]) -> Shard m -> Shard m
prefixShard f = lmapEnds (Kleisli $ pure . f)

-- | Adapt a shard on the emit side (covariant).
--
-- Transform the @[Post]@ after it is emitted.  One common use is a
-- transport envelope: @suffixShard (map addHeader)@ decorates every
-- emitted post.
suffixShard :: (Monad m) => ([Post] -> [Post]) -> Shard m -> Shard m
suffixShard g = rmapEnds (Kleisli $ pure . g)

-- | Adapt both sides of a shard at once.
--
-- @codecShard f g = prefixShard f . suffixShard g@.
codecShard :: (Monad m) => ([Post] -> [Post]) -> ([Post] -> [Post]) -> Shard m -> Shard m
codecShard f g = dimapEnds (Kleisli $ pure . f) (Kleisli $ pure . g)

-- | Sequential composition of shards.
--
-- The output stream of the first shard feeds the input stream of the
-- second.  This is the same shape as connecting two effectful agents
-- in series.
composeShard :: (Monad m) => Shard m -> Shard m -> Shard m
composeShard = composeEnds
