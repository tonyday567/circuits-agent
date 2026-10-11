-- | Seat-level tensor combinators over shards, with state carried by
-- 'Step'.
--
-- These are the semantic citizens that free-agent 'FreeSeat' terms fold into.
-- The buffer state is part of the base arrow ('Step (,) (,) [Post Text]
-- [Post Text] (K IO)') rather than a monad transformer.
module Circuit.Agent.Tensor
  ( AgentShard,
    silentShard,
    awaitShard,
    raceShard,
    fanOutShard,
    fanInShard,
    runSubShard,
    closeShardIO,
    ioShard,
    writeBatch,
    readBatch,
    synthesisSummary,
  )
where

import Circuit.Agent (Name, Post (..), PostId, mkPost, synthesis)
import Circuit.Category (K (..))
import Circuit.Machine (Poles (..), Step (..), close)
import Data.Text (Text)
import Data.Text qualified as T

-- | An effectful agent shard with a '[Post Text]' buffer threaded through the
-- arrow.
type AgentShard a b = Poles () (Step (,) (,) [Post Text] [Post Text] (K IO)) a b

-- | Run a child shard in isolation on the given input, discarding its
-- residual state.  Branches in await / race / fan-out have private scratch
-- state; only their emits rejoin the main stream.
runSubShard :: AgentShard [Post Text] [Post Text] -> [Post Text] -> IO [Post Text]
runSubShard sh xs = do
  let thread = close sh
  (_, ys) <- runK (run thread) ([], xs)
  pure ys

-- | Close a same-type shard once, exposing both the output and the residual
-- state.  Works for any state carrier @s@ and payload @a@.
closeShardIO :: Poles () (Step (,) (,) s s (K IO)) a a -> a -> s -> IO (a, s)
closeShardIO sh x s0 = do
  let thread = close sh
  (s', y) <- runK (run thread) (s0, x)
  pure (y, s')

-- | Helper: store the input batch as the buffer.
writeBatch :: Step (,) (,) [Post Text] [Post Text] (K IO) [Post Text] ()
writeBatch = Step $ K $ \(_, xs) -> pure (xs, ())

-- | Helper: return the buffer as output and clear it.
readBatch :: Step (,) (,) [Post Text] [Post Text] (K IO) () [Post Text]
readBatch = Step $ K $ \(s, ()) -> pure ([], s)

-- | Build an agent shard that stores the input batch, then computes outputs
-- from that batch in 'IO'.
ioShard :: ([Post Text] -> IO [Post Text]) -> AgentShard [Post Text] [Post Text]
ioShard emit = Poles writeBatch writeBatch read'
  where
    read' = Step $ K $ \(s, ()) -> do
      outs <- emit s
      pure ([], outs)

-- | Silent shard: commit replaces the buffer; emit clears it and returns [].
silentShard :: AgentShard [Post Text] [Post Text]
silentShard = ioShard (pure . const [])

-- | Product / await shard: both sub-shards see the same input; emits are
-- concatenated left-to-right.
awaitShard ::
  AgentShard [Post Text] [Post Text] ->
  AgentShard [Post Text] [Post Text] ->
  AgentShard [Post Text] [Post Text]
awaitShard sh1 sh2 = Poles writeBatch writeBatch read'
  where
    read' = Step $ K $ \(s, ()) -> do
      o1 <- runSubShard sh1 s
      o2 <- runSubShard sh2 s
      pure ([], o1 ++ o2)

-- | Coproduct / race shard: left emit wins if non-empty, otherwise right.
raceShard ::
  AgentShard [Post Text] [Post Text] ->
  AgentShard [Post Text] [Post Text] ->
  AgentShard [Post Text] [Post Text]
raceShard sh1 sh2 = Poles writeBatch writeBatch read'
  where
    read' = Step $ K $ \(s, ()) -> do
      o1 <- runSubShard sh1 s
      o2 <- runSubShard sh2 s
      pure ([], if null o1 then o2 else o1)

-- | Fan-out shard: every sub-shard sees the same input; emits are concatenated
-- in branch order.
fanOutShard ::
  [AgentShard [Post Text] [Post Text]] ->
  AgentShard [Post Text] [Post Text]
fanOutShard shs = Poles writeBatch writeBatch read'
  where
    read' = Step $ K $ \(s, ()) -> do
      os <- traverse (`runSubShard` s) shs
      pure ([], concat os)

-- | Fan-in shard: fan-out, then collapse the collected branch outputs with the
-- supplied summary function.
fanInShard ::
  ([[Post Text]] -> [Post Text]) ->
  [AgentShard [Post Text] [Post Text]] ->
  AgentShard [Post Text] [Post Text]
fanInShard summary shs = Poles writeBatch writeBatch read'
  where
    read' = Step $ K $ \(s, ()) -> do
      os <- traverse (`runSubShard` s) shs
      pure ([], summary os)

-- | A fan-in summary honest by construction: the single output post is a
-- 'synthesis' of the supplied parent ids, so its ancestry cites every branch
-- output by exact reference.  The supplied function computes the body.
-- No branch outputs, or an empty body -> no posts (quiet).
--
-- The caller supplies one 'PostId' per branch output (in the order produced
-- by @concat oss@).  When ids are not available, pass @[]@ and the summary
-- falls back to a root post (no thread edge).
synthesisSummary ::
  Name ->
  [Name] ->
  [PostId] ->
  ([[Post Text]] -> Text) ->
  [[Post Text]] ->
  [Post Text]
synthesisSummary who audience parentIds f oss =
  case (concat oss, T.strip (f oss)) of
    ([], _) -> []
    (_, b) | T.null b -> []
    (ps, b) ->
      let ids = take (length ps) parentIds
       in [if null ids then mkPost who audience b else synthesis who audience ids b]
