{-# LANGUAGE GADTs #-}

-- | Seat-level tensor combinators over 'Shard' values in 'StateT [Post] IO'.
--
-- These are the semantic citizens that free-agent 'FreeSeat' terms fold into.
-- They live in circuits-agent because they mention no free syntax: only
-- 'Shard', 'Post', and the shared 'StateT [Post] IO' buffer.
module Circuit.Agent.Tensor
  ( silentShard,
    awaitShard,
    raceShard,
    fanOutShard,
    fanInShard,
  )
where

import Circuit (Ends (..), close, companion, conjoint, endsK)
import Circuit.Agent (Post, Shard)
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (StateT, get, put, runStateT)

-- | Run a child shard in isolation on the given input, discarding its
-- residual state.  Branches in await / race / fan-out have private scratch
-- state; only their emits rejoin the main stream.
runSubShard :: Shard (StateT [Post] IO) [Post] [Post] -> [Post] -> StateT [Post] IO [Post]
runSubShard sh xs = do
  let kleisli = close (conjoint sh) (companion sh)
  liftIO (fmap fst (runStateT (runKleisli kleisli xs) []))

-- | Silent shard: commit replaces state, emit clears it and returns [].
silentShard :: Shard (StateT [Post] IO) [Post] [Post]
silentShard =
  endsK
    (\xs -> put xs)
    (put [] >> pure [])

-- | Product / await shard: both sub-shards see the same input; emits are
-- concatenated left-to-right.
awaitShard ::
  Shard (StateT [Post] IO) [Post] [Post] ->
  Shard (StateT [Post] IO) [Post] [Post] ->
  Shard (StateT [Post] IO) [Post] [Post]
awaitShard sh1 sh2 =
  endsK
    (\xs -> put xs)
    ( do
        xs <- get
        put []
        o1 <- runSubShard sh1 xs
        o2 <- runSubShard sh2 xs
        pure (o1 ++ o2)
    )

-- | Coproduct / race shard: left emit wins if non-empty, otherwise right.
raceShard ::
  Shard (StateT [Post] IO) [Post] [Post] ->
  Shard (StateT [Post] IO) [Post] [Post] ->
  Shard (StateT [Post] IO) [Post] [Post]
raceShard sh1 sh2 =
  endsK
    (\xs -> put xs)
    ( do
        xs <- get
        put []
        o1 <- runSubShard sh1 xs
        o2 <- runSubShard sh2 xs
        pure (if null o1 then o2 else o1)
    )

-- | Fan-out shard: every sub-shard sees the same input; emits are concatenated
-- in branch order.
fanOutShard ::
  [Shard (StateT [Post] IO) [Post] [Post]] ->
  Shard (StateT [Post] IO) [Post] [Post]
fanOutShard shs =
  endsK
    (\xs -> put xs)
    ( do
        xs <- get
        put []
        os <- traverse (`runSubShard` xs) shs
        pure (concat os)
    )

-- | Fan-in shard: fan-out, then collapse the collected branch outputs with the
-- supplied summary function.
fanInShard ::
  ([[Post]] -> [Post]) ->
  [Shard (StateT [Post] IO) [Post] [Post]] ->
  Shard (StateT [Post] IO) [Post] [Post]
fanInShard summary shs =
  endsK
    (\xs -> put xs)
    ( do
        xs <- get
        put []
        os <- traverse (`runSubShard` xs) shs
        pure (summary os)
    )
