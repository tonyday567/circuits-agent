{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

-- | Effectful 'Circuit.Poles.Poles' constructors and queueing strategies.
--
-- This module lives in @circuits-agent@ because it needs @STM@.  Core
-- 'Circuit.Poles' is pure in the base arrow; the queue implementations here
-- are one possible effectful instantiation, placed beside their consumers
-- rather than forcing the core library to depend on @stm@.
module Circuit.Agent.Ends
  ( -- * Queue strategies
    Queue (..),

    -- * Channel policies (mediator-configured buffering)
    ChannelPolicy (..),
    openChannel,
    openChannelSTM,

    -- * Linear default channels
    openLinearChannel,
    openLinearChannelSTM,

    -- * Halt-mark channels (compile-time linearity witness)
    HaltChannel (..),
    IsLinear,
    openHaltChannel,
    writeHaltChannel,
    readHaltChannel,

    -- * STM @Ends@
    openSTM,

    -- * IO @Ends@
    openIO,

    -- * Honest composition
    pipeEnds,
  )
where

import Circuit.Category (K (..))
import Circuit.Poles (HasDual (..), Poles (..), commit, companion, conjoint, emit, open, polesK, splay0)
import Control.Applicative
import Control.Concurrent.Async (async, cancel)
import Control.Concurrent.STM
import Control.Monad (forever, void)
import Data.Kind (Constraint, Type)
import GHC.TypeLits (ErrorMessage (..), TypeError)
import Prelude

-- | How messages are queued between producer and consumer.
data Queue a
  = -- | Unbounded FIFO queue.
    Unbounded
  | -- | Bounded FIFO with backpressure (write blocks when full).
    Bounded Int
  | -- | Single-slot buffer (write blocks when full).
    Single
  | -- | Single-slot buffer, overwrite-on-full.
    -- Write always succeeds; read empties.
    SwapQ
  | -- | Always holds the latest value (overwrites, never blocks).
    Latest a
  | -- | Like @Bounded@ but drops oldest when full.
    Newest Int
  deriving (Show, Eq)

-- | A channel policy names the residual mediator that governs an effectful
-- channel.  This is the Track-B relocation of the old @Queue@ annotation:
-- the policy is a value passed at allocation time, not a field of the
-- channel type.  The constructors match the ?-modality vocabulary from the
-- B0 spike; 'Linear' is the empty-residual default and the only policy on
-- which halt marks are safe.
data ChannelPolicy a
  = -- | Unbounded FIFO: empty residual, preserves every token in order.
    -- This is the effectful face of a linear process.
    Linear
  | -- | Single-slot buffer with backpressure (write blocks when full).
    SingleSlot
  | -- | Single-slot overwrite: write always succeeds, read empties.
    -- A weakening policy that can drop a halt mark.
    SwapOne
  | -- | Always holds the latest value; requires a seed for the first read.
    -- A weakening policy suitable for diagnostics, not for halt marks.
    LatestValue a
  | -- | Bounded FIFO with backpressure.
    BoundedN Int
  | -- | Bounded FIFO dropping oldest when full.
    -- A weakening policy suitable for bounded diagnostics.
    NewestN Int
  deriving (Show, Eq)

-- | Convert a channel policy to the concrete queue strategy that implements it.
policyToQueue :: ChannelPolicy a -> Queue a
policyToQueue = \case
  Linear -> Unbounded
  SingleSlot -> Single
  SwapOne -> SwapQ
  LatestValue a -> Latest a
  BoundedN n -> Bounded n
  NewestN n -> Newest n

-- | Open a channel policy as IO @Poles@.
openChannel :: ChannelPolicy a -> IO (Poles (K IO) a a)
openChannel = openIO . policyToQueue

-- | Open a channel policy as STM @Poles@.
openChannelSTM :: ChannelPolicy a -> STM (Poles (K STM) a a)
openChannelSTM = openSTM . policyToQueue

-- | Open a linear channel as IO @Poles@.
--
-- 'Linear' is the default policy: unbounded FIFO, empty residual, preserves
-- every token in order.  This is the effectful face of a linear process.
openLinearChannel :: IO (Poles (K IO) a a)
openLinearChannel = openChannel Linear

-- | Open a linear channel as STM @Poles@.
openLinearChannelSTM :: STM (Poles (K STM) a a)
openLinearChannelSTM = openChannelSTM Linear

-- | Type-level witness that a channel policy is linear.
--
-- Only 'Linear' is allowed to carry halt marks; any other policy produces a
-- compile-time type error.
type family IsLinear (p :: ChannelPolicy a) :: Constraint where
  IsLinear 'Linear = ()
  IsLinear p = TypeError ('Text "only 'Linear' channels can carry halt marks")

-- | A channel statically known to be linear.
--
-- The index @p :: ChannelPolicy a@ is checked by 'IsLinear' at construction
-- time.  Attempting to build a 'HaltChannel' with a non-linear policy fails
-- to typecheck.
type HaltChannel :: ChannelPolicy a -> Type
data HaltChannel p where
  HaltChannel :: (IsLinear p) => Poles (K STM) a a -> HaltChannel (p :: ChannelPolicy a)

-- | Open a halt-mark channel.  This is 'openLinearChannelSTM' with a
-- type-level certificate.
openHaltChannel :: STM (HaltChannel 'Linear)
openHaltChannel = HaltChannel <$> openLinearChannelSTM

-- | Write a token to a halt-mark channel.
writeHaltChannel :: forall a (p :: ChannelPolicy a). HaltChannel p -> a -> STM ()
writeHaltChannel (HaltChannel ends) = runK (commit (conjoint ends) haltOut)
  where
    haltOut = companion (unitEndsSTM :: Poles (K STM) () ())

-- | Read a token from a halt-mark channel.
readHaltChannel :: forall a (p :: ChannelPolicy a). HaltChannel p -> STM a
readHaltChannel (HaltChannel ends) = runK (emit (companion ends) haltIn) ()
  where
    haltIn = conjoint (unitEndsSTM :: Poles (K STM) () ())

-- | Unit ends specialised to 'K STM'.
unitEndsSTM :: Poles (K STM) () ()
unitEndsSTM = polesK (const (pure ())) (pure ())

-- | Internal STM primitive for a queue strategy.
--
-- Returns the raw write/read actions used by 'openSTM'.  Not exported;
-- the canonical API is 'openSTM'.
endsSTM :: Queue a -> STM (a -> STM (), STM a)
endsSTM = \case
  Bounded n -> do
    q <- newTBQueue (fromIntegral n)
    pure (writeTBQueue q, readTBQueue q)
  Unbounded -> do
    q <- newTQueue
    pure (writeTQueue q, readTQueue q)
  Single -> do
    m <- newEmptyTMVar
    pure (putTMVar m, takeTMVar m)
  SwapQ -> do
    v <- newEmptyTMVar
    let write x = tryPutTMVar v x >>= \case True -> pure (); False -> void (swapTMVar v x)
    pure (write, takeTMVar v)
  Latest a -> do
    t <- newTVar a
    pure (writeTVar t, readTVar t)
  Newest n -> do
    q <- newTBQueue (fromIntegral n)
    let write x = writeTBQueue q x <|> (tryReadTBQueue q *> write x)
    pure (write, readTBQueue q)

-- | Open a queue strategy as STM @Poles@.
--
-- Allocates STM primitives and returns a matched pair of ends sharing
-- the same mutable channel.  Both ends live in 'STM', so you can compose
-- operations across channels in a single 'atomically' block.
openSTM :: Queue a -> STM (Poles (K STM) a a)
openSTM q = do
  (write, read') <- endsSTM q
  pure (polesK write read')

-- | Open a queue strategy as IO @Poles@.
--
-- Like 'openSTM', but each primitive operation is wrapped in its own
-- 'atomically'.  You cannot batch multiple writes or a write-plus-read
-- into a single STM transaction; for that use 'openSTM' and wrap in
-- 'atomically' yourself.
openIO :: Queue a -> IO (Poles (K IO) a a)
openIO q = do
  e <- atomically (openSTM q)
  let (K write, K receive) = splay0 e
  pure (polesK (atomically . write) (atomically (receive ())))

-- | Honest sequential composition of two allocated ends via an intermediate
-- queue and a pump.
--
-- @pipeEnds e1 makeE2@ allocates a queue of @b@ values, builds the right end
-- around that queue with @makeE2@, and starts a pump that moves values from
-- @e1@ into the right end.  The returned 'Poles' uses @e1@ for input and the
-- built right end for output; the close action cancels the pump.
--
-- This is the coend-style composition that 'composePoles' cannot express: the
-- intermediate carrier is a real queue (the residual's home) rather than the
-- unit type, so a multi-read consumer can accumulate inputs before emitting.
pipeEnds ::
  forall a b c.
  Poles (K IO) a b ->
  (TQueue b -> IO (Poles (K IO) b c)) ->
  IO (Poles (K IO) a c, IO ())
pipeEnds e1 makeE2 = do
  q <- newTQueueIO
  e2 <- makeE2 q
  let unitEnds :: Poles (K IO) () ()
      unitEnds = open
      readFromE1 :: IO b
      readFromE1 = runK (emit (companion e1) (conjoint unitEnds)) ()
      writeToE2 :: b -> IO ()
      writeToE2 = runK (commit (conjoint e2) (companion unitEnds))
  pump <- async . forever $ do
    x <- readFromE1
    writeToE2 x
  pure (Poles (conjoint e1) (companion e2), cancel pump)
