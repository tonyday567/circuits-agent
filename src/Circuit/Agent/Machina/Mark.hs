{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Mark-driven halt machinery for STM agents.
--
-- This module graduates the first machina probe-station combinator into
-- @circuits-agent@.  The design principle: the builder posts its silence as a
-- token, and the runner halts on that read.  There is no 'orElse' fallback —
-- absence is not an opinion here.  If the mark never arrives, the runner
-- blocks; the halt is decided by content, not inferred from quiet.
--
-- The 'Loop Either' form pushes the same halt to the surface of a composition:
-- 'Left' = continue, 'Right' = halt.  This makes the mark-halt a trace citizen,
-- with the continuation folded away by 'trace'.
--
-- The rest of the machina probe station (quiet ends, sealed ends, stream ends)
-- stays in @circuits-agent-machina@ until a consumer appears here.
module Circuit.Agent.Machina.Mark
  ( -- * Mark-driven halt
    spinMark,
    markLoop,
  )
where

import Circuit (trace)
import Circuit.Ends (Ends (..), emit, endsK)
import Circuit.Loop (Loop (..))
import Control.Arrow (Kleisli (..))
import Control.Concurrent.STM (STM)
import Data.Function (fix)

-- | Unit ends for plugging the unused slot when reading or writing one end.
endsU :: Ends (Kleisli STM) () ()
endsU = endsK (const (pure ())) (pure ())

-- | Spin until the mark is /read/: the builder posts its silence as a token,
-- and the runner halts on that read.  No 'orElse' — absence is not an opinion
-- here.  If the mark never arrives, this blocks; the halt is decided by
-- content, not inferred from quiet.
--
-- Contrast a plain 'retry'-driven spin: that frame drains the queue and falls
-- through on absence; mark-driven halt is decisive mid-stream — tokens after
-- the mark are never consumed.
spinMark :: (a -> Bool) -> (s -> a -> s) -> Ends (Kleisli STM) a a -> Kleisli STM s s
spinMark isMark step e = fix $ \go -> Kleisli $ \s -> do
  a <- runKleisli (emit (companion e) (conjoint endsU)) ()
  if isMark a
    then pure s
    else runKleisli go (step s a)

-- | One mark frame in the 'Either'-trace halt alphabet: 'Left' = continue,
-- 'Right' = halt.  The read is committed before the decision, so the mark is
-- consumed either way.
markFrame :: (a -> Bool) -> (s -> a -> s) -> Ends (Kleisli STM) a a -> Kleisli STM (Either s s) (Either s s)
markFrame isMark step e = Kleisli $ \es -> do
  let s = either id id es
  a <- runKleisli (emit (companion e) (conjoint endsU)) ()
  pure
    ( if isMark a
        then Right s
        else Left (step s a)
    )

-- | The mark-halt pushed to the surface of a composition: a @Loop Either@
-- citizen.  The halt decision travels as data through the channel and the
-- 'trace' folds the continuation away — the runner is a value, not a loop
-- spelled in 'fix'.
markLoop :: (a -> Bool) -> (s -> a -> s) -> Ends (Kleisli STM) a a -> Loop Either (Kleisli STM) s s
markLoop isMark step e = trace (Lift (markFrame isMark step e))
