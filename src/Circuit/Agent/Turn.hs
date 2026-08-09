{-# LANGUAGE OverloadedStrings #-}

-- | Named runner circuits that tie free dual ends into a turn.
--
-- A turn is a /runner/ observation: it commits input, then blocks on one
-- frame.  Framing lives port-side ('Circuit.Agent.StdPorts' stream marks);
-- the queue retry is the blocking boundary.  No polling, no backoff — the
-- halt is decided by content, not inferred from quiet.
--
-- @
--   turn        e :: Loop (,) (Kleisli IO) Text Text
--   turnTimeout u e :: Loop (,) (Kleisli IO) Text (Maybe Text)
-- @
--
-- 'turnTimeout' wraps the blocking read in a deadline: a runner that cannot
-- wait forever sets a budget.  'Nothing' means the budget expired before the
-- frame arrived; partial output stays port-side, framed, for the next read.
module Circuit.Agent.Turn
  ( -- * Runner circuits
    turn,
    turnTimeout,
  )
where

import Circuit (Loop (..))
import Circuit.Ends (Ends (..), HasUnit (..), commit, emit, open)
import Control.Arrow (Kleisli (..), runKleisli)
import Data.Text (Text)
import System.Timeout (timeout)
import Prelude

-- | One turn: commit one token, then block until the next frame arrives.
--
-- Agent endomorphism @Text -> Text@ — matches the free dual on commit /
-- emit.  This blocks: if the mark never arrives, neither does the result.
turn ::
  Ends (Kleisli IO) Text Text ->
  Loop (,) (Kleisli IO) Text Text
turn e = Lift $ Kleisli $ \cmd -> do
  runKleisli (commit (conjoint e) outU) cmd
  runKleisli (emit (companion e) inU) ()
  where
    Ends _ outU = open :: Ends (Kleisli IO) () ()
    Ends inU _ = open :: Ends (Kleisli IO) () ()

-- | 'turn' under a deadline (microseconds).  'Nothing' on expiry; the
-- unarrived frame is not lost — the next emit still receives it.
turnTimeout ::
  Int ->
  Ends (Kleisli IO) Text Text ->
  Loop (,) (Kleisli IO) Text (Maybe Text)
turnTimeout us e = Lift $ Kleisli $ \cmd -> do
  runKleisli (commit (conjoint e) outU) cmd
  timeout us (runKleisli (emit (companion e) inU) ())
  where
    Ends _ outU = open :: Ends (Kleisli IO) () ()
    Ends inU _ = open :: Ends (Kleisli IO) () ()
