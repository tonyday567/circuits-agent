{-# LANGUAGE OverloadedStrings #-}

-- | Named runner circuits that tie free dual ends into a turn.
--
-- A turn is a /runner/ observation: it commits input, then polls the emit
-- end until a boundary predicate is satisfied or a timeout expires.  The
-- ends themselves live elsewhere (e.g. 'stdioEnds'); the tying schedule
-- lives here.
--
-- @
--   closeOnce cfg e  :: Loop (,) (Kleisli IO) [Text] (Maybe [Text])
--   turnUntil cfg p e :: Loop (,) (Kleisli IO) [Text] (Maybe [Text])
-- @
--
-- Both return 'Nothing' when the timeout expires before the boundary is
-- reached.  Partial output is discarded on timeout (runner choice); use a
-- raw poll emit if you need every line.
module Circuit.Agent.Turn
  ( -- * Turn configuration
    TurnConfig (..),
    defaultTurnConfig,

    -- * Runner circuits
    closeOnce,
    turnUntil,
  )
where

import Circuit (Loop (..))
import Circuit.Ends (Ends (..), HasUnit (..), commit, emit, open)
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Concurrent (threadDelay)
import Data.Text (Text)
import Data.Text qualified as T

-- | Configuration for a single turn.
data TurnConfig = TurnConfig
  { -- | Timeout in microseconds.
    turnTimeoutUs :: Int,
    -- | End-of-turn marker used by 'closeOnce'.
    turnEofTag :: Text
  }
  deriving (Show, Eq)

-- | Sensible defaults: 15 second timeout, @"<EOF>"@ end-of-turn tag.
defaultTurnConfig :: TurnConfig
defaultTurnConfig =
  TurnConfig
    { turnTimeoutUs = 15_000_000,
      turnEofTag = "<EOF>"
    }

-- | One turn: commit input lines, then emit until the boundary
-- predicate succeeds or the timeout expires.
--
-- Agent endomorphism @[Text] -> Maybe [Text]@ — matches the free dual
-- on commit / emit.
turnUntil ::
  TurnConfig ->
  (Text -> Bool) ->
  Ends (Kleisli IO) [Text] [Text] ->
  Loop (,) (Kleisli IO) [Text] (Maybe [Text])
turnUntil cfg isBoundary e = Lift $ Kleisli $ \cmds -> do
  runKleisli (commit (conjoint e) outU) cmds
  poll 0 [] 10_000
  where
    Ends _ outU = open :: Ends (Kleisli IO) () ()
    timeoutUs = turnTimeoutUs cfg
    poll elapsed acc delay = do
      news <- runKleisli (emit (companion e) inU) ()
      let acc' = acc <> news
      if any isBoundary news
        then pure (Just acc')
        else do
          let elapsed' = elapsed + delay
          if elapsed' >= timeoutUs
            then pure Nothing
            else do
              threadDelay delay
              let delay' = min 500_000 (floor (fromIntegral delay * 1.5 :: Double))
              poll elapsed' acc' delay'
    Ends inU _ = open :: Ends (Kleisli IO) () ()

-- | One turn that closes when the configured 'turnEofTag' appears in the
-- emitted stream.
closeOnce ::
  TurnConfig ->
  Ends (Kleisli IO) [Text] [Text] ->
  Loop (,) (Kleisli IO) [Text] (Maybe [Text])
closeOnce cfg = turnUntil cfg (T.isInfixOf (turnEofTag cfg))
