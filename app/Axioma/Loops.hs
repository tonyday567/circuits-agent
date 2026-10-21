{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}
-- | self-loops: S-agent, spikes, Loop Either citizen.
module Axioma.Loops
  ( loopsTopic,
  )
where

import Axioma.Common
import Algebra.Graph.Labelled qualified as LG
import Circuit.Agent
import Circuit.Category (K (..))
import Circuit.Category (K (..))
import Circuit.Category qualified as C
import Control.Concurrent.STM
import Control.Monad (unless)
import Data.Foldable (traverse_)
import Data.Function (fix)
import Data.Text (Text)
import Data.Text qualified as T

default (Text)


loopsTopic :: IO ()
loopsTopic = do
  putStrLn "S-agent self-loop"

  do
    let k = 3 :: Int
        selfEcho :: AgentS [Post Text] (Post Text)
        selfEcho = agentM $ cellToAgent $ tape $ \hist ->
          [mkPost "self" ["self"] ("echo:" <> T.pack (show (length hist))) | length hist <= k]
        seed = mkPost "human" ["self"] "start"
        drainEnd ends = go []
          where
            go acc = (readEndSTM ends >>= \a -> go (a : acc)) `orElse` pure (reverse acc)
    ends <- atomically $ openSTM Unbounded
    atomically $ writeEndSTM ends seed
    (sFinal, remaining) <- atomically $ do
      s' <- selfLoopS selfEcho [] ends
      leftover <- drainEnd ends
      pure (s', leftover)
    assert "self-loop processed seed plus k echoes" $ length sFinal == k + 1
    assert "self-loop reached quiescence" $ null remaining
    assert "self-loop state carries echoes newest-first" $
      case sFinal of
        (lastEcho : _) -> body lastEcho == "echo:3"
        _ -> False

  putStrLn "S-agent self-loop spikes"

  do
    let k = 3 :: Int
        selfEcho :: AgentS [Post Text] (Post Text)
        selfEcho = agentM $ cellToAgent $ tape $ \hist ->
          [mkPost "self" ["self"] ("echo:" <> T.pack (show (length hist))) | length hist <= k]
        seed = mkPost "human" ["self"] "start"
        drainEnd :: Poles () (K STM) a a -> STM [a]
        drainEnd ends = go []
          where
            go acc = (readEndSTM ends >>= \a -> go (a : acc)) `orElse` pure (reverse acc)

        -- \| orElse lifted to state-threading K arrows.
        orElseA :: K STM s s -> K STM s s -> K STM s s
        orElseA (K f) (K g) = K $ \s -> f s `orElse` g s

        -- \| Run a frame until the read end retries (quiescence).
        quiesce :: K STM s s -> K STM s s
        quiesce frame = fix $ \go -> (frame C..> go) `orElseA` C.id

        -- \| Spike A: one token per frame, no do/bind in the frame.
        frameToken :: AgentS s a -> Poles () (K STM) a a -> Poles () (K STM) a a -> K STM s s
        frameToken agent inbox outbox =
          K (\s -> (s,) <$> readEndSTM inbox)
            C..> K (Prelude.uncurry (stepS agent))
            C..> K (\(s', outs) -> s' <$ traverse_ (writeEndSTM outbox) outs)

        -- \| Spike B: one bundle per frame over a bundle wire.
        frameBundle :: AgentS s a -> Poles () (K STM) [a] [a] -> Poles () (K STM) [a] [a] -> K STM s s
        frameBundle agent inbox outbox =
          K (\s -> (s,) <$> readEndSTM inbox)
            C..> K (Prelude.uncurry (stepsS agent))
            C..> K (\(s', outs) -> s' <$ unless (null outs) (writeEndSTM outbox outs))

    -- Spike A: composed token frame
    (sTok, remTok) <- do
      ends <- atomically $ openSTM (Unbounded :: Queue (Post Text))
      atomically $ writeEndSTM ends seed
      atomically $ do
        s' <- runK (quiesce (frameToken selfEcho ends ends)) []
        leftover <- drainEnd ends
        pure (s', leftover)
    assert "spike A (composed token frame) processed seed plus k echoes" $ length sTok == k + 1
    assert "spike A reached quiescence" $ null remTok
    assert "spike A state carries echoes newest-first" $
      case sTok of
        (lastEcho : _) -> body lastEcho == "echo:3"
        _ -> False

    -- Spike B: composed bundle frame
    (sBun, remBun) <- do
      ends <- atomically $ openSTM (Unbounded :: Queue [Post Text])
      atomically $ writeEndSTM ends [seed]
      atomically $ do
        s' <- runK (quiesce (frameBundle selfEcho ends ends)) []
        leftover <- drainEnd ends
        pure (s', leftover)
    assert "spike B (bundle frame) processed seed plus k echoes" $ length sBun == k + 1
    assert "spike B reached quiescence" $ null remBun
    assert "spike B state carries echoes newest-first" $
      case sBun of
        (lastEcho : _) -> body lastEcho == "echo:3"
        _ -> False

    -- Agreement with the bind-spelled selfLoopS
    sRef <- do
      ends <- atomically $ openSTM (Unbounded :: Queue (Post Text))
      atomically $ writeEndSTM ends seed
      atomically $ selfLoopS selfEcho [] ends
    assert "spike A agrees with selfLoopS" $ sTok == sRef
    assert "spike B agrees with selfLoopS" $ sBun == sRef
    assert "spikes agree with each other" $ sTok == sBun

  putStrLn "Loop self-loop"

  do
    let k = 3 :: Int
        selfEcho :: AgentS [Post Text] (Post Text)
        selfEcho = agentM $ cellToAgent $ tape $ \hist ->
          [mkPost "self" ["self"] ("echo:" <> T.pack (show (length hist))) | length hist <= k]
        seed = mkPost "human" ["self"] "start"
        drainEnd :: Poles () (K STM) a a -> STM [a]
        drainEnd ends = go []
          where
            go acc = (readEndSTM ends >>= \a -> go (a : acc)) `orElse` pure (reverse acc)

    -- Loop version: bundle wire, Either-trace iteration
    endsL <- atomically $ openSTM (Unbounded :: Queue [Post Text])
    atomically $ writeEndSTM endsL [seed]
    (sLoop, remainingL) <- atomically $ do
      s' <- selfLoopL selfEcho [] endsL
      leftover <- drainEnd endsL
      pure (s', leftover)

    assert "Loop self-loop processed seed plus k echoes" $ length sLoop == k + 1
    assert "Loop self-loop reached quiescence" $ null remainingL
    assert "Loop self-loop state carries echoes newest-first" $
      case sLoop of
        (lastEcho : _) -> body lastEcho == "echo:3"
        _ -> False

    -- Reference run with the bind-spelled token self-loop
    sRef <- do
      endsRef <- atomically $ openSTM (Unbounded :: Queue (Post Text))
      atomically $ writeEndSTM endsRef seed
      atomically $ selfLoopS selfEcho [] endsRef
    assert "Loop self-loop agrees with selfLoopS" $ sLoop == sRef

-- 1792568198N
-- 1792568203N
-- 1792568338N
