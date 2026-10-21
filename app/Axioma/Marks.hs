{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | the mark grammar, halt oracles, content-decided turns.
module Axioma.Marks
  ( marksTopic,
  )
where

import Axioma.Common
import Circuit.Agent
import Circuit.Agent.Machina.Mark (markLoop, spinMark)
import Circuit.Agent.Mark (Mark (..), isEscalate, isHalt, markGlyph, markOf, parseMark)
import Circuit.Agent.Turn qualified as TurnPort
import Circuit.Category (K (..))
import Circuit.Syntax (eval)
import Control.Concurrent.Async (async, cancel)
import Control.Concurrent.STM
import Control.Monad (replicateM)
import Data.Maybe (isNothing)
import Data.Text (Text)

default (Text)

marksTopic :: IO ()
marksTopic = do
  putStrLn "mark grammar"
  do
    assert "render/parse round-trips every mark" $
      all (\m -> parseMark (markGlyph m) == Just m) [minBound .. maxBound]
    assert "parse tolerates the emoji variation selector" $
      parseMark "↩️ amend this" == Just Amendment
        && parseMark "🟢\xFE0F landed" == Just Landed
    assert "plain bodies carry no mark" $
      isNothing (parseMark "hello") && isNothing (parseMark "")
    assert "halt marks are Landed and StandDown" $
      all isHalt [Landed, StandDown]
        && not (any isHalt [Motion, Consent, Amendment, Escalate, Timeout])
    assert "⌛ parses and is not a decided quiet (🔵)" $
      parseMark "⌛ timed out after 3 empty cycles" == Just Timeout
        && markOf (mkPost "a" ["b"] "⌛ timed out") == Just Timeout
        && markOf (mkPost "a" ["b"] "⌛ timed out") /= Just StandDown
        && parseMark "🔵 standing down" == Just StandDown
    assert "escalation is its own class" $
      isEscalate Escalate && not (isEscalate Landed)
    assert "markOf reads the post body" $
      markOf (mkPost "a" ["b"] "🟢 landed") == Just Landed
        && isNothing (markOf (mkPost "a" ["b"] "no mark"))
    -- The pinned collision: legacy quiescence posts used 🟡, which is a
    -- Motion here.  That ambiguity is why quiescence moved to 🔵; this
    -- oracle stops anyone reintroducing it quietly.
    assert "legacy 🟡 quiescent body parses as Motion (the pinned collision)" $
      parseMark "🟡 quiescent after 10 empty cycles" == Just Motion

  putStrLn "mark-driven halt"
  do
    let isHaltMark p = maybe False isHalt (markOf p)
        collectStep acc p = p : acc
        seed = mkPost "human" ["self"] "seed"
        one = mkPost "human" ["self"] "one"
        two = mkPost "human" ["self"] "two"
        halt = mkPost "human" ["self"] "🟢 landed"
        writeAll ends = do
          writeEndSTM ends seed
          writeEndSTM ends one
          writeEndSTM ends two
          writeEndSTM ends halt
    endsSpin <- atomically $ openChannelSTM (Linear :: ChannelPolicy (Post Text))
    atomically $ writeAll endsSpin
    accSpin <- atomically $ runK (spinMark isHaltMark collectStep endsSpin) []
    endsLoop <- atomically $ openChannelSTM (Linear :: ChannelPolicy (Post Text))
    atomically $ writeAll endsLoop
    accLoop <- atomically $ runK (eval (markLoop isHaltMark collectStep endsLoop)) []
    assert "spinMark accumulated the three normal posts" $
      length accSpin == 3
    assert "spinMark consumed the halt mark as the halt token" $
      not (any (\p -> body p == "🟢 landed") accSpin)
    assert "markLoop agrees with spinMark" $
      accLoop == accSpin

  putStrLn "mark-loss oracle"
  do
    let normal1 = mkPost "human" ["self"] "one"
        normal2 = mkPost "human" ["self"] "two"
        halt = mkPost "human" ["self"] "🟢 landed"
        normal3 = mkPost "human" ["self"] "three"
        writeAll ends = do
          writeEndSTM ends normal1
          writeEndSTM ends normal2
          writeEndSTM ends halt
          writeEndSTM ends normal3
    linearPoles <- atomically $ openChannelSTM (Linear :: ChannelPolicy (Post Text))
    swapQPoles <- atomically $ openChannelSTM (SwapOne :: ChannelPolicy (Post Text))
    atomically $ writeAll linearPoles
    atomically $ writeAll swapQPoles
    linearTokens <- atomically $ replicateM 4 (readEndSTM linearPoles)
    swapQToken <- atomically $ readEndSTM swapQPoles
    assert "linear channel preserves the halt mark in order" $
      map body linearTokens == ["one", "two", "🟢 landed", "three"]
    assert "SwapQ channel loses the halt mark" $
      body swapQToken /= "🟢 landed"

  putStrLn "linear default oracle"
  do
    let one = mkPost "human" ["self"] "one"
        two = mkPost "human" ["self"] "two"
        three = mkPost "human" ["self"] "three"
        four = mkPost "human" ["self"] "four"
    defaultPoles <- atomically openLinearChannelSTM
    atomically $ do
      writeEndSTM defaultPoles one
      writeEndSTM defaultPoles two
      writeEndSTM defaultPoles three
      writeEndSTM defaultPoles four
    tokens <- atomically $ replicateM 4 (readEndSTM defaultPoles)
    assert "openLinearChannelSTM preserves four sequential writes in order" $
      map body tokens == ["one", "two", "three", "four"]

  putStrLn "compile-time mark-loss oracle"
  do
    let one = mkPost "human" ["self"] "one"
        two = mkPost "human" ["self"] "two"
        halt = mkPost "human" ["self"] "🟢 landed"
    haltPoles <- atomically openHaltChannel
    atomically $ do
      writeHaltChannel haltPoles one
      writeHaltChannel haltPoles two
      writeHaltChannel haltPoles halt
    tokens <- atomically $ replicateM 3 (readHaltChannel haltPoles)
    assert "HaltChannel (Linear) preserves halt mark in order" $
      map body tokens == ["one", "two", "🟢 landed"]
  -- The following would not compile:
  -- badPoles <- atomically openHaltChannel
  -- let bad = HaltChannel @'SwapOne badPoles

  putStrLn "content-decided turn"
  do
    cmdQ <- newTQueueIO
    respQ <- newTQueueIO
    let runnerPoles :: Poles () (K IO) (TurnPort.TurnToken Text) (TurnPort.TurnToken Text)
        runnerPoles = polesK (atomically . writeTQueue cmdQ) (atomically $ readTQueue respQ)
        processPoles :: Poles () (K IO) (TurnPort.TurnToken Text) (TurnPort.TurnToken Text)
        processPoles = polesK (atomically . writeTQueue respQ) (atomically $ readTQueue cmdQ)
        -- Responder: read one command and reply with the command id in thread.
        responder = do
          cmd <- runK (emit processPoles) ()
          let resp = TurnPort.TurnToken ("ack: " <> TurnPort.turnBody cmd) (TurnPort.turnThread cmd)
          runK (commit processPoles) resp
    turnLoop <- TurnPort.turn runnerPoles
    -- Run the responder in parallel with the turn, but wait for the turn
    -- result before cancelling the responder.  A raw race cancels the loser
    -- as soon as the responder writes, so the turn might not finish reading.
    responderA <- async responder
    result <- runK (eval turnLoop) "hello"
    cancel responderA
    assert "turn correlates response by thread content" $
      result == "ack: hello"

  do
    cmdQ <- newTQueueIO
    respQ <- newTQueueIO
    let runnerPoles :: Poles () (K IO) (TurnPort.TurnToken Text) (TurnPort.TurnToken Text)
        runnerPoles = polesK (atomically . writeTQueue cmdQ) (atomically $ readTQueue respQ)
        processPoles :: Poles () (K IO) (TurnPort.TurnToken Text) (TurnPort.TurnToken Text)
        processPoles = polesK (atomically . writeTQueue respQ) (atomically $ readTQueue cmdQ)
        responder = do
          cmd <- runK (emit processPoles) ()
          let resp = TurnPort.TurnToken ("ack: " <> TurnPort.turnBody cmd) (TurnPort.turnThread cmd)
          runK (commit processPoles) resp
    turnLoop <- TurnPort.turnTimeout 100000 runnerPoles
    responderA <- async responder
    result <- runK (eval turnLoop) "hello"
    cancel responderA
    assert "turnTimeout correlates response by thread content" $
      result == Just "ack: hello"

  do
    cmdQ <- newTQueueIO
    respQ <- newTQueueIO
    let runnerPoles :: Poles () (K IO) (TurnPort.TurnToken Text) (TurnPort.TurnToken Text)
        runnerPoles = polesK (atomically . writeTQueue cmdQ) (atomically $ readTQueue respQ)
    turnLoop <- TurnPort.turnTimeout 10000 runnerPoles
    result <- runK (eval turnLoop) "hello"
    assert "turnTimeout returns Nothing on expiry" $
      isNothing result
