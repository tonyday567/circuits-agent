{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | shard combinators, agent-as-shard, branch agent, token ports.
module Axioma.Shards
  ( shardsTopic,
  )
where

import Axioma.Common
import Circuit.Agent
import Circuit.Category (K (..))
import Circuit.Machine (Body (Body), Moore, Step (..))
import Circuit.Poly (monoDir)
import Circuit.Stream (These (..), uncons)
import Circuit.Tensor (unConst)
import Control.Concurrent.STM
import Control.Monad.State (State, get, gets, modify, put, runState)
import Data.Functor.Identity (Identity (..))
import Data.Maybe (isNothing)
import Data.Text (Text)
import Data.Text qualified as T
import System.Timeout (timeout)

default (Text)

shardsTopic :: IO ()
shardsTopic = do
  putStrLn "shard combinators"
  do
    let p1 = mkPost "human" ["j"] "hi"
        p2 = mkPost "j" ["human"] "ack"
        fixedShard :: Shard Identity [Post Text] [Post Text]
        fixedShard = polesK (\_ -> pure ()) (pure [p2])
        coded = codecShard (map (\p -> p {body = "in:" <> body p})) (map (\p -> p {body = body p <> ":out"})) fixedShard
        out = runIdentity (runK (close coded) [p1])
    assert "codec transforms commit and emit" $
      map body out == ["ack:out"]

    let accumShard :: Shard (State [Post Text]) [Post Text] [Post Text]
        accumShard = polesK (\ps -> modify (ps ++)) get
        composed = composeShard accumShard (suffixShard (map (\p -> p {body = body p <> "!"})) accumShard)
        (out2, st) = runState (runK (close composed) [p1]) []
    assert "compose chains shards through the monad" $
      map body out2 == ["hi!", "hi!"] && length st == 2

    -- Degeneracy warning: composePoles over allocated channels splays through
    -- the unit and serialises the intermediate wire.  An honest pipeline with
    -- a separate buffer and pump can feed a multi-read consumer; the composed
    -- end cannot.
    do
      let pairSumEnd :: TQueue Int -> IO (Shard IO Int Int)
          pairSumEnd q =
            pure $ polesK (atomically . writeTQueue q) (atomically $ (+) <$> readTQueue q <*> readTQueue q)
      e1 <- openIO Unbounded :: IO (Shard IO Int Int)
      e2 <- pairSumEnd =<< newTQueueIO
      let e12 = composeShard e1 e2
          Poles e1Write _ _ = e1
          Poles _ _ e12Read = e12
      runK e1Write 1
      runK e1Write 2
      serialResult <- timeout 100000 $ runK e12Read ()
      e1' <- openIO Unbounded :: IO (Shard IO Int Int)
      (ePipe, closePipe) <- pipeEnds e1' pairSumEnd
      let Poles e1Write' _ _ = e1'
          Poles _ _ ePipeRead = ePipe
      runK e1Write' 1
      runK e1Write' 2
      pipelinedResult <- timeout 1000000 $ runK ePipeRead ()
      closePipe
      assert "composePoles serialises allocated channels; honest pipeline does not" $
        isNothing serialResult && pipelinedResult == Just 3

  putStrLn "agent as shard"
  do
    let ack :: Agent (->) [Post Text] (Post Text) [Post Text]
        ack = cellToAgent (tape (reply "j"))
        pIn = mkPost "human" ["j"] "hi"
        -- pure closed form
        (outs, seat) = runAgentShard ack (AgentSeat [] []) [pIn]
    assert "runAgentShard one ack" $
      map body outs == ["ack: hi"] && length (asState seat) == 1

    -- same citizen as Poles (K State) — commit/emit only at the boundary
    let sh :: Shard (State (AgentSeat [Post Text] Text)) [Post Text] [Post Text]
        sh = agentShard get put ack
        (outs2, seat2) =
          runState
            (runK (close sh) [pIn])
            (AgentSeat [] [])
    assert "agentShard close matches runAgentShard" $
      outs2 == outs && asState seat2 == asState seat

    let pIn2 = mkPost "human" ["j"] "again"
        (outs3, seat3) = runAgentShard ack seat [pIn2]
    assert "agentShard keeps carrier across turns" $
      map body outs3 == ["ack: again"] && length (asState seat3) == 2

  putStrLn "O5: arity change"
  do
    let arityBreaker :: Agent (->) [Post Text] (Post Text) [Post Text]
        arityBreaker =
          cellToAgent
            ( tape
                ( \hist ->
                    let n = length hist
                     in [ mkPost "bot" ["human"] ("x" <> T.pack (show n))
                        | _ <- [1 .. n]
                        ]
                )
            )
        pIn = mkPost "human" ["j"] "a"
        pIn2 = mkPost "human" ["j"] "b"
        (outs, _) = runAgentShard arityBreaker (AgentSeat [] []) [pIn, pIn2]
    assert "O5: Agent now emits a list per input, so input length /= output length" $
      length [pIn, pIn2] /= length outs

  putStrLn "branch agent"
  do
    let liftAgent :: Moore (,) [Post Text] (->) (Post Text) [Post Text] -> Agent (->) (Bool, [Post Text]) (Post Text) [Post Text]
        liftAgent sys =
          Step $ \((tag, hist), d) ->
            let inp = monoDir d
                Body _ k o = sys
                hist' = k (hist, inp)
             in ((tag, hist'), (unConst (o hist'), ()))
        calcOnly :: Moore (,) [Post Text] (->) (Post Text) [Post Text]
        calcOnly = tape calc
        echoOnly :: Moore (,) [Post Text] (->) (Post Text) [Post Text]
        echoOnly = tape (reply "j")
        branchy :: Agent (->) (Bool, [Post Text]) (Post Text) [Post Text]
        branchy = branchAgent fst (liftAgent calcOnly) (liftAgent echoOnly)
        pCalc = mkPost "human" ["j"] "1 2 3"
        pEcho = mkPost "human" ["j"] "hello"

    -- Mode True selects the calc branch.
    let (outsCalc, seatCalc) = runAgentShard branchy (AgentSeat (True, []) []) [pCalc]
    assert "branch agent mode True -> calc output" $
      map body outsCalc == ["6"]
    assert "branch agent mode True preserves tag" $
      fst (asState seatCalc)

    -- Mode False selects the echo branch.
    let (outsEcho, seatEcho) = runAgentShard branchy (AgentSeat (False, []) []) [pEcho]
    assert "branch agent mode False -> echo output" $
      map body outsEcho == ["ack: hello"]
    assert "branch agent mode False preserves tag" $
      not (fst (asState seatEcho))

  putStrLn "port (token seat)"
  do
    let ack :: Agent (->) [Post Text] (Post Text) [Post Text]
        ack = cellToAgent (tape (reply "j"))
        pIn = mkPost "human" ["j"] "hi"
        -- agent as list shard, then token seat via stream buffers
        sh :: Shard (State (AgentSeat [Post Text] Text, [Post Text], [Post Text])) [Post Text] [Post Text]
        sh =
          agentShard
            (gets (\(seat, _, _) -> seat))
            (\seat -> modify (\(_, i, o) -> (seat, i, o)))
            ack
        port :: Port (State (AgentSeat [Post Text] Text, [Post Text], [Post Text])) Text
        port =
          portShard
            (gets (\(_, i, _) -> i))
            (\i -> modify (\(seat, _, o) -> (seat, i, o)))
            (gets (\(_, _, o) -> o))
            (\o -> modify (\(seat, i, _) -> (seat, i, o)))
            sh
        (pOut, (seat', inB, outB)) =
          runState
            (runK (close port) pIn)
            (AgentSeat [] [], [], [])
    assert "port close: one Post in, one Post out" $
      body pOut == "ack: hi"
    assert "port drains stream buffers on close" $
      null inB && null outB && length (asState seat') == 1

    let pIn2 = mkPost "human" ["j"] "again"
        (pOut2, (seat2, _, _)) =
          runState
            (runK (close port) pIn2)
            (seat', [], [])
    assert "port keeps agent carrier across token turns" $
      body pOut2 == "ack: again" && length (asState seat2) == 2

    assert "uncons matches Uncons on lists" $
      let u :: [Int] -> These Int [Int]
          u = uncons
       in u [] == That []
            && u [1] == This 1
            && u [1, 2, 3] == These 1 [2, 3]
