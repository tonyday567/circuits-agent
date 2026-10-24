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
import Data.Functor.Identity (Identity (..))
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
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

    do
      ref <- newIORef []
      let accumShard :: Shard IO [Post Text] [Post Text]
          accumShard = polesK (\ps -> modifyIORef' ref (ps ++)) (readIORef ref)
          composed = composeShard accumShard (suffixShard (map (\p -> p {body = body p <> "!"})) accumShard)
      out2 <- runK (close composed) [p1]
      st <- readIORef ref
      assert "compose chains shards through the carrier" $
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

    -- same citizen through a real carrier (IORef) — commit/emit only at the
    -- boundary, matching the pure runner
    do
      ref <- newIORef (AgentSeat [] [] :: AgentSeat [Post Text] Text)
      let sh :: Shard IO [Post Text] [Post Text]
          sh = agentShard (readIORef ref) (\seat -> writeIORef ref seat) ack
      outs2 <- runK (close sh) [pIn]
      seat2 <- readIORef ref
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
        (pOut, ps1) = runPort ack (PortSeat (AgentSeat [] []) [] []) pIn
    assert "port close: one Post in, one Post out" $
      fmap body pOut == Just "ack: hi"
    assert "port drains stream buffers on close" $
      null (psIn ps1) && null (psOut ps1)
    assert "port carrier holds the input" $
      length (asState (psAgent ps1)) == 1

    let pIn2 = mkPost "human" ["j"] "again"
        (pOut2, ps2) = runPort ack ps1 pIn2
    assert "port keeps agent carrier across token turns" $
      fmap body pOut2 == Just "ack: again" && length (asState (psAgent ps2)) == 2

    assert "uncons matches Uncons on lists" $
      let u :: [Int] -> These Int [Int]
          u = uncons
       in u [] == That []
            && u [1] == This 1
            && u [1, 2, 3] == These 1 [2, 3]

  putStrLn "ioShard container dial"
  do
    let a = mkPost "alice" [] "a"
        b = mkPost "bob" [] "b"
        c = mkPost "carol" [] "c"
        outPost x = x {body = "out:" <> body x}
        sh = ioShard (pure . map outPost)
        runBag sh' ins = do
          (outs, _) <- closeShardIO sh' ins []
          pure (toBag outs)
    bag1 <- runBag sh [a, b, c]
    bag2 <- runBag sh [c, a, b]
    assert "permuting input preserves output bag" $ bag1 == bag2
