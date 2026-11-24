{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | ends combinators, agent-as-ends, branch agent, token ports.
module Axioma.Shards
  ( shardsTopic,
  )
where

import Axioma.Common
import Circuit.Agent
import Circuit.Body (Body (Body), iomap, pipe)
import Circuit.Category (K (..))
import Circuit.Machine (Moore (Moore))
import Circuit.Stream (These (..), uncons)
import Control.Concurrent.STM
import Control.Exception (IOException, try)
import Data.Functor.Identity (Identity (..))
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.Maybe (isNothing)
import Data.Text (Text)
import Data.Text qualified as T
import System.Timeout (timeout)

default (Text)

shardsTopic :: IO ()
shardsTopic = do
  putStrLn "Poles combinators"
  do
    let p1 = mkPost "human" ["j"] "hi"
        p2 = mkPost "j" ["human"] "ack"
        fixedPoles :: Poles () (K Identity) [Post Text] [Post Text]
        fixedPoles = polesK (\_ -> pure ()) (pure [p2])
        coded =
          iomap
            (K (pure . map (\p -> p {body = "in:" <> body p})))
            (K (pure . map (\p -> p {body = body p <> ":out"})))
            fixedPoles
        out = runIdentity (runK (close coded) [p1])
    assert "iomap transforms commit and emit" $
      map body out == ["ack:out"]

    do
      ref <- newIORef []
      let accumPoles :: Poles () (K IO) [Post Text] [Post Text]
          accumPoles = polesK (\ps -> modifyIORef' ref (ps ++)) (readIORef ref)
          suffixed =
            iomap
              (K pure)
              (K (pure . map (\p -> p {body = body p <> "!"})))
              accumPoles
          composed = pipe accumPoles suffixed
      out2 <- runK (close composed) [p1]
      st <- readIORef ref
      assert "pipe chains Poles through the carrier" $
        map body out2 == ["hi!", "hi!"] && length st == 2

    -- Degeneracy warning: pipe over allocated channels splays through
    -- the unit and serialises the intermediate wire.  An honest pipeline with
    -- a separate buffer and pump can feed a multi-read consumer; the composed
    -- end cannot.
    do
      let pairSumEnd :: TQueue Int -> IO (Poles () (K IO) Int Int)
          pairSumEnd q =
            pure $ polesK (atomically . writeTQueue q) (atomically $ (+) <$> readTQueue q <*> readTQueue q)
      e1 <- openIO Unbounded :: IO (Poles () (K IO) Int Int)
      e2 <- pairSumEnd =<< newTQueueIO
      let e12 = pipe e1 e2
          Poles e1Write _ _ = e1
          Poles _ _ e12Read = e12
      runK e1Write 1
      runK e1Write 2
      serialResult <- timeout 100000 $ runK e12Read ()
      e1' <- openIO Unbounded :: IO (Poles () (K IO) Int Int)
      (ePipe, closePipe) <- pipeEnds e1' pairSumEnd
      let Poles e1Write' _ _ = e1'
          Poles _ _ ePipeRead = ePipe
      runK e1Write' 1
      runK e1Write' 2
      pipelinedResult <- timeout 1000000 $ runK ePipeRead ()
      closePipe
      assert "pipe serialises allocated channels; honest pipeline does not" $
        isNothing serialResult && pipelinedResult == Just 3

  putStrLn "Body commit/emit independence"
  do
    let p1 = mkPost "human" ["body"] "first"
        p2 = mkPost "human" ["body"] "second"
        p3 = mkPost "human" ["body"] "third"
        replyPost x = mkPost "body" ["human"] x
        emissions = [[], [replyPost "one"], [replyPost "two-a", replyPost "two-b"], [replyPost "final"]]
        scripted :: [[Post Text]] -> Agent ([Text], [[Post Text]], Int)
        scripted script =
          Body
            (K $ \first -> pure (AgentChannel ([body first], script, 0) Continue))
            ( K $ \(AgentChannel (seen, rest, n) _, post_) ->
                pure (AgentChannel (seen <> [body post_], rest, n) Continue)
            )
            ( K $ \(AgentChannel (seen, rest, n) _) ->
                case rest of
                  [] -> pure (AgentChannel (seen, [], n) Done, [])
                  (outs : more) ->
                    pure
                      ( AgentChannel (seen, more, n + 1) (if null more then Done else Continue),
                        outs
                      )
            )
        Body birth commit' emit' = scripted emissions
    born <- runK birth p1
    (quiet, quietOuts) <- runK emit' born
    committed1 <- runK commit' (quiet, p2)
    committed2 <- runK commit' (committed1, p3)
    observedRef <- newIORef []
    let observe channel = do
          (channel', outs) <- runK emit' channel
          modifyIORef' observedRef (<> [map body outs])
          pure (channel', outs)
    (continuing1, firstOuts) <- observe committed2
    assert "one emission is observable while the channel continues" $
      agentLifecycle continuing1 == Continue && map body firstOuts == ["one"]
    (continuing2, secondOuts) <- observe continuing1
    observedMid <- readIORef observedRef
    assert "incremental output retains emission boundaries and order" $
      agentLifecycle continuing2 == Continue
        && map body secondOuts == ["two-a", "two-b"]
        && observedMid == [["one"], ["two-a", "two-b"]]
    (finalDirect, finalOuts) <- observe continuing2
    observedFinal <- readIORef observedRef
    assert "direct final output arrives beside Done" $
      agentLifecycle finalDirect == Done
        && map body finalOuts == ["final"]
        && observedFinal == [["one"], ["two-a", "two-b"], ["final"]]
    (finalChannel, drained) <- drainAgent (scripted emissions) committed2
    compatible <- runAgent (scripted emissions) [p1, p2, p3]
    empty <- runAgent (scripted emissions) []
    assert "an independent emit can be quiet before later commits" $
      null quietOuts && agentLifecycle quiet == Continue
    assert "commits retain independent inputs in order" $
      let AgentChannel (seen, _, _) _ = finalChannel
       in seen == ["first", "second", "third"]
    assert "drain passes quiet, single, repeated, and final Done output in order" $
      map body drained == ["one", "two-a", "two-b", "final"]
    assert "final output is retained beside Done after four emits" $
      agentLifecycle finalChannel == Done
        && (let AgentChannel (_, rest, n) _ = finalChannel in null rest && n == 4)
    assert "compatibility init/commit/drain agrees with independent legs" $
      compatible == drained && map body drained == concat observedFinal
    assert "compatibility requires a first post for init" $
      null empty

  putStrLn "Body failure after observable output"
  do
    let p1 = mkPost "human" ["body"] "start"
        replyPost x = mkPost "body" ["human"] x
        failing :: Agent Int
        failing =
          Body
            (K $ \_ -> pure (AgentChannel 0 Continue))
            (K $ \(AgentChannel n _, _) -> pure (AgentChannel n Continue))
            ( K $ \(AgentChannel n _) ->
                case n of
                  0 -> pure (AgentChannel 1 Continue, [replyPost "before-failure"])
                  _ -> ioError (userError "intentional body emit failure")
            )
        Body birth _ emit' = failing
    born <- runK birth p1
    (continuing, beforeFailure) <- runK emit' born
    failure <-
      try (runK emit' continuing) ::
        IO (Either IOException (AgentChannel Int, [Post Text]))
    assert "output before failure is observable beside Continue" $
      agentLifecycle continuing == Continue && map body beforeFailure == ["before-failure"]
    assert "an emit failure remains an explicit IO exception" $
      case failure of
        Left _ -> True
        Right _ -> False

  putStrLn "agent as buffered Poles"
  do
    let ack :: PureAgent [Post Text] (Post Text) [Post Text]
        ack = cellToAgent (tape (reply "j"))
        pIn = mkPost "human" ["j"] "hi"
        -- pure closed form
        (outs, seat) = runAgentPoles ack (AgentSeat [] []) [pIn]
    assert "runAgentPoles one ack" $
      map body outs == ["ack: hi"] && length (asState seat) == 1

    -- same citizen through a real carrier (IORef) — commit/emit only at the
    -- boundary, matching the pure runner
    do
      ref <- newIORef (AgentSeat [] [] :: AgentSeat [Post Text] Text)
      let sh :: Poles () (K IO) [Post Text] [Post Text]
          sh = agentPoles (readIORef ref) (\st -> writeIORef ref st) ack
      outs2 <- runK (close sh) [pIn]
      seat2 <- readIORef ref
      assert "agentPoles close matches runAgentPoles" $
        outs2 == outs && asState seat2 == asState seat

    let pIn2 = mkPost "human" ["j"] "again"
        (outs3, seat3) = runAgentPoles ack seat [pIn2]
    assert "agentPoles keeps carrier across turns" $
      map body outs3 == ["ack: again"] && length (asState seat3) == 2

  putStrLn "O5: arity change"
  do
    let arityBreaker :: PureAgent [Post Text] (Post Text) [Post Text]
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
        (outs, _) = runAgentPoles arityBreaker (AgentSeat [] []) [pIn, pIn2]
    assert "O5: Agent now emits a list per input, so input length /= output length" $
      length [pIn, pIn2] /= length outs

  putStrLn "branch agent"
  do
    let liftAgent :: Bool -> Moore (,) [Post Text] (->) (Post Text) [Post Text] -> PureAgent (Bool, [Post Text]) (Post Text) [Post Text]
        liftAgent tag (Moore _ k o) =
          Body
            (\inp -> (tag, k ([], inp)))
            (\((tg, hist), inp) -> (tg, k (hist, inp)))
            (\ch@(_, hist) -> (ch, o hist))
        calcOnly :: Moore (,) [Post Text] (->) (Post Text) [Post Text]
        calcOnly = tape calc
        echoOnly :: Moore (,) [Post Text] (->) (Post Text) [Post Text]
        echoOnly = tape (reply "j")
        branchy :: PureAgent (Bool, [Post Text]) (Post Text) [Post Text]
        branchy = branchAgent fst (liftAgent True calcOnly) (liftAgent False echoOnly)
        pCalc = mkPost "human" ["j"] "1 2 3"
        pEcho = mkPost "human" ["j"] "hello"

    -- Mode True selects the calc branch.
    let (outsCalc, seatCalc) = runAgentPoles branchy (AgentSeat (True, []) []) [pCalc]
    assert "branch agent mode True -> calc output" $
      map body outsCalc == ["6"]
    assert "branch agent mode True preserves tag" $
      fst (asState seatCalc)

    -- Mode False selects the echo branch.
    let (outsEcho, seatEcho) = runAgentPoles branchy (AgentSeat (False, []) []) [pEcho]
    assert "branch agent mode False -> echo output" $
      map body outsEcho == ["ack: hello"]
    assert "branch agent mode False preserves tag" $
      not (fst (asState seatEcho))

  putStrLn "port (token seat)"
  do
    let ack :: PureAgent [Post Text] (Post Text) [Post Text]
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

  putStrLn "ioAgent container dial"
  do
    let a = mkPost "alice" [] "a"
        b = mkPost "bob" [] "b"
        c = mkPost "carol" [] "c"
        outPost x = x {body = "out:" <> body x}
        sh = ioAgent (pure . map outPost)
        runBag ins = toBag <$> runAgent sh ins
    bag1 <- runBag [a, b, c]
    bag2 <- runBag [c, a, b]
    assert "permuting input preserves output bag" $ bag1 == bag2
