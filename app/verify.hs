{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Circuit.Agent
import Circuit.Agent.Delivery
  ( deliveryMatrix,
    isNilpotent,
    matrixPowers,
    topologyMatrix,
  )
import Circuit.Agent.Population
  ( HPopAgent (..),
    HPopEvent (..),
    PopEvent (..),
    applyPopEvents,
    birthHPopAgent,
    loopHPop,
    loopPop,
    loopsPop,
  )
import Circuit.Stream (These (..), Uncons, uncons)
import Circuit.Poly (Eval (..), Mono, System (..), fromEvalSystem, monoDir)
import Circuit.Poly.Process (iterateSystem, runSystem)
import Circuit.Layer (run)
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Monad.State (State, get, gets, modify, put, runState)
import Data.Functor.Identity (Identity (..))
import Data.List (find, foldl', sort)
import Data.Text (Text)
import Data.Text qualified as T
import Harpie.NumHask.Matrix (Matrix, fromLists, matPlus, starMatrix, toLists)
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

mkPost :: Text -> Text -> Text -> Text -> Post
mkPost = Post

peek :: [Post] -> Post
peek [] = error "verify: empty history"
peek (p : _) = p

reply :: Text -> [Post] -> [Post]
reply name hist =
  [mkPost name (author (peek hist)) (channel (peek hist)) ("ack: " <> body (peek hist))]

-- | New posts in @new@ compared to @old@, oldest first.
diffLog :: [Post] -> [Post] -> [Post]
diffLog old new = reverse (take (length new - length old) new)

-- | Route one post to a state's inbox if it is addressed to the owner.
routeToInbox :: Post -> AgentState [Post] [Post] -> AgentState [Post] [Post]
routeToInbox p st =
  if addr p == inboxWho (asInbox st)
    then st {asInbox = appendInbox p (asInbox st)}
    else st

-- | Feed oldest-first posts into a state's inbox.
feedState :: [Post] -> AgentState [Post] [Post] -> AgentState [Post] [Post]
feedState posts st = foldl' (flip routeToInbox) st posts

-- | Seed an agent state from the addressed posts in a log.
seedState :: Text -> [Post] -> AgentState [Post] [Post]
seedState who lg = feedState (watch who lg) (emptyAgentState who)

-- | Addressed posts for @who@ in @lg@ that are not already in the carrier.
newFor :: Text -> [Post] -> AgentState [Post] [Post] -> [Post]
newFor who lg st = filter (`notElem` asCarrier st) (watch who lg)

-- | Parallel reduction: every agent runs against the *same* input log, and
-- all emitted posts are appended to that log.  This is the schedule-independent
-- baseline that O8 compares against the round-robin 'loop'.
runParallel :: [(Text, Agent [Post])] -> [Post] -> [Post]
runParallel roster lg = foldl' (flip post) lg outputs
  where
    outputs = concatMap (\(who, agent) -> beh agent [] (watch who lg)) roster

main :: IO ()
main = do
  putStrLn "circuits-agent oracle tests"

  -------------------------------------------------------------------------
  -- The pretense: carrier is invisible at the interface.
  -------------------------------------------------------------------------
  putStrLn "the pretense"
  do
    let sumAgent :: System (->) Int (Mono Int Int)
        sumAgent = fromEvalSystem $ \s -> EP (EK s, EE (+ s))
    assert "tape sum == [1,3,6]" $
      iterateSystem (tape sum) [] [1, 2, 3 :: Int] == [1, 3, 6]
    assert "sumAgent == [1,3,6]" $
      iterateSystem sumAgent 0 [1, 2, 3 :: Int] == [1, 3, 6]

    -- O1: tape is the anamorphism that applies f to each input prefix.
    -- iterateSystem emits f applied to the state after each input, i.e. the
    -- non-empty prefixes of the input stream (newest-first), so we drop the
    -- initial empty prefix from scanl.
    let xs = [1, 2, 3 :: Int]
    assert "O1: tape f xs == map f (drop 1 (scanl (flip (:)) [] xs))" $
      iterateSystem (tape sum) [] xs == map sum (drop 1 (scanl (flip (:)) [] xs))

  -------------------------------------------------------------------------
  -- O2: coalgebra homomorphism (compaction invariance as behaviour preservation)
  -------------------------------------------------------------------------
  putStrLn "O2: coalgebra homomorphism"
  do
    let p1 = mkPost "human" "j" "alpha" "one"
        p2 = mkPost "human" "j" "alpha" "two"
        p3 = mkPost "human" "j" "alpha" "three"
        ins = [p1, p2, p3]
        f = reply "j"
        h = take 1
        sys1 :: Agent [Post]
        sys1 = tape f
        sys2 :: Agent [Post]
        sys2 = tape (f . h)
    assert "O2: summarizer h preserves behaviour" $
      beh sys2 (h []) ins == beh sys1 [] ins

  -------------------------------------------------------------------------
  -- S3: behaviour is functorial over stream concatenation.
  -------------------------------------------------------------------------
  putStrLn "S3: behaviour functoriality"
  do
    let p1 = mkPost "human" "j" "alpha" "one"
        p2 = mkPost "human" "j" "alpha" "two"
        p3 = mkPost "human" "j" "alpha" "three"
        xs = [p1, p2]
        ys = [p3]
        agent :: Agent [Post]
        agent = tape (reply "j")
        s0 = [] :: [Post]
    assert "S3: beh s0 (xs ++ ys) == beh s0 xs ++ beh (after s0 xs) ys" $
      beh agent s0 (xs ++ ys)
        == beh agent s0 xs ++ beh agent (after agent s0 xs) ys

  -------------------------------------------------------------------------
  -- Delivery: addressed posts, no redelivery.
  -------------------------------------------------------------------------
  putStrLn "delivery"
  do
    let t0 =
          [ mkPost "human" "k" "beta" "hi k",
            mkPost "human" "j" "alpha" "hi j"
          ]
    let (stJ1, t1, _) = turn (tape (reply "j")) (seedState "j" t0) t0
    let (stK1, t2, _) = turn (tape (reply "k")) (seedState "k" t1) t1
    assert "j receives only its addressed posts" $
      map body (reverse (asCarrier stJ1)) == ["hi j"]
    assert "k receives only its addressed posts" $
      map body (reverse (asCarrier stK1)) == ["hi k"]

    assert "unicast post delivers only to addressee" $
      deliversTo (mkPost "human" "j" "alpha" "hi") "j"
        && not (deliversTo (mkPost "human" "j" "alpha" "hi") "k")
    assert "broadcast post delivers to every recipient" $
      deliversTo (mkPost "human" "nobody" "broadcast" "hi") "j"
        && deliversTo (mkPost "human" "nobody" "broadcast" "hi") "k"
    assert "empty channel keeps unicast semantics" $
      deliversTo (mkPost "human" "j" "" "hi") "j"
        && not (deliversTo (mkPost "human" "j" "" "hi") "k")

    let t3 = post (mkPost "human" "j" "alpha" "again") t2
    let (stJ2, _t4, _) = turn (tape (reply "j")) (feedState (newFor "j" t3 stJ1) stJ1) t3
    assert "j sees the new post, no redelivery" $
      map body (reverse (asCarrier stJ2)) == ["hi j", "again"]

  -------------------------------------------------------------------------
  -- Semiring delivery (S1)
  -------------------------------------------------------------------------
  putStrLn "semiring delivery"
  do
    -- G2 · boolean semiring reproduces today's FinRel delivery exactly.
    let agents = ["j", "k"] :: [Text]
        posts =
          [ ("j", "alpha"), -- unicast to j
            ("nobody", "broadcast"), -- broadcast
            ("k", "") -- unicast to k with empty channel
          ] :: [(Text, Text)]
        m = deliveryMatrix agents posts
        expected = [[True, False], [True, True], [False, True]]
    assert "G2 boolean delivery matrix matches FinRel" $
      toLists m == expected

  do
    -- G3 · nilpotency iff topology is acyclic.
    --
    -- DAG: j -> k only. The topology matrix is strictly upper-triangular,
    -- hence nilpotent.
    let agentsDag = ["j", "k"] :: [Text]
        postsDag = [("j", "k", "alpha")] :: [(Text, Text, Text)]
        dag = topologyMatrix agentsDag postsDag :: Matrix Bool
    assert "G3 DAG topology is nilpotent" $ isNilpotent dag

  do
    -- Cycle: j -> k -> j. The topology matrix has a directed cycle,
    -- so no power is zero.
    let agentsCycle = ["j", "k"] :: [Text]
        postsCycle =
          [ ("j", "k", "alpha"),
            ("k", "j", "beta")
          ] ::
          [(Text, Text, Text)]
        cyclic = topologyMatrix agentsCycle postsCycle :: Matrix Bool
    assert "G3 cyclic topology is not nilpotent" $ not (isNilpotent cyclic)

  do
    -- G3 · star of a nilpotent boolean matrix equals the finite sum
    -- I + D + D^2 + ... + D^(n-1).
    let agents = ["j", "k", "l"] :: [Text]
        posts =
          [ ("j", "k", "alpha"),
            ("k", "l", "beta")
          ] ::
          [(Text, Text, Text)]
        d = topologyMatrix agents posts :: Matrix Bool
        n = 3
        eye = fromLists [[True, False, False], [False, True, False], [False, False, True]]
        finiteSum = foldl' matPlus eye (matrixPowers (n - 1) d)
    assert "G3 star of nilpotent boolean matrix equals finite sum" $
      starMatrix d == finiteSum

  -------------------------------------------------------------------------
  -- S0b · estimator fork: soft routing path (pathwise gradients)
  -------------------------------------------------------------------------
  putStrLn "S0b estimator fork: soft routing"
  do
    -- Soft routing: delivery weights are logits; the actual delivery matrix
    -- is the softmax.  The loss is a differentiable function of the expected
    -- delivery, so gradients are pathwise and checkable against finite
    -- differences.  This is the default for slow routing (weights fixed
    -- during a meeting, updated between them).  Hard / sampled routing is
    -- still available if the product needs discrete per-post delivery.
    let softmax ws =
          let es = map exp ws
              s = sum es
           in map (/ s) es
        values = [1.0, 2.0] :: [Double]
        loss ws =
          let ps = softmax ws
           in sum (zipWith (*) ps values)
        grad ws =
          let ps = softmax ws
              l = sum (zipWith (*) ps values)
           in zipWith (\p v -> p * (v - l)) ps values
        ws = [0.5, -0.3] :: [Double]
        eps = 1e-5
        analytic = grad ws
        fd k =
          let wsPlus = take k ws ++ [ws !! k + eps] ++ drop (k + 1) ws
              wsMinus = take k ws ++ [ws !! k - eps] ++ drop (k + 1) ws
           in (loss wsPlus - loss wsMinus) / (2 * eps)
        fds = map fd [0 .. length ws - 1]
    assert "S0b soft-routing gradient matches finite difference" $
      all (\(a, f) -> abs (a - f) < 1e-8) (zip analytic fds)

  -------------------------------------------------------------------------
  -- G1 · routing-weight gradient of usage loss ≈ finite difference
  -------------------------------------------------------------------------
  putStrLn "G1 routing-weight usage loss"
  do
    -- A trajectory of posts, each routed to two agents by softmax weights.
    -- The usage loss is the weighted total value received by the agents,
    -- with a per-agent utility.  The gradient wrt routing logits is computed
    -- analytically and checked against finite differences.  This is the
    -- trajectory-level loss that S2 credit assignment has to differentiate.
    let agents = ["x", "y"] :: [Text]
        posts = [(1.0, "a"), (2.0, "b"), (3.0, "a")] :: [(Double, Text)]
        utility who (_, sender) = if who == sender then 1.0 else 0.5
        softmax xs =
          let es = map exp xs
              s = sum es
           in map (/ s) es
        chunks _ [] = []
        chunks n xs = take n xs : chunks n (drop n xs)
        loss ws =
          let rows = chunks (length agents) ws
           in sum
                [ value
                    * sum
                      [ p * utility agent (value, sender)
                        | (p, agent) <- zip (softmax row) agents
                      ]
                | (row, (value, sender)) <- zip rows posts
                ]
        grad ws =
          concat
            [ let ps = softmax row
                  us = map (\agent -> utility agent (value, sender)) agents
                  lrow = sum (zipWith (*) ps us)
               in zipWith (\p u -> p * (u - lrow)) ps us
              | (row, (value, sender)) <- zip (chunks (length agents) ws) posts
              ]
        ws0 = [0.2, -0.1, 0.5, 0.3, -0.4, 0.1] :: [Double]
        eps = 1e-5
        fd k =
          let bump e = take k ws0 ++ [ws0 !! k + e] ++ drop (k + 1) ws0
           in (loss (bump eps) - loss (bump (-eps))) / (2 * eps)
        fds = map fd [0 .. length ws0 - 1]
        analytic = grad ws0
    assert "G1 usage-loss gradient matches finite difference" $
      all (\(a, f) -> abs (a - f) < 1e-8) (zip analytic fds)

  -------------------------------------------------------------------------
  -- Compaction invariance: summary-insensitive folds survive it.
  -------------------------------------------------------------------------
  putStrLn "compaction invariance"
  do
    let a = tape sum :: System (->) [Int] (Mono Int Int)
    let (_, s1) = run1 a [] 1
    let (_, s2) = run1 a s1 2
    let (o3, _) = run1 a [sum s2] 3
    assert "sum survives wholesale compaction" $ o3 == 6

    let b = tape length :: System (->) [Int] (Mono Int Int)
    let (_, t1) = run1 b [] 1
    let (_, t2) = run1 b t1 2
    let (p3, _) = run1 b [sum t2] 3
    assert "length notices wholesale compaction" $ p3 == 2

  -------------------------------------------------------------------------
  -- Turn integrity: one turn appends exactly the fold's output.
  -------------------------------------------------------------------------
  putStrLn "turn integrity"
  do
    let t0 = [mkPost "human" "j" "alpha" "calc:1 2 3"]
    let (stJ1, t1, _) = turn (tape llmJ) (seedState "j" t0) t0
    let (_stCalc, t2, _) = turn (tape calc) (seedState "calc" t1) t1
    let (_stJ2, t3, _) = turn (tape llmJ) (feedState (newFor "j" t2 stJ1) stJ1) t2
    assert "tool-call chain produces expected final post" $
      body (peek t3) == "final: 6"
    assert "turn appends exactly one post per input" $
      length t3 == 4

  -------------------------------------------------------------------------
  -- Loop v0: round-robin to quiescence (replaces hand-scheduling).
  -------------------------------------------------------------------------
  putStrLn "loop quiescence"
  do
    let roster =
          [ ("j", tape (reply "j")),
            ("k", tape (reply "k"))
          ]
    let t0 =
          [ mkPost "human" "k" "beta" "hi k",
            mkPost "human" "j" "alpha" "hi j"
          ]
    let (states, t1, derivs) = loop roster t0
    assert "loop delivers both agents" $
      map body (reverse (maybe [] asCarrier (lookup "j" states))) == ["hi j"]
        && map body (reverse (maybe [] asCarrier (lookup "k" states))) == ["hi k"]
    assert "loop posts both acks" $
      length t1 == 4
    assert "loop reaches quiescence (no pending)" $
      all (\(_n, st) -> not (hasPending st)) states
    assert "loop records a derivation per processed post" $
      length derivs == 2
    assert "derivation agent names match roster" $
      sort (map dAgent derivs) == ["j", "k"]

    let pToJ = mkPost "human" "j" "alpha" "hi j"
        expectedAckJ = mkPost "j" "human" "alpha" "ack: hi j"
        jDeriv = find (\d -> dAgent d == "j") derivs
    assert "reply derivation records input, outputs, and agent" $
      case jDeriv of
        Just d -> dInput d == pToJ && dOutputs d == [expectedAckJ] && null (dChildren d)
        Nothing -> False

    let roster2 = [("j", tape llmJ), ("calc", tape calc)]
    let tCalc0 = [mkPost "human" "j" "alpha" "calc:1 2 3"]
    let (_states2, tCalc, derivs2) = loop roster2 tCalc0
    assert "loop runs tool-call chain to final" $
      body (peek tCalc) == "final: 6"
    assert "loop tool chain length" $
      length tCalc == 4
    assert "tool-call chain records three derivations" $
      length derivs2 == 3

    let (_emptyStates, tEmpty, emptyDerivs) = loop roster ([] :: [Post])
    assert "loop on empty log is identity" $ null tEmpty
    assert "loop on empty log records no derivations" $ null emptyDerivs

    -- S0a: the meeting is a 'Loop Either (->)' value; 'run' agrees with 'loopWith'.
    let states0 = [(n, feedState (watch n t0) (emptyAgentState n)) | (n, _) <- roster]
        bundle0 = (states0, t0, [])
    assert "meetingLoop run agrees with loopWith" $
      run (meetingLoop roster) bundle0 == loopWith roster states0 t0

  -------------------------------------------------------------------------
  -- O8: schedule independence — loop vs parallel reduction.
  --
  -- Parallel reduction runs every agent against the *same* input log and
  -- appends all outputs.  For independent addresses this agrees with the
  -- round-robin 'loop'; for dependent addresses it is a counterexample.
  -------------------------------------------------------------------------
  putStrLn "O8: schedule independence"
  do
    let rosterInd =
          [ ("j", tape (reply "j")),
            ("k", tape (reply "k"))
          ]
        t0Ind =
          [ mkPost "human" "k" "beta" "hi k",
            mkPost "human" "j" "alpha" "hi j"
          ]
        (_, loopInd, derivsInd) = loop rosterInd t0Ind
        parallelInd = runParallel rosterInd t0Ind
    assert "O8: independent addresses agree between loop and parallel" $
      loopInd == parallelInd
    assert "O8: independent loop records two derivations" $
      length derivsInd == 2

    let forwardTo target hist =
          [mkPost "j" target (channel (peek hist)) ("fwd: " <> body (peek hist))]
        ackToHuman hist =
          [mkPost "k" "human" (channel (peek hist)) ("ack: " <> body (peek hist))]
        rosterDep =
          [ ("j", tape (forwardTo "k")),
            ("k", tape ackToHuman)
          ]
        t0Dep = [mkPost "human" "j" "alpha" "tell k"]
        (_, loopDep, derivsDep) = loop rosterDep t0Dep
        parallelDep = runParallel rosterDep t0Dep
    assert "O8: dependent-address counterexample recorded (loop /= parallel)" $
      loopDep /= parallelDep
    assert "O8: dependent loop records two derivations" $
      length derivsDep == 2

  -------------------------------------------------------------------------
  -- Multi-round pure dialogue: two Moore agents, fixed rounds (not oneshot).
  -- Nudge = const "tell me more."; worker acks. Force = hand-scheduled turns.
  -------------------------------------------------------------------------
  putStrLn "multi-round pure (two Moore agents)"
  do
    let rounds = 3 :: Int
        chan = "mr" :: Text
        nudge :: Agent [Post]
        nudge =
          tape
            ( \_ ->
                [mkPost "nudge" "worker" chan "tell me more."]
            )
        worker :: Agent [Post]
        worker =
          tape
            ( \hist ->
                let p = peek hist
                 in [mkPost "worker" "nudge" chan ("ack:" <> body p)]
            )
        -- seed: human addresses worker
        t0 = [mkPost "human" "worker" chan "start"]
        step (sw, sn, lg) =
          let (sw', lg1, _) = turn worker sw lg
              sn' = feedState (diffLog lg lg1) sn
              (sn'', lg2, _) = turn nudge sn' lg1
              sw'' = feedState (diffLog lg1 lg2) sw'
           in (sw'', sn'', lg2)
        (_, _, tF) = iterate step (seedState "worker" t0, seedState "nudge" t0, t0) !! rounds
        -- newest first: take dialogue posts (exclude seed)
        dialogue = take (2 * rounds) tF
    assert "multi-round: log grew by 2 posts per round" $
      length tF == 1 + 2 * rounds
    assert "multi-round: worker and nudge both posted" $
      any ((== "worker") . author) dialogue
        && any ((== "nudge") . author) dialogue
    assert "multi-round: nudge bodies constant" $
      all (\p -> author p /= "nudge" || body p == "tell me more.") tF

  -------------------------------------------------------------------------
  -- Shard combinators: composition and codec adapters on Ends.
  -------------------------------------------------------------------------
  putStrLn "shard combinators"
  do
    let p1 = mkPost "human" "j" "alpha" "hi"
        p2 = mkPost "j" "human" "alpha" "ack"
        fixedShard :: Shard Identity [Post]
        fixedShard = endsK (\_ -> pure ()) (pure [p2])
        coded = codecShard (map (\p -> p {body = "in:" <> body p})) (map (\p -> p {body = body p <> ":out"})) fixedShard
        out = runIdentity (runKleisli (close (conjoint coded) (companion coded)) [p1])
    assert "codec transforms commit and emit" $
      map body out == ["ack:out"]

    let accumShard :: Shard (State [Post]) [Post]
        accumShard = endsK (\ps -> modify (ps ++)) get
        composed = composeShard accumShard (suffixShard (map (\p -> p {body = body p <> "!"})) accumShard)
        (out2, st) = runState (runKleisli (close (conjoint composed) (companion composed)) [p1]) []
    assert "compose chains shards through the monad" $
      map body out2 == ["hi!", "hi!"] && length st == 2

  -------------------------------------------------------------------------
  -- Agent as Shard: pure Moore citizen at Kleisli Ends (change of base).
  -------------------------------------------------------------------------
  putStrLn "agent as shard"
  do
    let ack :: Agent [Post]
        ack = tape (reply "j")
        pIn = mkPost "human" "j" "alpha" "hi"
        -- pure closed form
        (outs, seat) = runAgentShard ack (AgentSeat [] []) [pIn]
    assert "runAgentShard one ack" $
      map body outs == ["ack: hi"] && length (asState seat) == 1

    -- same citizen as Ends (Kleisli State) — commit/emit only at the boundary
    let sh :: Shard (State (AgentSeat [Post])) [Post]
        sh = agentShard get put ack
        (outs2, seat2) =
          runState
            (runKleisli (close (conjoint sh) (companion sh)) [pIn])
            (AgentSeat [] [])
    assert "agentShard close matches runAgentShard" $
      outs2 == outs && asState seat2 == asState seat

    let pIn2 = mkPost "human" "j" "alpha" "again"
        (outs3, seat3) = runAgentShard ack seat [pIn2]
    assert "agentShard keeps carrier across turns" $
      map body outs3 == ["ack: again"] && length (asState seat3) == 2

  -------------------------------------------------------------------------
  -- O5: arity change — the old "input length == output length" law is gone.
  -------------------------------------------------------------------------
  putStrLn "O5: arity change"
  do
    let arityBreaker :: Agent [Post]
        arityBreaker =
          tape
            ( \hist ->
                let n = length hist
                 in [ mkPost "bot" "human" "alpha" ("x" <> T.pack (show n))
                    | _ <- [1 .. n]
                    ]
            )
        pIn = mkPost "human" "j" "alpha" "a"
        pIn2 = mkPost "human" "j" "alpha" "b"
        (outs, _) = runAgentShard arityBreaker (AgentSeat [] []) [pIn, pIn2]
    assert "O5: Agent now emits a list per input, so input length /= output length" $
      length [pIn, pIn2] /= length outs

  -------------------------------------------------------------------------
  -- Branch agent: level-1 grammar choice via carrier mode.
  --
  -- The carrier carries a Boolean mode. The agent dispatches to an echo or
  -- calc branch based on that mode; the chosen branch's update function
  -- writes the next carrier. The derivation tree records which branch fired.
  -------------------------------------------------------------------------
  putStrLn "branch agent"
  do
    let liftAgent :: Agent [Post] -> Agent (Bool, [Post])
        liftAgent sys =
          System $ \((tag, hist), d) ->
            let inp = monoDir d
                (outs, next) = runSystem sys hist
             in ((tag, next inp), (outs, ()))
        calcOnly :: Agent [Post]
        calcOnly = tape calc
        echoOnly :: Agent [Post]
        echoOnly = tape (reply "j")
        branchy :: Agent (Bool, [Post])
        branchy = branchAgent fst (liftAgent calcOnly) (liftAgent echoOnly)
        pCalc = mkPost "human" "j" "alpha" "1 2 3"
        pEcho = mkPost "human" "j" "alpha" "hello"

    -- Mode True selects the calc branch.
    let (outsCalc, seatCalc) = runAgentShard branchy (AgentSeat (True, []) []) [pCalc]
    assert "branch agent mode True -> calc output" $
      map body outsCalc == ["6"]
    assert "branch agent mode True preserves tag" $
      fst (asState seatCalc) == True

    -- Mode False selects the echo branch.
    let (outsEcho, seatEcho) = runAgentShard branchy (AgentSeat (False, []) []) [pEcho]
    assert "branch agent mode False -> echo output" $
      map body outsEcho == ["ack: hello"]
    assert "branch agent mode False preserves tag" $
      fst (asState seatEcho) == False

  -------------------------------------------------------------------------
  -- Port: batch >:> shard >:> unbatch (parser stream coalgebra around Shard)
  -------------------------------------------------------------------------
  putStrLn "port (token seat)"
  do
    let ack :: Agent [Post]
        ack = tape (reply "j")
        pIn = mkPost "human" "j" "alpha" "hi"
        -- agent as list shard, then token seat via stream buffers
        sh :: Shard (State (AgentSeat [Post], [Post], [Post])) [Post]
        sh =
          agentShard
            (gets (\(seat, _, _) -> seat))
            (\seat -> modify (\(_, i, o) -> (seat, i, o)))
            ack
        port :: Port (State (AgentSeat [Post], [Post], [Post]))
        port =
          portShard
            (gets (\(_, i, _) -> i))
            (\i -> modify (\(seat, _, o) -> (seat, i, o)))
            (gets (\(_, _, o) -> o))
            (\o -> modify (\(seat, i, _) -> (seat, i, o)))
            sh
        (pOut, (seat', inB, outB)) =
          runState
            (runKleisli (close (conjoint port) (companion port)) pIn)
            (AgentSeat [] [], [], [])
    assert "port close: one Post in, one Post out" $
      body pOut == "ack: hi"
    assert "port drains stream buffers on close" $
      null inB && null outB && length (asState seat') == 1

    let pIn2 = mkPost "human" "j" "alpha" "again"
        (pOut2, (seat2, _, _)) =
          runState
            (runKleisli (close (conjoint port) (companion port)) pIn2)
            (seat', [], [])
    assert "port keeps agent carrier across token turns" $
      body pOut2 == "ack: again" && length (asState seat2) == 2

    assert "uncons matches Uncons on lists" $
      let u :: [Int] -> These Int [Int]
          u = uncons
       in u [] == That []
            && u [1] == This 1
            && u [1, 2, 3] == These 1 [2, 3]

  -------------------------------------------------------------------------
  -- Tool call: for an Agent, a tool call is a Post (addr = tool, body = args).
  -- Type / code / example — not related to withhold.
  -------------------------------------------------------------------------
  putStrLn "tool call"
  do
    -- type: tool call ≡ Post addressed to the tool
    let call :: Post
        call = toolCall "j" "calc" "alpha" "1 2 3"
    assert "tool call addr is the tool" $ addr call == "calc"
    assert "tool call body is the args" $ body call == "1 2 3"

    -- code: pure Agent that emits a tool-call Post
    let caller :: Agent [Post]
        caller = tape callCalc
        human = mkPost "human" "j" "alpha" "please sum 1 2 3"
        (outs, _) = runAgentShard caller (AgentSeat [] []) [human]
    assert "agent emits one tool-call post" $
      case outs of
        [p] -> addr p == "calc" && body p == "1 2 3"
        _ -> False

    -- example: Port (Ends Post Post) — one token in, tool-call token out
    let sh :: Shard (State (AgentSeat [Post], [Post], [Post])) [Post]
        sh =
          agentShard
            (gets (\(s, _, _) -> s))
            (\s -> modify (\(_, i, o) -> (s, i, o)))
            caller
        port :: Port (State (AgentSeat [Post], [Post], [Post]))
        port =
          portShard
            (gets (\(_, i, _) -> i))
            (\i -> modify (\(s, _, o) -> (s, i, o)))
            (gets (\(_, _, o) -> o))
            (\o -> modify (\(s, i, _) -> (s, i, o)))
            sh
        (pOut, (seatPort, _, _)) =
          runState
            (runKleisli (close (conjoint port) (companion port)) human)
            (AgentSeat [] [], [], [])
    assert "port example: human Post in → tool-call Post out" $
      author pOut == "j" && addr pOut == "calc" && body pOut == "1 2 3"
    assert "port carrier saw the human input" $
      length (asState seatPort) == 1

  -------------------------------------------------------------------------
  -- Withhold: force only some held content into the seat.
  -- Unrelated to tool calls — about what enters commit, not Post shape.
  -------------------------------------------------------------------------
  putStrLn "withhold"
  do
    let secret = mkPost "ops" "j" "alpha" "bus emergency — do not show yet"
        public = mkPost "human" "j" "alpha" "hi j"
        held = [secret, public] -- store exists; not all of it is delivered
        agent = tape (reply "j") :: Agent [Post]

        -- release only public (withhold secret)
        released = filter ((== "human") . author) held
        (outs, seat) = runAgentShard agent (AgentSeat [] []) released

    assert "withhold: only released posts enter the carrier" $
      map body (asState seat) == ["hi j"]
    assert "withhold: secret never in carrier" $
      all ((/= "bus emergency — do not show yet") . body) (asState seat)
    assert "withhold: agent replies only to what was committed" $
      map body outs == ["ack: hi j"]

    -- stuffing everything is the anti-pattern this avoids
    -- tape carrier is newest-first after fold
    let (outsAll, seatAll) = runAgentShard agent (AgentSeat [] []) held
    assert "full commit would expose secret in carrier" $
      "bus emergency — do not show yet" `elem` map body (asState seatAll)
        && "hi j" `elem` map body (asState seatAll)
    assert "full commit produces a reply to the secret too" $
      length outsAll == 2

  -------------------------------------------------------------------------
  -- S3: population churn
  -------------------------------------------------------------------------
  putStrLn "population churn"
  do
    -- Birth: an agent born between meetings sees posts already addressed to it
    -- on the log and participates in the next meeting.
    let humanPost = mkPost "human" "j" "alpha" "hello"
        replyAgent = tape (reply "j") :: Agent [Post]
        t0 = [humanPost]
        events = [[Birth "j" replyAgent Nothing]]
        (_roster, states, lg, _derivs) = loopPop [] [] t0 events
    assert "birth: agent exists after birth" $
      any ((== "j") . fst) states
    assert "birth: born agent replies to post on the log" $
      any (\p -> author p == "j") lg

  do
    -- Death: an agent removed before a meeting no longer processes posts
    -- addressed to it.
    let humanPost = mkPost "human" "j" "alpha" "hello"
        replyAgent = tape (reply "j") :: Agent [Post]
        t0 = [humanPost]
        events = [[Death "j"]]
        (_roster, states, lg, _derivs) = loopPop [("j", replyAgent)] [("j", seedState "j" t0)] t0 events
    assert "death: agent is removed" $
      not (any ((== "j") . fst) states)
    assert "death: no reply from dead agent" $
      not (any (\p -> author p == "j") lg)

  do
    -- Replacement: birth and death in the same gap leave unrelated agents
    -- untouched.
    let humanPost = mkPost "human" "k" "alpha" "hello"
        jReply = tape (reply "j") :: Agent [Post]
        kReply = tape (reply "k") :: Agent [Post]
        t0 = [humanPost]
        events = [[Death "j", Birth "k" kReply Nothing]]
        (_roster, states, lg, _derivs) =
          loopPop [("j", jReply)] [("j", seedState "j" t0)] t0 events
    assert "replacement: j is gone" $ not (any ((== "j") . fst) states)
    assert "replacement: k exists" $ any ((== "k") . fst) states
    assert "replacement: k replied" $ any (\p -> author p == "k") lg

  do
    -- P1: loopPop is the final element of loopsPop, and derivations accumulate.
    let humanPost = mkPost "human" "j" "alpha" "hello"
        replyAgent = tape (reply "j") :: Agent [Post]
        t0 = [humanPost]
        events = [[Birth "j" replyAgent Nothing]]
        (rosterF, statesF, lgF, derivsF) = loopPop [] [] t0 events
        unfolding = loopsPop [] [] t0 events
        (rosterU, statesU, lgU, derivsU) = last unfolding
    assert "P1: loopPop roster names == last loopsPop roster names" $
      map fst rosterF == map fst rosterU
    assert "P1: loopPop states == last loopsPop states" $ statesF == statesU
    assert "P1: loopPop log == last loopsPop log" $ lgF == lgU
    assert "P1: loopPop derivations == last loopsPop derivations" $ derivsF == derivsU
    assert "P1: loopsPop starts with the initial state" $
      case unfolding of
        (r0, s0, l0, d0) : _ -> null r0 && null s0 && l0 == t0 && null d0
        _ -> False

  do
    -- P2: an agent born at meeting 2 takes the same first turn as one
    -- present-and-silent throughout meeting 1.
    let pingOnce :: [Post] -> [Post]
        pingOnce hist = [mkPost "k" "j" "alpha" "ping" | length hist == 0]
        kAgent = tape pingOnce :: Agent [Post]
        jReply = tape (reply "j") :: Agent [Post]
        humanToK = mkPost "human" "k" "alpha" "hi"
        t0 = [humanToK]
        (_, _, lgB, derivsB) =
          loopPop [("k", kAgent)] [("k", seedState "k" t0)] t0 [[Birth "j" jReply Nothing]]
        (_, _, lgP, derivsP) =
          loopPop
            [("k", kAgent), ("j", jReply)]
            [("k", seedState "k" t0), ("j", seedState "j" t0)]
            t0
            [[], []]
        isJ d = dAgent d == "j"
    assert "P2: born and present-silent final logs agree" $ lgB == lgP
    assert "P2: born and present-silent j derivations agree" $
      filter isJ derivsB == filter isJ derivsP

  do
    -- P3: population schedule order matters.
    let oldReply :: [Post] -> [Post]
        oldReply _ = [mkPost "n" "human" "alpha" "old"]
        newReply :: [Post] -> [Post]
        newReply _ = [mkPost "n" "human" "alpha" "new"]
        oldAgent = tape oldReply :: Agent [Post]
        newAgent = tape newReply :: Agent [Post]
        humanToN = mkPost "human" "n" "alpha" "hi"
        t0 = [humanToN]
        (_, _, lgDB, _) =
          loopPop [("n", oldAgent)] [("n", seedState "n" t0)] t0
            [[Death "n", Birth "n" newAgent Nothing]]
        (_, rosterBD, lgBD, _) =
          loopPop [("n", oldAgent)] [("n", seedState "n" t0)] t0
            [[Birth "n" newAgent Nothing, Death "n"]]
    assert "P3: [Death, Birth] emits the new reply" $
      any (\p -> body p == "new") lgDB
    assert "P3: [Birth, Death] removes agent n" $
      not (any ((== "n") . fst) rosterBD)
    assert "P3: [Birth, Death] emits no reply from n" $
      not (any (\p -> author p == "n") lgBD)
    assert "P3: final logs differ" $ lgDB /= lgBD

  -------------------------------------------------------------------------
  -- H1: heterogeneous population — mixed carrier types in one roster.
  -------------------------------------------------------------------------
  putStrLn "heterogeneous population"
  do
    let liftAgent :: Agent [Post] -> Agent (Bool, [Post])
        liftAgent sys =
          System $ \((tag, hist), d) ->
            let inp = monoDir d
                (outs, next) = runSystem sys hist
             in ((tag, next inp), (outs, ()))
        calcOnly :: Agent [Post]
        calcOnly = tape calc
        echoOnly :: Agent [Post]
        echoOnly = tape (reply "branchy")
        branchy :: Agent (Bool, [Post])
        branchy = branchAgent fst (liftAgent calcOnly) (liftAgent echoOnly)
        echoAgent :: Agent [Post]
        echoAgent = tape (reply "echo")
        t0 =
          [ mkPost "human" "echo" "alpha" "hi",
            mkPost "human" "branchy" "alpha" "1 2 3"
          ]
        roster =
          [ ("echo", HPopAgent echoAgent (seedHPopState "echo" [] t0)),
            ("branchy", HPopAgent branchy (seedHPopState "branchy" (True, []) t0))
          ]
        (_, lg, derivs) = loopHPop roster t0 [[]]
    assert "H1: echo agent (carrier [Post]) replied" $
      any (\p -> author p == "echo") lg
    assert "H1: branchy agent (carrier (Bool, [Post])) calculated" $
      any (\p -> body p == "6") lg
    assert "H1: both agents recorded derivations" $
      any (\d -> dAgent d == "echo") derivs
        && any (\d -> dAgent d == "branchy") derivs

  do
    -- H2: a heterogeneous agent can be born into an existing homogeneous-ish
    -- meeting, and it sees posts already addressed to it on the log.
    let liftAgent :: Agent [Post] -> Agent (Bool, [Post])
        liftAgent sys =
          System $ \((tag, hist), d) ->
            let inp = monoDir d
                (outs, next) = runSystem sys hist
             in ((tag, next inp), (outs, ()))
        calcOnly = tape calc :: Agent [Post]
        echoOnly = tape (reply "branchy") :: Agent [Post]
        branchy = branchAgent fst (liftAgent calcOnly) (liftAgent echoOnly) :: Agent (Bool, [Post])
        echoAgent = tape (reply "echo") :: Agent [Post]
        t0 =
          [ mkPost "human" "echo" "alpha" "hi",
            mkPost "human" "branchy" "alpha" "1 2 3"
          ]
        echoState = AgentState [] (foldl' (flip appendInbox) (emptyInbox "echo") (watch "echo" t0))
        roster = [("echo", HPopAgent echoAgent echoState)]
        events = [[HBirth "branchy" (HPopAgent branchy (seedHPopState "branchy" (True, []) t0))]]
        (_, lg, derivs) = loopHPop roster t0 events
    assert "H2: born heterogeneous agent calculated" $
      any (\p -> body p == "6") lg
    assert "H2: original echo agent still replied" $
      any (\p -> author p == "echo") lg
    assert "H2: branchy derivation recorded" $
      any (\d -> dAgent d == "branchy") derivs

  putStrLn "All tests passed"
  where
    -- | Seed an agent state for a heterogeneous roster.
    seedHPopState ::
      (Snoc f Post, Uncons f Post) => Text -> s -> Log f -> AgentState s f
    seedHPopState name carrier lg =
      AgentState carrier (foldl' (flip appendInbox) (emptyInbox name) (watch name lg))

    -- | Tool call as data: author = caller, addr = tool, body = args.
    toolCall :: Text -> Text -> Text -> Text -> Post
    toolCall from tool chan args = mkPost from tool chan args

    -- | Agent policy: on a "please sum …" human, emit a calc tool call.
    callCalc :: [Post] -> [Post]
    callCalc hist =
      let p = peek hist
          args =
            if "please sum " `T.isPrefixOf` body p
              then T.drop (T.length "please sum ") (body p)
              else body p
       in [toolCall "j" "calc" (channel p) args]

    llmJ :: [Post] -> [Post]
    llmJ hist =
      let p = peek hist
       in [ if "calc:" `T.isPrefixOf` body p
              then mkPost "j" "calc" (channel p) (T.drop 5 (body p))
              else
                mkPost
                  "j"
                  (author (peek (dropWhile ((== "calc") . author) hist)))
                  (channel p)
                  ("final: " <> body p)
          ]

    calc :: [Post] -> [Post]
    calc hist =
      let p = peek hist
       in [ mkPost
              "calc"
              (author p)
              (channel p)
              (T.pack (show (sum [read (T.unpack w) :: Int | w <- T.words (body p)])))
          ]
