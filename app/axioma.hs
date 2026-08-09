{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -Wno-x-partial #-}
-- Post is polymorphic in its payload; this file pins everything at Text via
-- the module 'default' declaration, so -Wtype-defaults would be noise.
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Main (main) where

import Algebra.Graph.Labelled qualified as LG
import Circuit.Agent
import Circuit.Agent.Mark (Mark (..), isEscalate, isHalt, markGlyph, markOf, parseMark)
import Circuit.Agent.Machina.Mark (markLoop, spinMark)
import Circuit.Agent.Framing
  ( Cons (..),
    Jsonl (..),
    Snoc (..),
    Stamped (..),
    frameStored,
    parseLine,
    parseLineAt,
    parseMessage,
    renderStored,
  )
import Circuit.Agent.Delivery
  ( DelRel,
    broadcastRel,
    copyRel,
    deliveryMatrix,
    deliveryRel,
    deliversRel,
    discardRel,
    emptyRel,
    isNilpotent,
    matrixPowers,
    namedRel,
    topologyMatrix,
  )
import Circuit.Agent.Graph
  ( AgentRegistry,
    atomic,
    bus,
    runGraph,
    star,
  )
import Circuit.Agent.Query
  ( echoShard,
    replyPosts,
    runShardIO,
    sessionPrompt,
    synthesisPosts,
  )
import Circuit.Agent.Tensor
  ( awaitShard,
    fanInShard,
    fanOutShard,
    raceShard,
    silentShard,
    synthesisSummary,
  )
import Circuit.Layer (run)
import Circuit.Poly (Dir, Eval (..), Mono, Pos, System (..), fromEvalSystem, monoDir, monoIn)
import Circuit.Poly.Process (after, iterateSystem, runSystem)
import Circuit.Stream (These (..), Uncons, uncons)
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Category qualified as C
import Cursor (newMem, pollNumberedFile)
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.STM
import Control.Exception (BlockedIndefinitelyOnSTM (..), SomeException, catch, fromException)
import Control.Monad (unless, when)
import Control.Monad.State (State, StateT, get, gets, modify, put, runState, runStateT)
import Data.Foldable (traverse_)
import Data.Function (fix)
import Data.Functor.Identity (Identity (..))
import Data.List (find, foldl', nub, sort)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Harpie.NumHask.Matrix (Matrix, fromLists, matPlus, starMatrix, toLists)
import System.Directory (doesFileExist, getTemporaryDirectory, removeFile)
import System.Exit (exitFailure)
import System.FilePath ((</>))
import System.Timeout (timeout)

default (Text)

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

-- | Remove a file if present.
wipe :: FilePath -> IO ()
wipe f = do
  e <- doesFileExist f
  when e (removeFile f)

-- | Close a same-type shard once under 'StateT [Post Text] IO'.
closeShardIO :: Shard (StateT [Post Text] IO) [Post Text] [Post Text] -> [Post Text] -> [Post Text] -> IO ([Post Text], [Post Text])
closeShardIO sh x s0 =
  runStateT (runKleisli (close (conjoint sh) (companion sh)) x) s0

peek :: [Post Text] -> Post Text
peek [] = error "verify: empty history"
peek (p : _) = p

reply :: Text -> [Post Text] -> [Post Text]
reply name hist =
  [mkPost name [from (peek hist)] ("ack: " <> body (peek hist))]

-- | New posts in @new@ compared to @old@, oldest first.
diffLog :: [Post Text] -> [Post Text] -> [Post Text]
diffLog old new = reverse (take (length new - length old) new)

-- | Route one post to a state's inbox if it is addressed to the owner.
routeToInbox :: Post Text -> AgentState [Post Text] [Post Text] -> AgentState [Post Text] [Post Text]
routeToInbox p st =
  if deliversTo p (inboxSubs (asInbox st))
    then st {asInbox = appendInbox p (asInbox st)}
    else st

-- | Feed oldest-first posts into a state's inbox.
feedState :: [Post Text] -> AgentState [Post Text] [Post Text] -> AgentState [Post Text] [Post Text]
feedState posts st = foldl' (flip routeToInbox) st posts

-- | Seed an agent state from the addressed posts in a log.
seedState :: [Text] -> [Post Text] -> AgentState [Post Text] [Post Text]
seedState who lg = feedState (watch @Text who lg) (emptyAgentState @Text who)

-- | Addressed posts for @who@ in @lg@ that are not already in the carrier.
newFor :: [Text] -> [Post Text] -> AgentState [Post Text] [Post Text] -> [Post Text]
newFor who lg st = filter (`notElem` asCarrier st) (watch @Text who lg)

-- | Parallel reduction: every agent runs against the *same* input log, and
-- all emitted posts are appended to that log.  This is the schedule-independent
-- baseline that O8 compares against the round-robin 'loop'.
runParallel :: [(Text, Agent (->) [Post Text] (Post Text) [Post Text])] -> [Post Text] -> [Post Text]
runParallel roster lg = foldl' (flip post) lg outputs
  where
    outputs = concatMap (\(who, agent) -> beh agent [] (watch @Text [who] lg)) roster

-- | Pure 'orElse': left branch speaks unless it is silent, otherwise right.
raceP :: ([Post Text] -> [Post Text]) -> ([Post Text] -> [Post Text]) -> ([Post Text] -> [Post Text])
raceP f g hist =
  let os = f hist
   in if null os then g hist else os

-- | Pure product / await: both branches speak; emits are concatenated
-- left-to-right.
awaitP :: ([Post Text] -> [Post Text]) -> ([Post Text] -> [Post Text]) -> ([Post Text] -> [Post Text])
awaitP f g hist = f hist <> g hist

-- | Silent policy: the zero of race and the unit of await.
silent :: [Post Text] -> [Post Text]
silent _ = []

-- | Symmetric closure of 'raceP' outcomes under left/right bias.
-- In the pure model this is the set of possible results; temporal race
-- refines it by picking one element.
outcomesRace :: ([Post Text] -> [Post Text]) -> ([Post Text] -> [Post Text]) -> [Post Text] -> [[Post Text]]
outcomesRace f g hist = nub [raceP f g hist, raceP g f hist]

-- | Agent that ignores its history and always emits the same list.
constAgent :: [Post Text] -> Agent (->) [Post Text] (Post Text) [Post Text]
constAgent outs = tape (const outs)

-- | STM agent that ignores its history and always emits the same list.
constAgentS :: [Post Text] -> AgentS [Post Text] (Post Text)
constAgentS outs = agentM (tape (const outs))

main :: IO ()
main = do
  putStrLn "circuits-agent oracle tests"

  -------------------------------------------------------------------------
  -- Tier A: structural laws
  --
  -- Parametric over token types (Int, Bool, [Int], etc.).  No Post semantics.
  -------------------------------------------------------------------------
  putStrLn "Tier A: structural laws"

  -------------------------------------------------------------------------
  -- A0: identity agent
  -------------------------------------------------------------------------
  putStrLn "A0: identity agent"
  do
    let idAgent :: Agent (->) [Int] Int Int
        idAgent = tape head
    assert "A0: tape head streams inputs through unchanged" $
      iterateSystem idAgent [] [1, 2, 3 :: Int] == [1, 2, 3]

  -------------------------------------------------------------------------
  -- A1: sequential stream composition
  -------------------------------------------------------------------------
  putStrLn "A1: sequential stream composition"
  do
    let f :: Int -> Int
        f = (+ 10)
        g :: Int -> Int
        g = (* 2)
        fAgent :: Agent (->) [Int] Int Int
        fAgent = tape (f . head)
        gAgent :: Agent (->) [Int] Int Int
        gAgent = tape (g . head)
        inputs = [1, 2, 3 :: Int]
        chained = iterateSystem gAgent [] (iterateSystem fAgent [] inputs)
        direct = iterateSystem (tape (g . f . head)) [] inputs
    assert "A1: chaining outputs equals feeding the composed function" $
      chained == direct

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
    let xs = [1, 2, 3 :: Int]
        f hist = [head hist]
        h = take 1
        sys1 :: Agent (->) [Int] Int [Int]
        sys1 = tape f
        sys2 :: Agent (->) [Int] Int [Int]
        sys2 = tape (f . h)
    assert "O2: summarizer h preserves behaviour" $
      iterateSystem sys2 (h []) xs == iterateSystem sys1 [] xs

  -------------------------------------------------------------------------
  -- S3: behaviour is functorial over stream concatenation.
  -------------------------------------------------------------------------
  putStrLn "S3: behaviour functoriality"
  do
    let xs = [1, 2 :: Int]
        ys = [3 :: Int]
        agent :: Agent (->) [Int] Int [Int]
        agent = tape (\hist -> [head hist])
        s0 = [] :: [Int]
    assert "S3: beh s0 (xs ++ ys) == beh s0 xs ++ beh (after agent s0 xs) ys" $
      behA agent s0 (xs ++ ys)
        == behA agent s0 xs ++ behA agent (after agent s0 xs) ys

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
  -- Tier B: addressed-log laws
  --
  -- Concrete Post semantics: delivery, turns, loops, shards, tool calls.
  -------------------------------------------------------------------------
  putStrLn "Tier B: addressed-log laws"

  -------------------------------------------------------------------------
  -- Reply stream laws (addressed-log instances of O2 / S3)
  -------------------------------------------------------------------------
  putStrLn "reply stream laws"
  do
    let p1 = mkPost "human" ["j"] "one"
        p2 = mkPost "human" ["j"] "two"
        p3 = mkPost "human" ["j"] "three"
        ins = [p1, p2, p3]
        f = reply "j"
        h = take 1
        sys1 :: Agent (->) [Post Text] (Post Text) [Post Text]
        sys1 = tape f
        sys2 :: Agent (->) [Post Text] (Post Text) [Post Text]
        sys2 = tape (f . h)
    assert "reply homomorphism: summarizer h preserves behaviour" $
      beh sys2 (h []) ins == beh sys1 [] ins

  do
    let p1 = mkPost "human" ["j"] "one"
        p2 = mkPost "human" ["j"] "two"
        p3 = mkPost "human" ["j"] "three"
        xs = [p1, p2]
        ys = [p3]
        agent :: Agent (->) [Post Text] (Post Text) [Post Text]
        agent = tape (reply "j")
        s0 = [] :: [Post Text]
    assert "reply functoriality: beh s0 (xs ++ ys) == beh s0 xs ++ beh (after agent s0 xs) ys" $
      beh agent s0 (xs ++ ys)
        == beh agent s0 xs ++ beh agent (after agent s0 xs) ys

  -------------------------------------------------------------------------
  -- Delivery: addressed posts, no redelivery.
  -------------------------------------------------------------------------
  putStrLn "delivery"
  do
    let t0 =
          [ mkPost "human" ["k"] "hi k",
            mkPost "human" ["j"] "hi j"
          ]
    let (stJ1, t1, _) = turn (tape (reply "j")) (seedState ["j"] t0) t0
    let (stK1, t2, _) = turn (tape (reply "k")) (seedState ["k"] t1) t1
    assert "j receives only its addressed posts" $
      map body (reverse (asCarrier stJ1)) == ["hi j"]
    assert "k receives only its addressed posts" $
      map body (reverse (asCarrier stK1)) == ["hi k"]

    assert "unicast post delivers only to addressee" $
      deliversTo (mkPost "human" ["j"] "hi") ["j"]
        && not (deliversTo (mkPost "human" ["j"] "hi") ["k"])
    assert "multi-cast post delivers to every named recipient" $
      deliversTo (mkPost "human" ["j", "k"] "hi") ["j"]
        && deliversTo (mkPost "human" ["j", "k"] "hi") ["k"]
    assert "post not addressed to agent does not deliver" $
      deliversTo (mkPost "human" ["j"] "hi") ["j"]
        && not (deliversTo (mkPost "human" ["j"] "hi") ["k"])
    assert "to=all broadcasts to every subscriber" $
      deliversTo (mkPost "human" ["all"] "hi") ["j"]
        && deliversTo (mkPost "human" ["all"] "hi") ["k"]
    assert "to=[] delivers to no one" $
      not (deliversTo (mkPost "human" [] "hi") ["j"])
        && not (deliversTo (mkPost "human" [] "hi") ["k"])
    assert "to=[''] is discard, delivers to no one" $
      not (deliversTo (mkPost "human" [""] "hi") ["j"])
        && not (deliversTo (mkPost "human" [""] "hi") ["k"])

    let t3 = post (mkPost "human" ["j"] "again") t2
    let (stJ2, _t4, _) = turn (tape (reply "j")) (feedState (newFor ["j"] t3 stJ1) stJ1) t3
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
          [ ["j"], -- unicast to j
            ["j", "k"], -- multi-cast to both
            ["k"], -- unicast to k
            ["all"], -- broadcast
            [], -- discard
            [""] -- discard sentinel
          ] ::
            [[Text]]
        m = deliveryMatrix agents posts
        expected =
          [ [True, False],
            [True, True],
            [False, True],
            [True, True],
            [False, False],
            [False, False]
          ]
    assert "G2 boolean delivery matrix matches FinRel" $
      toLists m == expected

  do
    -- G3 · nilpotency iff topology is acyclic.
    --
    -- DAG: j -> k only. The topology matrix is strictly upper-triangular,
    -- hence nilpotent.
    let agentsDag = ["j", "k"] :: [Text]
        postsDag = [("j", ["k"])] :: [(Text, [Text])]
        dag = topologyMatrix agentsDag postsDag :: Matrix Bool
    assert "G3 DAG topology is nilpotent" $ isNilpotent dag

  do
    -- Cycle: j -> k -> j. The topology matrix has a directed cycle,
    -- so no power is zero.
    let agentsCycle = ["j", "k"] :: [Text]
        postsCycle =
          [ ("j", ["k"]),
            ("k", ["j"])
          ] ::
            [(Text, [Text])]
        cyclic = topologyMatrix agentsCycle postsCycle :: Matrix Bool
    assert "G3 cyclic topology is not nilpotent" $ not (isNilpotent cyclic)

  do
    -- G3 · star of a nilpotent boolean matrix equals the finite sum
    -- I + D + D^2 + ... + D^(n-1).
    let agents = ["j", "k", "l"] :: [Text]
        posts =
          [ ("j", ["k"]),
            ("k", ["l"])
          ] ::
            [(Text, [Text])]
        d = topologyMatrix agents posts :: Matrix Bool
        n = 3
        eye = fromLists [[True, False, False], [False, True, False], [False, False, True]]
        finiteSum = foldl' matPlus eye (matrixPowers (n - 1) d)
    assert "G3 star of nilpotent boolean matrix equals finite sum" $
      starMatrix d == finiteSum

  -------------------------------------------------------------------------
  -- FinRel delivery (F1)
  -------------------------------------------------------------------------
  putStrLn "FinRel delivery"
  do
    let agents :: Set Text
        agents = Set.fromList ["j", "k"]
        p = mkPost "human" [] "irrelevant"
        expect tos subs expected =
          deliversRel (deliveryRel agents tos) (Set.fromList subs) == expected
            && deliversTo (p {to = tos}) subs == expected

    assert "F1 copyRel is the diagonal on agents" $
      copyRel agents == Set.fromList [("j", ("j", "j")), ("k", ("k", "k"))]

    assert "F1 discardRel relates every agent to the terminal value" $
      discardRel agents == Set.fromList [("j", ()), ("k", ())]

    assert "F1 broadcast is the dagger (converse) of discard" $
      Set.map (\(a, ()) -> ((), a)) (discardRel agents)
        == broadcastRel agents

    assert "F1 deliveryRel [all] equals broadcast" $
      deliveryRel agents ["all"] == broadcastRel agents

    assert "F1 deliveryRel [] equals emptyRel" $
      deliveryRel agents [] == (emptyRel :: DelRel Text)

    assert "F1 deliveryRel [\"\"] equals emptyRel" $
      deliveryRel agents [""] == (emptyRel :: DelRel Text)

    assert "F1 deliveryRel named equals singleton union" $
      deliveryRel agents ["j", "k"]
        == namedRel "j" `Set.union` namedRel "k"

    assert "F1 FinRel agrees with deliversTo: unicast" $
      expect ["j"] ["j"] True && expect ["j"] ["k"] False

    assert "F1 FinRel agrees with deliversTo: multicast" $
      expect ["j", "k"] ["j"] True && expect ["j", "k"] ["k"] True

    assert "F1 FinRel agrees with deliversTo: broadcast" $
      expect ["all"] ["j"] True && expect ["all"] ["k"] True

    assert "F1 FinRel agrees with deliversTo: discard" $
      expect [] ["j"] False && expect [""] ["j"] False

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
  -- Turn integrity: one turn appends exactly the fold's output.
  -------------------------------------------------------------------------
  putStrLn "turn integrity"
  do
    let t0 = [mkPost "human" ["j"] "calc:1 2 3"]
    let (stJ1, t1, _) = turn (tape llmJ) (seedState ["j"] t0) t0
    let (_stCalc, t2, _) = turn (tape calc) (seedState ["calc"] t1) t1
    let (_stJ2, t3, _) = turn (tape llmJ) (feedState (newFor ["j"] t2 stJ1) stJ1) t2
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
          [ mkPost "human" ["k"] "hi k",
            mkPost "human" ["j"] "hi j"
          ]
    let (states, t1, derivs) = loop roster t0
    assert "loop delivers both agents" $
      map body (reverse (maybe [] asCarrier (lookup "j" states))) == ["hi j"]
        && map body (reverse (maybe [] asCarrier (lookup "k" states))) == ["hi k"]
    assert "loop posts both acks" $
      length t1 == 4
    assert "loop reaches quiescence (no pending)" $
      all (\(_n, st) -> not (hasPending @Text st)) states
    assert "loop records a derivation per processed post" $
      length derivs == 2
    assert "derivation agent names match roster" $
      sort (map dAgent derivs) == ["j", "k"]

    let pToJ = mkPost "human" ["j"] "hi j"
        expectedAckJ = mkPost "j" ["human"] "ack: hi j"
        jDeriv = find (\d -> dAgent d == "j") derivs
    assert "reply derivation records input, outputs, and agent" $
      case jDeriv of
        Just d -> dInput d == pToJ && dOutputs d == [expectedAckJ] && null (dChildren d)
        Nothing -> False

    let roster2 = [("j", tape llmJ), ("calc", tape calc)]
    let tCalc0 = [mkPost "human" ["j"] "calc:1 2 3"]
    let (_states2, tCalc, derivs2) = loop roster2 tCalc0
    assert "loop runs tool-call chain to final" $
      body (peek tCalc) == "final: 6"
    assert "loop tool chain length" $
      length tCalc == 4
    assert "tool-call chain records three derivations" $
      length derivs2 == 3

    let (_emptyStates, tEmpty, emptyDerivs) = loop roster ([] :: [Post Text])
    assert "loop on empty log is identity" $ null tEmpty
    assert "loop on empty log records no derivations" $ null emptyDerivs

    -- S0a: the meeting is a 'Loop Either (->)' value; 'run' agrees with 'loopWith'.
    let states0 = [(n, feedState (watch @Text [n] t0) (emptyAgentState @Text [n])) | (n, _) <- roster]
        bundle0 = (states0, t0, [])
    assert "meetingLoop run agrees with loopWith" $
      run (meetingLoop roster) bundle0 == loopWith roster states0 t0

  -------------------------------------------------------------------------
  -- Multi-seat card: two agents share one card subscription.
  --
  -- 'loopSubs' lets several agents subscribe to the same card name; a post
  -- addressed to the card reaches every subscriber.
  -------------------------------------------------------------------------
  putStrLn "multi-seat card"
  do
    let cardRoster =
          [ ("alpha", ["xyzzy"], tape (reply "alpha")),
            ("beta", ["xyzzy"], tape (reply "beta"))
          ]
        seed = [mkPost "human" ["xyzzy"] "hello card"]
        (cardStates, cardLog, cardDerivs) = loopSubs cardRoster seed
    let replies = filter (\p -> from p /= "human") cardLog
    assert "both subscribers processed the card post" $
      map body (reverse (maybe [] asCarrier (lookup "alpha" cardStates))) == ["hello card"]
        && map body (reverse (maybe [] asCarrier (lookup "beta" cardStates))) == ["hello card"]
    assert "log has seed plus one reply per subscriber" $
      length cardLog == 3 && length replies == 2
    assert "replies are from alpha and beta" $
      sort (map from replies) == ["alpha", "beta"]
    assert "replies are addressed to the original sender" $
      all (== ["human"]) (map to replies)
    assert "derivations name the subscriber agents, not the card" $
      sort (map dAgent cardDerivs) == ["alpha", "beta"]

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
          [ mkPost "human" ["k"] "hi k",
            mkPost "human" ["j"] "hi j"
          ]
        (_, loopInd, derivsInd) = loop rosterInd t0Ind
        parallelInd = runParallel rosterInd t0Ind
    assert "O8: independent addresses agree between loop and parallel" $
      loopInd == parallelInd
    assert "O8: independent loop records two derivations" $
      length derivsInd == 2

    let forwardTo target hist =
          [mkPost "j" [target] ("fwd: " <> body (peek hist))]
        ackToHuman hist =
          [mkPost "k" ["human"] ("ack: " <> body (peek hist))]
        rosterDep =
          [ ("j", tape (forwardTo "k")),
            ("k", tape ackToHuman)
          ]
        t0Dep = [mkPost "human" ["j"] "tell k"]
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
        nudge :: Agent (->) [Post Text] (Post Text) [Post Text]
        nudge =
          tape
            ( const
                [mkPost "nudge" ["worker"] "tell me more."]
            )
        worker :: Agent (->) [Post Text] (Post Text) [Post Text]
        worker =
          tape
            ( \hist ->
                let p = peek hist
                 in [mkPost "worker" ["nudge"] ("ack:" <> body p)]
            )
        -- seed: human addresses worker
        t0 = [mkPost "human" ["worker"] "start"]
        step (sw, sn, lg) =
          let (sw', lg1, _) = turn worker sw lg
              sn' = feedState (diffLog lg lg1) sn
              (sn'', lg2, _) = turn nudge sn' lg1
              sw'' = feedState (diffLog lg1 lg2) sw'
           in (sw'', sn'', lg2)
        (_, _, tF) = iterate step (seedState ["worker"] t0, seedState ["nudge"] t0, t0) !! rounds
        -- newest first: take dialogue posts (exclude seed)
        dialogue = take (2 * rounds) tF
    assert "multi-round: log grew by 2 posts per round" $
      length tF == 1 + 2 * rounds
    assert "multi-round: worker and nudge both posted" $
      any ((== "worker") . from) dialogue
        && any ((== "nudge") . from) dialogue
    assert "multi-round: nudge bodies constant" $
      all (\p -> from p /= "nudge" || body p == "tell me more.") tF

  -------------------------------------------------------------------------
  -- Shard combinators: composition and codec adapters on Ends.
  -------------------------------------------------------------------------
  putStrLn "shard combinators"
  do
    let p1 = mkPost "human" ["j"] "hi"
        p2 = mkPost "j" ["human"] "ack"
        fixedShard :: Shard Identity [Post Text] [Post Text]
        fixedShard = endsK (\_ -> pure ()) (pure [p2])
        coded = codecShard (map (\p -> p {body = "in:" <> body p})) (map (\p -> p {body = body p <> ":out"})) fixedShard
        out = runIdentity (runKleisli (close (conjoint coded) (companion coded)) [p1])
    assert "codec transforms commit and emit" $
      map body out == ["ack:out"]

    let accumShard :: Shard (State [Post Text]) [Post Text] [Post Text]
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
    let ack :: Agent (->) [Post Text] (Post Text) [Post Text]
        ack = tape (reply "j")
        pIn = mkPost "human" ["j"] "hi"
        -- pure closed form
        (outs, seat) = runAgentShard ack (AgentSeat [] []) [pIn]
    assert "runAgentShard one ack" $
      map body outs == ["ack: hi"] && length (asState seat) == 1

    -- same citizen as Ends (Kleisli State) — commit/emit only at the boundary
    let sh :: Shard (State (AgentSeat [Post Text] Text)) [Post Text] [Post Text]
        sh = agentShard get put ack
        (outs2, seat2) =
          runState
            (runKleisli (close (conjoint sh) (companion sh)) [pIn])
            (AgentSeat [] [])
    assert "agentShard close matches runAgentShard" $
      outs2 == outs && asState seat2 == asState seat

    let pIn2 = mkPost "human" ["j"] "again"
        (outs3, seat3) = runAgentShard ack seat [pIn2]
    assert "agentShard keeps carrier across turns" $
      map body outs3 == ["ack: again"] && length (asState seat3) == 2

  -------------------------------------------------------------------------
  -- O5: arity change — the old "input length == output length" law is gone.
  -------------------------------------------------------------------------
  putStrLn "O5: arity change"
  do
    let arityBreaker :: Agent (->) [Post Text] (Post Text) [Post Text]
        arityBreaker =
          tape
            ( \hist ->
                let n = length hist
                 in [ mkPost "bot" ["human"] ("x" <> T.pack (show n))
                    | _ <- [1 .. n]
                    ]
            )
        pIn = mkPost "human" ["j"] "a"
        pIn2 = mkPost "human" ["j"] "b"
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
    let liftAgent :: Agent (->) [Post Text] (Post Text) [Post Text] -> Agent (->) (Bool, [Post Text]) (Post Text) [Post Text]
        liftAgent sys =
          System $ \((tag, hist), d) ->
            let inp = monoDir d
                (outs, next) = runSystem sys hist
             in ((tag, next inp), (outs, ()))
        calcOnly :: Agent (->) [Post Text] (Post Text) [Post Text]
        calcOnly = tape calc
        echoOnly :: Agent (->) [Post Text] (Post Text) [Post Text]
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

  -------------------------------------------------------------------------
  -- Port: batch >:> shard >:> unbatch (parser stream coalgebra around Shard)
  -------------------------------------------------------------------------
  putStrLn "port (token seat)"
  do
    let ack :: Agent (->) [Post Text] (Post Text) [Post Text]
        ack = tape (reply "j")
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
            (runKleisli (close (conjoint port) (companion port)) pIn)
            (AgentSeat [] [], [], [])
    assert "port close: one Post in, one Post out" $
      body pOut == "ack: hi"
    assert "port drains stream buffers on close" $
      null inB && null outB && length (asState seat') == 1

    let pIn2 = mkPost "human" ["j"] "again"
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
  -- Tool call: for an Agent, a tool call is a Post (to = [tool], body = args).
  -- Type / code / example — not related to withhold.
  -------------------------------------------------------------------------
  putStrLn "tool call"
  do
    -- type: tool call ≡ Post addressed to the tool
    let call :: Post Text
        call = toolCall "j" "calc" "1 2 3"
    assert "tool call addr is the tool" $ to call == ["calc"]
    assert "tool call body is the args" $ body call == "1 2 3"

    -- code: pure Agent that emits a tool-call Post
    let caller :: Agent (->) [Post Text] (Post Text) [Post Text]
        caller = tape callCalc
        human = mkPost "human" ["j"] "please sum 1 2 3"
        (outs, _) = runAgentShard caller (AgentSeat [] []) [human]
    assert "agent emits one tool-call post" $
      case outs of
        [p] -> to p == ["calc"] && body p == "1 2 3"
        _ -> False

    -- example: Port (Ends Post Post) — one token in, tool-call token out
    let sh :: Shard (State (AgentSeat [Post Text] Text, [Post Text], [Post Text])) [Post Text] [Post Text]
        sh =
          agentShard
            (gets (\(s, _, _) -> s))
            (\s -> modify (\(_, i, o) -> (s, i, o)))
            caller
        port :: Port (State (AgentSeat [Post Text] Text, [Post Text], [Post Text])) Text
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
      from pOut == "j" && to pOut == ["calc"] && body pOut == "1 2 3"
    assert "port carrier saw the human input" $
      length (asState seatPort) == 1

  -------------------------------------------------------------------------
  -- Withhold: force only some held content into the seat.
  -- Unrelated to tool calls — about what enters commit, not Post shape.
  -------------------------------------------------------------------------
  putStrLn "withhold"
  do
    let secret = mkPost "ops" ["j"] "bus emergency — do not show yet"
        public = mkPost "human" ["j"] "hi j"
        held = [secret, public] -- store exists; not all of it is delivered
        agent = tape (reply "j") :: Agent (->) [Post Text] (Post Text) [Post Text]

        -- release only public (withhold secret)
        released = filter ((== "human") . from) held
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
  -- Agent graph wiring
  --
  -- Algebraic graphs over agents: vertices are names, edges are channels.
  -- runGraph now routes by explicit subscriptions (loopWithSubs), so a post
  -- to a channel reaches every agent whose incoming edges include that
  -- channel.  Echo agents must be guarded: an agent that always replies will
  -- see its own routed replies and loop forever.
  -------------------------------------------------------------------------
  putStrLn "agent graph wiring"
  do
    let echo name hist =
          let p = peek hist
           in if from p == "human"
                then [mkPost name [] ("ack:" <> body p)]
                else []
        reg :: AgentRegistry
        reg =
          Map.fromList
            [ ("j", atomic (tape (echo "j"))),
              ("k", atomic (tape (echo "k")))
            ]
        t0 = [mkPost "human" ["bus"] "hello"]
        logBus = runGraph (bus ["j", "k"] "bus") reg t0
    assert "bus: both agents see the shared post and reply" $
      any ((== "j") . from) logBus && any ((== "k") . from) logBus

  do
    let summary :: [Post Text] -> [Post Text]
        summary hist =
          let p = peek hist
           in if from p == "leaf"
                then [mkPost "hub" [] ("summary: " <> body p)]
                else []
        leafEcho :: [Post Text] -> [Post Text]
        leafEcho hist =
          let p = peek hist
           in if from p == "human"
                then [mkPost "leaf" [] ("leaf:" <> body p)]
                else []
        reg :: AgentRegistry
        reg =
          Map.fromList
            [ ("hub", atomic (tape summary)),
              ("leaf", atomic (tape leafEcho))
            ]
        -- leaf subscribes to the "hub" channel, so the seed must be posted
        -- there for leaf to receive it first.
        t0 = [mkPost "human" ["hub"] "data"]
        logStar = runGraph (star "hub" ["leaf"] "hub" "leaf") reg t0
    assert "star: hub posts a summary after receiving from leaf" $
      any ((== "hub") . from) logStar

  do
    let echo name hist =
          let p = peek hist
           in if from p == "human"
                then [mkPost name [] ("ack:" <> body p)]
                else []
        reg :: AgentRegistry
        reg =
          Map.fromList
            [ ("j", atomic (tape (echo "j"))),
              ("k", atomic (tape (echo "k")))
            ]
        t0 = [mkPost "human" ["bus"] "hello"]
        g = bus ["j", "k"] "bus"
        isolated = LG.overlay (LG.vertex "j") (LG.vertex "k")
        logFull = runGraph g reg t0
        logWithIsolated = runGraph (LG.overlay g isolated) reg t0
    assert "overlay with isolated vertices is a no-op" $
      logFull == logWithIsolated

  -------------------------------------------------------------------------
  -- Self-loop: one seat wired to itself through a card.
  --
  -- Posts are addressed to a card ("xyzzy"), never to seats; the seat
  -- subscribes to the card, so its own replies re-enter its inbox next
  -- round.  The grammar marks are the termination language: 🟢/🔵 halt,
  -- 🔴 escalates, silence is quiescence.  fork ⟜ id (AgentSeat is pure
  -- data); fan-in lands its summary on the main stream as exactly one post.
  -------------------------------------------------------------------------
  putStrLn "self-loop"

  -------------------------------------------------------------------------
  -- A self-wired deterministic agent acks itself forever unless a halt mark
  -- lands.  Here the policy echoes card posts back to the card and emits
  -- "🟢 landed" after k rounds; silence follows the mark, so the loop
  -- reaches quiescence with a bounded log.
  -------------------------------------------------------------------------
  putStrLn "self-loop halts on mark"
  do
    let k = 3 :: Int
        roster = [("xyzzy", tape (selfLoopPolicy "xyzzy" k))]
        t0 = [mkPost "human" ["xyzzy"] "start"]
        (states, tF, derivs) = loop roster t0
    assert "self-loop halts on mark: log is 1 seed + k replies + 1 halt" $
      length tF == 1 + k + 1
    assert "self-loop halts on mark: final post carries the 🟢 mark" $
      "🟢" `T.isPrefixOf` body (peek tF)
    assert "self-loop halts on mark: log stops growing after the halt post (silent last turn)" $
      null (dOutputs (last derivs))
    assert "self-loop halts on mark: quiescence reached" $
      all (\(_n, st) -> not (hasPending @Text st)) states

  -------------------------------------------------------------------------
  -- Silence is quiescence: with no new card-addressed posts the loop
  -- machinery is identity on the log and records no derivations.
  -------------------------------------------------------------------------
  putStrLn "silence is quiescence"
  do
    let quietLog :: [Post Text]
        quietLog = [mkPost "human" ["someone-else"] "not addressed to the card"]
        (_qStates, qLog, qDerivs) = loop [("xyzzy", tape (reply "xyzzy"))] quietLog
    assert "silence is quiescence: loop with no card posts is identity on the log" $
      qLog == quietLog
    assert "silence is quiescence: no derivations" $
      null qDerivs

  -------------------------------------------------------------------------
  -- fork ⟜ id: AgentSeat is pure data, so forking is copying the value.
  -- Running both copies gives identical outputs and identical seats.
  -------------------------------------------------------------------------
  putStrLn "fork is id"
  do
    let agent = tape (reply "xyzzy") :: Agent (->) [Post Text] (Post Text) [Post Text]
        p1 = mkPost "human" ["xyzzy"] "one"
        p2 = mkPost "human" ["xyzzy"] "two"
        (_outs0, seat0) = runAgentShard agent (AgentSeat [] []) [p1]
        forked = seat0
        (outsA, seatA) = runAgentShard agent seat0 [p2]
        (outsB, seatB) = runAgentShard agent forked [p2]
    assert "fork is id: duplicated seat gives identical outputs" $
      outsA == outsB
    assert "fork is id: duplicated seat gives identical resulting seats" $
      seatA == seatB
    assert "fork is id: carrier advanced on both copies" $
      length (asState seatA) == 2

  -------------------------------------------------------------------------
  -- fan-out / fan-in: run prompt[i] through fork i, fold the fork outputs
  -- with a pure summary into ONE card-addressed post, commit it to the main
  -- seat.  Forks are private scratch and die; only the fan-in is public.
  -------------------------------------------------------------------------
  putStrLn "fan-in lands exactly one post"
  do
    let worker = tape (reply "xyzzy") :: Agent (->) [Post Text] (Post Text) [Post Text]
        main0 = AgentSeat [] [] :: AgentSeat [Post Text] Text
        prompt1 = mkPost "human" ["xyzzy"] "task one"
        prompt2 = mkPost "human" ["xyzzy"] "task two"
        (outs1, fork1) = runAgentShard worker main0 [prompt1]
        (outs2, fork2) = runAgentShard worker main0 [prompt2]
        snap1 = fork1
        snap2 = fork2
        summaryPosts =
          [ mkPost
              "xyzzy"
              ["xyzzy"]
              ("summary: " <> T.intercalate " + " (map body (outs1 ++ outs2)))
          ]
        (mainOuts, main1) = runAgentShard worker main0 summaryPosts
    assert "fan-in: the summary is exactly one post" $
      length summaryPosts == 1
    assert "fan-in lands exactly one post: main carrier grew by exactly 1" $
      length (asState main1) == length (asState main0) + 1
    assert "fan-in lands exactly one post: main seat outputs respond to the summary only" $
      length mainOuts == 1 && "ack: summary:" `T.isPrefixOf` body (peek mainOuts)
    assert "fan-in lands exactly one post: forks unchanged by the main-seat commit" $
      fork1 == snap1 && fork2 == snap2
    assert "fan-in lands exactly one post: each fork saw only its own prompt" $
      map body (asState fork1) == ["task one"]
        && map body (asState fork2) == ["task two"]

  -------------------------------------------------------------------------
  -- Neutral grammar: two seats on the same card, names carry no role.
  -- 'loop' subscribes each seat to its own name, so both seats are
  -- hand-scheduled with ["xyzzy"] subscriptions (as in "multi-round
  -- pure").  Swapping seat names in the schedule permutes the `from`
  -- fields and leaves the bodies untouched.
  -------------------------------------------------------------------------
  putStrLn "neutral grammar: seat-name swap"
  do
    let seed = mkPost "human" ["xyzzy"] "start"
        t0 = [seed]
        agentA = tape (cardEcho "a") :: Agent (->) [Post Text] (Post Text) [Post Text]
        agentB = tape (cardEcho "b") :: Agent (->) [Post Text] (Post Text) [Post Text]
        -- one round: first seat turns, new card posts route to both inboxes
        -- (self-loop: its own reply re-enters), then the second seat turns.
        mkRound first second (stF, stS, lg) =
          let (stF', lg1, _) = turn first stF lg
              stS' = feedState (diffLog lg lg1) stS
              stF'' = feedState (diffLog lg lg1) stF'
              (stS'', lg2, _) = turn second stS' lg1
              stF3 = feedState (diffLog lg1 lg2) stF''
              stS3 = feedState (diffLog lg1 lg2) stS''
           in (stF3, stS3, lg2)
        pending :: (AgentState [Post Text] [Post Text], AgentState [Post Text] [Post Text], [Post Text]) -> Bool
        pending (stF, stS, _) = hasPending @Text stF || hasPending @Text stS
        settle round0 s0 = head (dropWhile pending (iterate round0 s0))
        states0 = (seedState ["xyzzy"] t0, seedState ["xyzzy"] t0, t0)
        (_, _, lgAB) = settle (mkRound agentA agentB) states0
        (_, _, lgBA) = settle (mkRound agentB agentA) states0
        swapName n
          | n == "a" = "b"
          | n == "b" = "a"
          | otherwise = n
    assert "seat-name swap: bounded log (1 seed + one halt reply each)" $
      length lgAB == 3 && length lgBA == 3
    assert "seat-name swap: same bodies in same order" $
      map body lgAB == map body lgBA
    assert "seat-name swap: from fields are exactly swapped" $
      map (swapName . from) lgAB == map from lgBA

  -------------------------------------------------------------------------
  -- Race / await tensors
  --
  -- raceP  = pure orElse: left branch speaks unless silent, otherwise right.
  -- awaitP = product collapse: both branches speak, emits concatenated.
  -- silence [] is the zero of race and the unit of await.
  -------------------------------------------------------------------------
  putStrLn "race await tensors"

  -------------------------------------------------------------------------
  -- R0: race = orElse with silence as zero
  -------------------------------------------------------------------------
  putStrLn "race is orElse with silence as zero"
  do
    let f :: [Post Text] -> [Post Text]
        f = const [mkPost "f" [] "f"]
        g :: [Post Text] -> [Post Text]
        g = const [mkPost "g" [] "g"]
        h :: [Post Text] -> [Post Text]
        h = const [mkPost "h" [] "h"]
    assert "race: silent is left identity" $ raceP silent f [] == f []
    assert "race: silent is right identity" $ raceP f silent [] == f []
    assert "race: associativity of bias" $ raceP (raceP f g) h [] == raceP f (raceP g h) []
    assert "race: left bias (left speaks)" $ raceP f g [] == f []
    assert "race: fallback to right when left silent" $ raceP silent g [] == g []
    assert "race: both silent is silent" $ null (raceP silent silent [])

  -------------------------------------------------------------------------
  -- R1: await = product with silence as unit
  -------------------------------------------------------------------------
  putStrLn "await is product with silence as unit"
  do
    let f :: [Post Text] -> [Post Text]
        f = const [mkPost "f" [] "f"]
        g :: [Post Text] -> [Post Text]
        g = const [mkPost "g" [] "g"]
        h :: [Post Text] -> [Post Text]
        h = const [mkPost "h" [] "h"]
    assert "await: silent is left unit" $ awaitP silent f [] == f []
    assert "await: silent is right unit" $ awaitP f silent [] == f []
    assert "await: associativity" $ awaitP (awaitP f g) h [] == awaitP f (awaitP g h) []
    assert "await: order is observable (not a bag)" $ awaitP f g [] /= awaitP g f []

  -------------------------------------------------------------------------
  -- R2: race takes the whole winning branch emit
  -------------------------------------------------------------------------
  putStrLn "race takes the whole winning branch emit"
  do
    let f2 :: [Post Text] -> [Post Text]
        f2 = const [mkPost "f" [] "f1", mkPost "f" [] "f2"]
        g1 :: [Post Text] -> [Post Text]
        g1 = const [mkPost "g" [] "g"]
    assert "race: left branch whole emit wins" $ raceP f2 g1 [] == f2 []
    assert "race: not just the first post of concat" $ raceP f2 g1 [] /= take 1 (f2 [] ++ g1 [])

  -------------------------------------------------------------------------
  -- R3: exchange probe
  --
  -- Pure race outcomes are the symmetric closure under left/right bias.
  -- Correlated choice (race of awaits) yields fewer outcomes than
  -- independent choice (await of races): the mixed pairs are reachable only
  -- when each side may decide independently.
  -------------------------------------------------------------------------
  putStrLn "exchange probe"
  do
    let a :: [Post Text] -> [Post Text]
        a = const [mkPost "a" [] "a"]
        b :: [Post Text] -> [Post Text]
        b = const [mkPost "b" [] "b"]
        c :: [Post Text] -> [Post Text]
        c = const [mkPost "c" [] "c"]
        d :: [Post Text] -> [Post Text]
        d = const [mkPost "d" [] "d"]
        leftHand = outcomesRace (awaitP a c) (awaitP b d) []
        rightHand = [x <> y | x <- outcomesRace a b [], y <- outcomesRace c d []]
        isSubset xs ys = all (`elem` ys) xs
    assert "exchange: correlated outcomes are a subset of independent outcomes" $
      isSubset leftHand rightHand
    assert "exchange: mixed outcome a+d exists only in independent choice" $
      [mkPost "a" [] "a", mkPost "d" [] "d"] `elem` rightHand
        && [mkPost "a" [] "a", mkPost "d" [] "d"] `notElem` leftHand

  -------------------------------------------------------------------------
  -- Seat-level tensors
  -------------------------------------------------------------------------
  putStrLn "seat-level tensors"

  putStrLn "awaitA is product with silent unit"
  do
    let p = mkPost "test" [] "p"
        a = constAgent [p]
        z = constAgent []
        ins = [mkPost "human" [] "one"]
        (outsAZ, _) = runAgentShard (awaitA a z) (AgentSeat ([], []) []) ins
        (outsZA, _) = runAgentShard (awaitA z a) (AgentSeat ([], []) []) ins
        (outsA, _) = runAgentShard a (AgentSeat [] []) ins
    assert "awaitA: silent agent is right unit (outputs)" $ outsAZ == outsA
    assert "awaitA: silent agent is left unit (outputs)" $ outsZA == outsA

  putStrLn "awaitA associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constAgent [p]
        b = constAgent [q]
        c = constAgent [r]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        left = awaitA (awaitA a b) c
        right = awaitA a (awaitA b c)
        (outsL, _) = runAgentShard left (AgentSeat (([], []), []) []) ins
        (outsR, _) = runAgentShard right (AgentSeat ([], ([], [])) []) ins
    assert "awaitA: associativity of outputs" $ outsL == outsR

  putStrLn "raceA is coproduct with silent unit / left bias"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        a = constAgent [p]
        b = constAgent [q]
        z = constAgent []
        ins = [mkPost "human" [] "one"]
        (outsAB, _) = runAgentShard (raceA a b) (AgentSeat ([], []) []) ins
        (outsAZ, _) = runAgentShard (raceA a z) (AgentSeat ([], []) []) ins
        (outsZA, _) = runAgentShard (raceA z a) (AgentSeat ([], []) []) ins
    assert "raceA: left bias (left speaks)" $ outsAB == [p]
    assert "raceA: silent right unit" $ outsAZ == [p]
    assert "raceA: silent left falls back to right" $ outsZA == [p]

  putStrLn "raceA associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constAgent [p]
        b = constAgent [q]
        c = constAgent [r]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        left = raceA (raceA a b) c
        right = raceA a (raceA b c)
        (outsL, _) = runAgentShard left (AgentSeat (([], []), []) []) ins
        (outsR, _) = runAgentShard right (AgentSeat ([], ([], [])) []) ins
    assert "raceA: associativity of outputs" $ outsL == outsR

  putStrLn "seat-level race agrees with policy-level race"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        f = const [p] :: [Post Text] -> [Post Text]
        g = const [q] :: [Post Text] -> [Post Text]
        a = constAgent [p]
        b = constAgent [q]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        (outsA, _) = runAgentShard (raceA a b) (AgentSeat ([], []) []) ins
    assert "raceA outputs match raceP per input" $
      outsA == concat (replicate (length ins) (raceP f g []))

  -------------------------------------------------------------------------
  -- STM rung
  --
  -- retry = silence (await), orElse = left-biased race,
  -- BlockedIndefinitelyOnSTM = dormancy of the whole meeting.
  -------------------------------------------------------------------------
  putStrLn "stm rung"

  putStrLn "retry is silence"
  do
    q <- newTQueueIO
    -- An empty queue makes 'readTQueue' retry; timeout observes the block.
    blocked <- timeout 100000 (atomically (readTQueue q))
    assert "retry: empty commit blocks" $ blocked == Nothing
    -- Once a writer fills the queue, the retry resumes.
    let p = mkPost "stm" [] "hello"
    _ <- forkIO $ do
      threadDelay 100000
      atomically (writeTQueue q p)
    resumed <- timeout 500000 (atomically (readTQueue q))
    assert "retry: resumes after commit" $ fmap body resumed == Just "hello"
    -- Extensional equivalence: a retrying emit with an orElse fallback []
    -- equals the silent agent on an empty commit.
    commitVar <- newTVarIO ([] :: [Post Text])
    let stmEmit :: STM [Post Text]
        stmEmit =
          readTVar commitVar >>= \case
            [] -> retry
            xs -> writeTVar commitVar [] >> pure xs
    silentFallback <- atomically (stmEmit `orElse` pure [])
    assert "retry: extensionally silent on empty commit" $ null silentFallback
    atomically (writeTVar commitVar [p])
    nonEmptyEmit <- atomically stmEmit
    assert "retry: emits when commit is non-empty" $ nonEmptyEmit == [p]

  putStrLn "orElse is lawful race"
  do
    leftFlag <- newTVarIO True
    rightFlag <- newTVarIO False
    let leftPost = mkPost "l" [] "left"
        rightPost = mkPost "r" [] "right"
        raceBranch flag branchPost = do
          ok <- readTVar flag
          if ok then pure [branchPost] else retry
        raceSTM = raceBranch leftFlag leftPost `orElse` raceBranch rightFlag rightPost
    resA <- atomically raceSTM
    assert "orElse: left wins when only left ready" $ resA == [leftPost]
    atomically $ do
      writeTVar leftFlag False
      writeTVar rightFlag True
    resB <- atomically raceSTM
    assert "orElse: falls back to right when left retries" $ resB == [rightPost]
    atomically (writeTVar leftFlag True)
    resC <- atomically raceSTM
    assert "orElse: left bias when both ready" $ resC == [leftPost]

  putStrLn "dormancy is BlockedIndefinitelyOnSTM"
  do
    let isDormant =
          catch
            (atomically (retry `orElse` retry) >> pure False)
            (\e -> pure (isJust (fromException @BlockedIndefinitelyOnSTM e)))
    dormant <- isDormant
    assert "dormancy: all-retry raises BlockedIndefinitelyOnSTM" dormant

  -------------------------------------------------------------------------
  -- Kleisli STM tensors
  --
  -- The same product/coproduct tensors, now effectful: state lives in STM,
  -- composition is Kleisli sequential, and the oracles mirror the pure
  -- seat-level ones.
  -------------------------------------------------------------------------
  putStrLn "S-agent tensors"

  putStrLn "awaitS is product with silent unit"
  do
    let p = mkPost "test" [] "p"
        a = constAgentS [p]
        z = constAgentS []
        ins = [mkPost "human" [] "one"]
    (outsAZ, _) <- runAgentS (awaitS a z) ([], []) ins
    (outsZA, _) <- runAgentS (awaitS z a) ([], []) ins
    (outsA, _) <- runAgentS a [] ins
    assert "awaitS: silent agent is right unit (outputs)" $ outsAZ == outsA
    assert "awaitS: silent agent is left unit (outputs)" $ outsZA == outsA

  putStrLn "awaitS associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constAgentS [p]
        b = constAgentS [q]
        c = constAgentS [r]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        left = awaitS (awaitS a b) c
        right = awaitS a (awaitS b c)
    (outsL, _) <- runAgentS left (([], []), []) ins
    (outsR, _) <- runAgentS right ([], ([], [])) ins
    assert "awaitS: associativity of outputs" $ outsL == outsR

  putStrLn "raceS is coproduct with silent unit / left bias"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        a = constAgentS [p]
        b = constAgentS [q]
        z = constAgentS []
        ins = [mkPost "human" [] "one"]
    (outsAB, _) <- runAgentS (raceS a b) ([], []) ins
    (outsAZ, _) <- runAgentS (raceS a z) ([], []) ins
    (outsZA, _) <- runAgentS (raceS z a) ([], []) ins
    assert "raceS: left bias (left speaks)" $ outsAB == [p]
    assert "raceS: silent right unit" $ outsAZ == [p]
    assert "raceS: silent left falls back to right" $ outsZA == [p]

  putStrLn "raceS associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constAgentS [p]
        b = constAgentS [q]
        c = constAgentS [r]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        left = raceS (raceS a b) c
        right = raceS a (raceS b c)
    (outsL, _) <- runAgentS left (([], []), []) ins
    (outsR, _) <- runAgentS right ([], ([], [])) ins
    assert "raceS: associativity of outputs" $ outsL == outsR

  putStrLn "S-agent race agrees with pure seat-level race"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        aPure = constAgent [p]
        bPure = constAgent [q]
        aSTM = constAgentS [p]
        bSTM = constAgentS [q]
        ins = [mkPost "human" [] "one", mkPost "human" [] "two"]
        (outsPure, _) = runAgentShard (raceA aPure bPure) (AgentSeat ([], []) []) ins
    (outsSTM, _) <- runAgentS (raceS aSTM bSTM) ([], []) ins
    assert "raceS outputs match raceA outputs" $ outsSTM == outsPure

  -------------------------------------------------------------------------
  -- X-agent temporal race: first mark wins, losers cancelled
  -------------------------------------------------------------------------
  putStrLn "X-agent temporal race"

  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        seed = mkPost "human" [] "one"
        fastLeft = System $ Kleisli $ \(_, _) -> pure ((), ([p], ()))
        slowRight = System $ Kleisli $ \(_, _) -> threadDelay 10000 >> pure ((), ([q], ()))
    (outs, _) <- runAgentM (raceIO fastLeft slowRight) ((), ()) seed
    assert "raceIO: fast left wins" $ outs == [p]

  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        seed = mkPost "human" [] "one"
        slowLeft = System $ Kleisli $ \(_, _) -> threadDelay 10000 >> pure ((), ([p], ()))
        fastRight = System $ Kleisli $ \(_, _) -> pure ((), ([q], ()))
    (outs, _) <- runAgentM (raceIO slowLeft fastRight) ((), ()) seed
    assert "raceIO: fast right wins" $ outs == [q]

  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        seed = mkPost "human" [] "one"
        fastLeft = System $ Kleisli $ \(_, _) -> pure ((), ([p], ()))
        fastRight = System $ Kleisli $ \(_, _) -> pure ((), ([q], ()))
    (outs, _) <- runAgentM (raceIO fastLeft fastRight) ((), ()) seed
    assert "raceIO: both emit -> one of them" $ outs == [p] || outs == [q]

  -------------------------------------------------------------------------
  -- Container dial: within-turn order is not observable (Bag / Seq)
  -------------------------------------------------------------------------
  putStrLn "Container dial"

  do
    let a = mkPost "alice" [] "a"
        b = mkPost "bob" [] "b"
        c = mkPost "carol" [] "c"
        outPost x = x {body = "out:" <> body x}
        sh = shard (\xs -> put xs) (do xs <- get; put []; pure (map outPost xs))
        runBag sh' ins = do
          (outs, _) <- closeShardIO sh' ins []
          pure (toBag outs)
    bag1 <- runBag sh [a, b, c]
    bag2 <- runBag sh [c, a, b]
    assert "permuting input preserves output bag" $ bag1 == bag2

  -------------------------------------------------------------------------
  -- S-agent self-loop: quiescence via orElse
  --
  -- The agent reads from and writes to the same STM end.  When the end is
  -- empty the loop retries; 'orElse' catches the retry and returns the state.
  -------------------------------------------------------------------------
  putStrLn "S-agent self-loop"

  do
    let k = 3 :: Int
        selfEcho :: AgentS [Post Text] (Post Text)
        selfEcho = agentM $ tape $ \hist ->
          if length hist >= k
            then []
            else [mkPost "self" ["self"] ("echo:" <> T.pack (show (length hist + 1)))]
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

  -------------------------------------------------------------------------
  -- Spikes: re-spellings of the self-loop frame
  --
  -- Spike A (composition): the frame as Kleisli composition; the loop is
  -- 'fix' plus 'orElse'.  No do-notation or bind in the frame itself.
  --
  -- Spike B (bundles): the same composition, but the wire carries @[a]@;
  -- the agent folds a whole bundle per frame ('stepsS').  Empty bundles
  -- are not written — an empty bundle on the wire would circulate forever.
  -------------------------------------------------------------------------
  putStrLn "S-agent self-loop spikes"

  do
    let k = 3 :: Int
        selfEcho :: AgentS [Post Text] (Post Text)
        selfEcho = agentM $ tape $ \hist ->
          if length hist >= k
            then []
            else [mkPost "self" ["self"] ("echo:" <> T.pack (show (length hist + 1)))]
        seed = mkPost "human" ["self"] "start"
        drainEnd :: Ends (Kleisli STM) a a -> STM [a]
        drainEnd ends = go []
          where
            go acc = (readEndSTM ends >>= \a -> go (a : acc)) `orElse` pure (reverse acc)

        -- | orElse lifted to state-threading Kleisli arrows.
        orElseA :: Kleisli STM s s -> Kleisli STM s s -> Kleisli STM s s
        orElseA (Kleisli f) (Kleisli g) = Kleisli $ \s -> f s `orElse` g s

        -- | Run a frame until the read end retries (quiescence).
        quiesce :: Kleisli STM s s -> Kleisli STM s s
        quiesce frame = fix $ \go -> (frame C.>>> go) `orElseA` C.id

        -- | Spike A: one token per frame, no do/bind in the frame.
        frameToken :: AgentS s a -> Ends (Kleisli STM) a a -> Ends (Kleisli STM) a a -> Kleisli STM s s
        frameToken agent inbox outbox =
          Kleisli (\s -> (s,) <$> readEndSTM inbox)
            C.>>> Kleisli (uncurry (stepS agent))
            C.>>> Kleisli (\(s', outs) -> s' <$ traverse_ (writeEndSTM outbox) outs)

        -- | Spike B: one bundle per frame over a bundle wire.
        frameBundle :: AgentS s a -> Ends (Kleisli STM) [a] [a] -> Ends (Kleisli STM) [a] [a] -> Kleisli STM s s
        frameBundle agent inbox outbox =
          Kleisli (\s -> (s,) <$> readEndSTM inbox)
            C.>>> Kleisli (uncurry (stepsS agent))
            C.>>> Kleisli (\(s', outs) -> s' <$ unless (null outs) (writeEndSTM outbox outs))

    -- Spike A: composed token frame
    (sTok, remTok) <- do
      ends <- atomically $ openSTM (Unbounded :: Queue (Post Text))
      atomically $ writeEndSTM ends seed
      atomically $ do
        s' <- runKleisli (quiesce (frameToken selfEcho ends ends)) []
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
        s' <- runKleisli (quiesce (frameBundle selfEcho ends ends)) []
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

  -------------------------------------------------------------------------
  -- Loop self-loop: the queue self-loop as a Loop Either citizen
  -------------------------------------------------------------------------
  putStrLn "Loop self-loop"

  do
    let k = 3 :: Int
        selfEcho :: AgentS [Post Text] (Post Text)
        selfEcho = agentM $ tape $ \hist ->
          if length hist >= k
            then []
            else [mkPost "self" ["self"] ("echo:" <> T.pack (show (length hist + 1)))]
        seed = mkPost "human" ["self"] "start"
        drainEnd :: Ends (Kleisli STM) a a -> STM [a]
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

  -------------------------------------------------------------------------
  -- The mark grammar as a type (Circuit.Agent.Mark)
  --
  -- The level-0 grammar: finite K, stateless predicate.  The free boundary
  -- K + payload, where the 🟡/quiescent collision is pinned, not folklore.
  -------------------------------------------------------------------------
  putStrLn "mark grammar"
  do
    assert "render/parse round-trips every mark" $
      all (\m -> parseMark (markGlyph m) == Just m) [minBound .. maxBound]
    assert "parse tolerates the emoji variation selector" $
      parseMark "↩️ amend this" == Just Amendment
        && parseMark "🟢\xFE0F landed" == Just Landed
    assert "plain bodies carry no mark" $
      parseMark "hello" == Nothing && parseMark "" == Nothing
    assert "halt marks are Landed and StandDown" $
      all isHalt [Landed, StandDown]
        && not (any isHalt [Motion, Consent, Amendment, Escalate])
    assert "escalation is its own class" $
      isEscalate Escalate && not (isEscalate Landed)
    assert "markOf reads the post body" $
      markOf (mkPost "a" ["b"] "🟢 landed") == Just Landed
        && markOf (mkPost "a" ["b"] "no mark") == Nothing
    -- The pinned collision: legacy quiescence posts used 🟡, which is a
    -- Motion here.  That ambiguity is why quiescence moved to 🔵; this
    -- oracle stops anyone reintroducing it quietly.
    assert "legacy 🟡 quiescent body parses as Motion (the pinned collision)" $
      parseMark "🟡 quiescent after 10 empty cycles" == Just Motion

  -------------------------------------------------------------------------
  -- Mark-driven halt (Circuit.Agent.Machina)
  --
  -- The first machina graduate: spinMark halts on a mark token, and markLoop
  -- is the same halt as a Loop Either citizen.
  -------------------------------------------------------------------------
  putStrLn "mark-driven halt"
  do
    let isHaltMark p = maybe False isHalt (markOf p)
        step acc p = p : acc
        seed = mkPost "human" ["self"] "seed"
        one = mkPost "human" ["self"] "one"
        two = mkPost "human" ["self"] "two"
        halt = mkPost "human" ["self"] "🟢 landed"
        writeAll ends = do
          writeEndSTM ends seed
          writeEndSTM ends one
          writeEndSTM ends two
          writeEndSTM ends halt
    endsSpin <- atomically $ openSTM (Unbounded :: Queue (Post Text))
    atomically $ writeAll endsSpin
    accSpin <- atomically $ runKleisli (spinMark isHaltMark step endsSpin) []
    endsLoop <- atomically $ openSTM (Unbounded :: Queue (Post Text))
    atomically $ writeAll endsLoop
    accLoop <- atomically $ runKleisli (run (markLoop isHaltMark step endsLoop)) []
    assert "spinMark accumulated the three normal posts" $
      length accSpin == 3
    assert "spinMark consumed the halt mark as the halt token" $
      not (any (\p -> body p == "🟢 landed") accSpin)
    assert "markLoop agrees with spinMark" $
      accLoop == accSpin

  -------------------------------------------------------------------------
  -- Shard-level tensors (StateT [Post Text] IO)
  --
  -- These are the semantic citizens that free-agent 'FreeSeat' terms fold
  -- into.  Laws are tested directly on shards, independent of any free syntax.
  -------------------------------------------------------------------------
  let constShard outs =
        shard
          (\xs -> put xs)
          (put [] >> pure outs)
      tagShard suffix =
        shard
          (\xs -> put xs)
          ( do
              xs <- get
              put []
              pure [x {body = body x <> suffix} | x <- xs]
          )

  putStrLn "shard-level tensors"

  putStrLn "silent shard"
  do
    let posts = [mkPost "human" ["bot"] "x"]
    (outs, st) <- closeShardIO silentShard posts []
    assert "silent shard emits empty" $ null outs
    assert "silent shard clears buffer" $ null st

  putStrLn "awaitShard is product with silent unit"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        a = constShard [p]
        b = constShard [q]
        z = silentShard
        posts = [mkPost "human" [] "one"]
    (outsAZ, _) <- closeShardIO (awaitShard z a) posts []
    (outsZA, _) <- closeShardIO (awaitShard a z) posts []
    (outsA, _) <- closeShardIO a posts []
    (outsAB, _) <- closeShardIO (awaitShard a b) posts []
    assert "awaitShard: silent is right unit" $ outsAZ == outsA
    assert "awaitShard: silent is left unit" $ outsZA == outsA
    assert "awaitShard: both branches speak" $ outsAB == [p, q]

  putStrLn "awaitShard associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constShard [p]
        b = constShard [q]
        c = constShard [r]
        posts = [mkPost "human" [] "one"]
        left = awaitShard (awaitShard a b) c
        right = awaitShard a (awaitShard b c)
    (outsL, _) <- closeShardIO left posts []
    (outsR, _) <- closeShardIO right posts []
    assert "awaitShard associative" $ outsL == outsR

  putStrLn "raceShard is coproduct with silent unit / left bias"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        a = constShard [p]
        b = constShard [q]
        z = silentShard
        posts = [mkPost "human" [] "one"]
    (outsAB, _) <- closeShardIO (raceShard a b) posts []
    (outsAZ, _) <- closeShardIO (raceShard a z) posts []
    (outsZA, _) <- closeShardIO (raceShard z a) posts []
    assert "raceShard: left bias" $ outsAB == [p]
    assert "raceShard: silent right unit" $ outsAZ == [p]
    assert "raceShard: silent left falls back" $ outsZA == [p]

  putStrLn "raceShard associativity"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        r = mkPost "test" [] "r"
        a = constShard [p]
        b = constShard [q]
        c = constShard [r]
        posts = [mkPost "human" [] "one"]
        left = raceShard (raceShard a b) c
        right = raceShard a (raceShard b c)
    (outsL, _) <- closeShardIO left posts []
    (outsR, _) <- closeShardIO right posts []
    assert "raceShard associative" $ outsL == outsR

  putStrLn "raceShard agrees with seat-level raceA"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        posts = [mkPost "human" [] "one"]
        (outsAgent, _) =
          runAgentShard
            (raceA (tape (const [p])) (tape (const [q])))
            (AgentSeat ([], []) [])
            posts
    (outsShard, _) <- closeShardIO (raceShard (constShard [p]) (constShard [q])) posts []
    assert "raceShard outputs match raceA outputs" $ outsShard == outsAgent

  putStrLn "fanOutShard runs branches on copies"
  do
    let p = mkPost "test" [] "p"
        q = mkPost "test" [] "q"
        posts = [mkPost "human" [] "one"]
    (outs, _) <- closeShardIO (fanOutShard [constShard [p], constShard [q]]) posts []
    assert "fanOutShard: both branches see input" $ outs == [p, q]

  putStrLn "fanInShard summarizes branch outputs"
  do
    let posts = [mkPost "human" [] "one"]
        summary pss = [mkPost "sum" [] (T.intercalate "+" (map body (concat pss)))]
    (outs, _) <- closeShardIO (fanInShard summary [tagShard "-a", tagShard "-b"]) posts []
    assert "fanInShard: summary is one post" $ length outs == 1
    assert "fanInShard: summary body collects branches" $
      case outs of
        [o] -> body o == "one-a+one-b"
        _ -> False

  putStrLn "fanInShard with synthesisSummary is honest by construction"
  do
    let posts = [mkPost "human" [] "one"]
        branchA = constShard [mkPost "a" [] "x"]
        branchB = constShard [mkPost "b" [] "y"]
        summary = synthesisSummary "sum" ["human"] [0, 1] (T.intercalate "+" . map body . concat)
    (outs, _) <- closeShardIO (fanInShard summary [branchA, branchB]) posts []
    assert "honest fan-in: one synthesis post" $ length outs == 1
    assert "honest fan-in: ancestry cites every branch output by id" $
      case outs of
        [o] -> thread o == [0, 1] && body o == "x+y"
        _ -> False
    assert "honest fan-in: empty body is quiet" $
      null (synthesisSummary "sum" [] [0] (const "") [[mkPost "a" [] "x"]])

  -------------------------------------------------------------------------
  -- Tier F: framing laws
  --
  -- Stamped Text JSON Lines round-trip, legacy parsing, and Jsonl typeclass
  -- laws. These were formerly in test/Test.hs under tasty.
  -------------------------------------------------------------------------
  putStrLn "Tier F: framing laws"
  do
    let p = Post "kimi" ["bus"] [3] ("hello \nworld ♪" :: Text)
        stored = Stamped 42 "2026-08-03T23:10:25" p
    assert "F0: round-trip unicode and embedded newlines" $
      parseLine (frameStored stored) == Just stored

  do
    let p = Post "a" ["b"] [2] ("body" :: Text)
        stored = Stamped 7 "2026-08-03T23:10:25" p
    assert "F1: id is preserved across round-trip" $
      maybe False ((== 7) . stampId) (parseLine (frameStored stored))

  do
    let line = "{\"ts\":\"2026-08-03T12:00:00\",\"sender\":\"kimi\",\"body\":\"legacy\"}" :: Text
    assert "F2: legacy triple round-trip" $
      case parseLineAt 5 line of
        Just s ->
          stampId s == 5
            && from (stamped s) == "kimi"
            && body (stamped s) == "legacy"
            && to (stamped s) == []
            && thread (stamped s) == []
        Nothing -> False

  do
    let line = "[2026-08-03T12:00:00] kimi: legacy bracket" :: Text
    assert "F3: legacy bracket round-trip" $
      case parseLineAt 3 line of
        Just s ->
          stampId s == 3
            && from (stamped s) == "kimi"
            && body (stamped s) == "legacy bracket"
        Nothing -> False

  do
    let p = Post "kimi" ["bus"] [] ("hi" :: Text)
        stored = Stamped 1 "2026-08-03T23:10:25" p
    assert "F4: parseMessage extracts (from, body) on stamped line" $
      parseMessage (frameStored stored) == Just ("kimi", "hi")

  do
    let p = Post "kimi" ["bus"] [] ("hi" :: Text)
        s = Stamped 9 "2026-08-03T23:10:25" p
        rendered = renderStored s
    assert "F5: renderStored includes id@ts" $
      "[9@2026-08-03T23:10:25]" `T.isPrefixOf` rendered
    assert "F6: renderStored contains from:body" $
      "kimi: hi" `T.isSuffixOf` rendered

  do
    let a = Stamped 0 "t0" (Post "a" [] [] "A")
        b = Stamped 1 "t1" (Post "b" [] [] "B")
        j = snoc (snoc (Jsonl []) a) b
    assert "F7: Snoc then Uncons peels oldest first" $
      case uncons j of
        These a' (Jsonl rest1) ->
          a' == a
            && case uncons (Jsonl rest1) of
              This b' -> b' == b
              _ -> False
        _ -> False

  do
    let posts =
          [ Stamped 0 "t0" (Post "a" ["x"] [1, 2] "multi\nline ♪"),
            Stamped 1 "t1" (Post "b" ["y"] [] "body2"),
            Stamped 2 "t2" (Post "c" [] [] "body3")
          ] :: [Stamped Text]
        j = foldl snoc (Jsonl []) posts
        go (Jsonl []) = []
        go js =
          case uncons js of
            This p -> [p]
            These p js' -> p : go js'
            That _ -> []
    assert "F8: Recreate from Jsonl via snoc/uncons" $
      go j == posts

  -------------------------------------------------------------------------
  -- Query-to-post adapters (from old cli-axioma)
  -------------------------------------------------------------------------
  do
    let p1 :: Post Text
        p1 = mkPost "tony" ["kimi"] "hello"
        p2 :: Post Text
        p2 = mkPost "grok" ["kimi", "tony"] "line1\nline2"

    putStrLn "sessionPrompt / replyPosts (data side)"
    assert
      "sessionPrompt concatenates bodies oldest-first"
      (sessionPrompt [p1, p2] == "hello\nline1\nline2")
    assert
      "replyPosts addresses last sender, preserves wire"
      (replyPosts "kimi" [p1, p2] [1] "sure" == [replyTo "kimi" 1 p2 "sure"])
    assert
      "whitespace reply is quiet"
      (replyPosts "kimi" [p1] [0] "  \n " == [])
    assert
      "empty input is quiet"
      (replyPosts "kimi" [] [] "x" == [])

    putStrLn "echoShard (exact mock oracle)"
    sh <- echoShard "kimi"
    r1 <- runShardIO sh [p1, p2]
    assert
      "echo reply body is the session prompt"
      (map body r1 == [sessionPrompt [p1, p2]]
         && all ((== "kimi") . from) r1
         && all ((== ["grok", "tony"]) . to) r1)
    r2 <- runShardIO sh [p1]
    assert
      "outbox drains between closes"
      (map body r2 == ["hello"]
         && all ((== "kimi") . from) r2
         && all ((== ["tony"]) . to) r2)
    r3 <- runShardIO sh []
    assert "empty commit emits nothing" (null r3)

    putStrLn "thread (ancestry) oracles"
    assert "root post has no parents" (thread p1 == [])
    assert
      "reply threads onto the parent id"
      (thread (replyTo "kimi" 1 p2 "x" :: Post Text) == [1])
    assert
      "replyPosts threads onto the last input's id"
      (case replyPosts "kimi" [p1, p2] [0, 1] "sure" of
         [rp] -> thread rp == [1]
         _ -> False)
    let r1' :: Post Text
        r1' = replyTo "kimi" 1 p2 "a"
        r2' :: Post Text
        r2' = replyTo "tony" 2 r1' "b"
    assert
      "branches of a root are its sender"
      (branchesByIndex [p1, p2] p2 == [["grok"]])
    assert
      "branches of a reply are pure cons"
      (branchesByIndex [p1, p2] r1' == map ("kimi" :) (branchesByIndex [p1, p2] p2))
    assert
      "branches unfolds a three-post thread"
      (branchesByIndex [p1, p2, r1'] r2' == [["tony", "kimi", "grok"]])
    let r0 :: Post Text
        r0 = replyTo "kimi" 0 p1 "old"
    assert
      "same-named posts are disambiguated by exact id"
      (branchesByIndex [p1, p2, r1', r0] r2' == [["tony", "kimi", "grok"]])

    putStrLn "synthesis (wire-merge) oracles"
    let syn :: Post Text
        syn = synthesis "sum" ["human"] [1, 0] "Σ"
    assert
      "synthesis ancestry is a normalised set of parent ids"
      (thread syn == [0, 1])
    assert
      "synthesis ancestry discards duplicate ids"
      (thread (synthesis "sum" [] [0, 0] "Σ" :: Post Text) == [0])
    assert
      "branches of a synthesis has one path per parent"
      (branchesByIndex [p1, p2] syn == [["sum", "tony"], ["sum", "grok"]])
    assert
      "branches of a synthesis continues through each parent"
      (branchesByIndex [p1, p2, r1'] (synthesis "sum" [] [2, 0] "Σ" :: Post Text)
         == [["sum", "tony"], ["sum", "kimi", "grok"]])

    putStrLn "honest provenance oracles"
    let syn2 = case synthesisPosts "sum" [p2, p1, r1'] [1, 0, 2] "Σ2" of
          [s] -> s
          _ -> error "synthesisPosts: expected one post"
        prior = [p2, p1, r1']
    assert
      "synthesisPosts ancestry cites every input id"
      (thread syn2 == [0, 1, 2])
    assert
      "synthesisPosts audience is senders and wires, minus self"
      (to syn2 == ["grok", "kimi", "tony"])
    assert "synthesisPosts is quiet on empty reply" $
      null (synthesisPosts "sum" [p1] [0] "  ")
    assert "synthesisPosts is quiet on no inputs" $
      null (synthesisPosts "sum" [] [] "x")
    assert
      "ancestry monotonicity: every parent id is a valid prior index"
      (all (< fromIntegral (length prior)) (thread syn2))
    assert
      "cone-union law: cone of a synthesis is the union of parent cones"
      (coneByIndex prior (synthesis "sum" [] [2, 0] "Σ")
         == sortNub ("sum" : concatMap (coneByIndex prior) [r1', p2]))
    assert
      "cone of a synthesis is the contributor set"
      (coneByIndex prior (synthesis "sum" [] [2, 0] "Σ") == ["grok", "kimi", "sum", "tony"])

    putStrLn "cursor numbered poll oracles"
    tmpC <- getTemporaryDirectory
    let logf = tmpC </> "circuits-agent-cursor-axioma.log"
    wipe logf
    TIO.writeFile logf "a\nb\n"
    cur <- newMem 0
    r4 <- pollNumberedFile cur logf
    assert "complete lines are numbered 1-based" (r4 == [(1, "a"), (2, "b")])
    r5 <- pollNumberedFile cur logf
    assert "frozen log polls empty" (null r5)
    TIO.appendFile logf "c"
    r6 <- pollNumberedFile cur logf
    assert "partial trailing line is left unconsumed" (null r6)
    TIO.appendFile logf "\n"
    r7 <- pollNumberedFile cur logf
    assert "completed line is delivered exactly once, with its number" (r7 == [(3, "c")])
    TIO.writeFile logf "x\n"
    r8 <- pollNumberedFile cur logf
    assert "truncation resets to zero" (r8 == [(1, "x")])

  putStrLn "All tests passed"
  where
    -- \| Generic behaviour for Tier A agents (output lists are concatenated).
    behA :: Agent (->) s a [b] -> s -> [a] -> [b]
    behA _sys _s0 [] = []
    behA sys s0 (i : ins) =
      let (os, s') = run1 sys s0 i
       in os ++ behA sys s' ins

    -- \| Tool call as data: from = caller, to = [tool], body = args.
    toolCall :: Text -> Text -> Text -> Post Text
    toolCall from tool = mkPost from [tool]

    -- \| Agent policy: on a "please sum …" human, emit a calc tool call.
    callCalc :: [Post Text] -> [Post Text]
    callCalc hist =
      let p = peek hist
          args =
            if "please sum " `T.isPrefixOf` body p
              then T.drop (T.length "please sum ") (body p)
              else body p
       in [toolCall "j" "calc" args]

    llmJ :: [Post Text] -> [Post Text]
    llmJ hist =
      let p = peek hist
       in [ if "calc:" `T.isPrefixOf` body p
              then mkPost "j" ["calc"] (T.drop 5 (body p))
              else
                mkPost
                  "j"
                  [from (peek (dropWhile ((== "calc") . from) hist))]
                  ("final: " <> body p)
          ]

    calc :: [Post Text] -> [Post Text]
    calc hist =
      let p = peek hist
       in [ mkPost
              "calc"
              [from p]
              (T.pack (show (sum [read (T.unpack w) :: Int | w <- T.words (body p)])))
          ]

    -- \| Self-loop policy: echo card posts back to the same card; after k
    -- rounds emit the halt mark; silence once the mark is on the card.
    selfLoopPolicy :: Text -> Int -> [Post Text] -> [Post Text]
    selfLoopPolicy name k hist =
      let p = peek hist
       in if markOf p == Just Landed
            then []
            else
              if length hist > k
                then [mkPost name ["xyzzy"] "🟢 landed"]
                else [mkPost name ["xyzzy"] ("echo: " <> body p)]

    -- \| Neutral card policy: answer human posts once with a halt-marked
    -- echo back to the card; silence on anything else (including the marks).
    cardEcho :: Text -> [Post Text] -> [Post Text]
    cardEcho name hist =
      let p = peek hist
       in if from p == "human"
            then [mkPost name ["xyzzy"] ("🟢 echo: " <> body p)]
            else []
