{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}
-- | addressed-log delivery laws: semiring/FinRel matrices, Chu spaces, S0b/G1.
module Axioma.Delivery
  ( deliveryTopic,
  )
where

import Axioma.Common
import Algebra.Graph.Labelled qualified as LG
import Circuit.Agent
import Circuit.Agent.Delivery
import Circuit.Machine (Body (Body), Moore, MooreT (..), Poles (..), Step (..))
import Circuit.Mat.Dense (Matrix, fromLists, matPlus, starMatrix, toLists)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T

default (Text)


deliveryTopic :: IO ()
deliveryTopic = do
  putStrLn "Tier B: addressed-log laws"

  putStrLn "reply stream laws"
  do
    let p1 = mkPost "human" ["j"] "one"
        p2 = mkPost "human" ["j"] "two"
        p3 = mkPost "human" ["j"] "three"
        ins = [p1, p2, p3]
        f = reply "j"
        h = take 1
        sys1 :: Moore (,) [Post Text] (->) (Post Text) [Post Text]
        sys1 = tape f
        sys2 :: Moore (,) [Post Text] (->) (Post Text) [Post Text]
        sys2 = tape (f . h)
    assert "reply homomorphism: summarizer h preserves behaviour" $
      beh (cellToAgent sys2) (h []) ins == beh (cellToAgent sys1) [] ins

  do
    let p1 = mkPost "human" ["j"] "one"
        p2 = mkPost "human" ["j"] "two"
        p3 = mkPost "human" ["j"] "three"
        xs = [p1, p2]
        ys = [p3]
        agent :: Moore (,) [Post Text] (->) (Post Text) [Post Text]
        agent = tape (reply "j")
        s0 = [] :: [Post Text]
    assert "reply functoriality: beh s0 (xs ++ ys) == beh s0 xs ++ beh (finalAgent agent s0 xs) ys" $
      beh (cellToAgent agent) s0 (xs ++ ys)
        == beh (cellToAgent agent) s0 xs ++ beh (cellToAgent agent) (finalAgent agent s0 xs) ys

  putStrLn "delivery"
  do
    let t0 =
          [ mkPost "human" ["k"] "hi k",
            mkPost "human" ["j"] "hi j"
          ]
    let (stJ1, t1, _) = turn (cellToAgent (tape (reply "j"))) (seedState ["j"] t0) t0
    let (stK1, t2, _) = turn (cellToAgent (tape (reply "k"))) (seedState ["k"] t1) t1
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
    let (stJ2, _t4, _) = turn (cellToAgent (tape (reply "j"))) (feedState (newFor ["j"] t3 stJ1) stJ1) t3
    assert "j sees the new post, no redelivery" $
      map body (reverse (asCarrier stJ2)) == ["hi j", "again"]

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

  putStrLn "bus Chu space"
  do
    let prefix :: Text
        prefix = "ch-"
        prefixTo :: [Text] -> [Text]
        prefixTo = map (\x -> if x == "all" || x == "" then x else T.append prefix x)
        unprefixSub :: [Text] -> [Text]
        unprefixSub =
          map
            ( \x ->
                if x == "all" || x == ""
                  then x
                  else fromMaybe x (T.stripPrefix prefix x)
            )
        lawfulFwd :: Post Text -> Post Text
        lawfulFwd p = p {to = prefixTo (to p)}
        lawfulBwd :: [Text] -> [Text]
        lawfulBwd = unprefixSub
        chuLaw fwd bwd p s =
          deliversTo (fwd p) s == deliversTo p (bwd s)
        roster = ["j", "k"] :: [Text]
        posts =
          [ mkPost "a" [r] "b"
          | r <- roster
          ]
            ++ [mkPost "a" ["j", "k"] "b"]
            ++ [mkPost "a" ["all"] "b"]
            ++ [mkPost "a" [] "b"]
        -- Subscriber sets live in the codomain (prefixed names).
        subs =
          map ((: []) . T.append prefix) roster
            ++ [map (T.append prefix) roster]
            ++ [["all"], [""]]
    assert "lawful prefix pair satisfies Chu adjoint law" $
      all (\p -> all (chuLaw lawfulFwd lawfulBwd p) subs) posts

  do
    let prefix :: Text
        prefix = "ch-"
        prefixTo = map (\x -> if x == "all" || x == "" then x else T.append prefix x)
        lawfulFwd p = p {to = prefixTo (to p)}
        unlawfulBwd :: [Text] -> [Text]
        unlawfulBwd = id
        chuLaw fwd bwd p s =
          deliversTo (fwd p) s == deliversTo p (bwd s)
        counterPost = mkPost "a" ["j"] "b"
        counterSub = [T.append prefix "j"]
    assert "unlawful pair violates Chu adjoint law" $
      not (chuLaw lawfulFwd unlawfulBwd counterPost counterSub)

  putStrLn "semiring Chu lift"
  do
    let prefix :: Text
        prefix = "ch-"
        prefixTo = map (\x -> if x == "all" || x == "" then x else T.append prefix x)
        domainAgents = ["j", "k"] :: [Text]
        codomainAgents = map (T.append prefix) domainAgents
        posts =
          [ mkPost "a" ["j"] "b",
            mkPost "a" ["j", "k"] "b",
            mkPost "a" ["k"] "b",
            mkPost "a" ["all"] "b",
            mkPost "a" [] "b"
          ]
        domainMat =
          deliveryMatrix domainAgents (map to posts) :: Matrix Bool
        codomainMat =
          deliveryMatrix codomainAgents (map (prefixTo . to) posts) :: Matrix Bool
    assert "delivery matrix commutes with prefix morphism (Bool)" $
      toLists domainMat == toLists codomainMat

  do
    let prefix :: Text
        prefix = "ch-"
        prefixTo = map (\x -> if x == "all" || x == "" then x else T.append prefix x)
        domainAgents = ["j", "k"] :: [Text]
        codomainAgents = map (T.append prefix) domainAgents
        posts =
          [ mkPost "a" ["j", "k"] "b",
            mkPost "a" ["all"] "b"
          ]
        domainMat =
          deliveryMatrix domainAgents (map to posts) :: Matrix Double
        codomainMat =
          deliveryMatrix codomainAgents (map (prefixTo . to) posts) :: Matrix Double
    assert "delivery matrix commutes with prefix morphism (Double)" $
      toLists domainMat == toLists codomainMat

  do
    let prefix :: Text
        prefix = "ch-"
        prefixTo = map (\x -> if x == "all" || x == "" then x else T.append prefix x)
        domainAgents = ["j", "k"] :: [Text]
        posts = [mkPost "a" ["j"] "b"]
        domainMat =
          deliveryMatrix domainAgents (map to posts) :: Matrix Bool
        forwardOnlyMat =
          deliveryMatrix domainAgents (map (prefixTo . to) posts) :: Matrix Bool
    assert "prefix without backward column rename breaks matrix equality" $
      toLists domainMat /= toLists forwardOnlyMat

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
        weights = [0.5, -0.3] :: [Double]
        eps = 1e-5
        analytic = grad weights
        fd k =
          let wsPlus = take k weights ++ [weights !! k + eps] ++ drop (k + 1) weights
              wsMinus = take k weights ++ [weights !! k - eps] ++ drop (k + 1) weights
           in (loss wsPlus - loss wsMinus) / (2 * eps)
        fds = map fd [0 .. length weights - 1]
    assert "S0b soft-routing gradient matches finite difference" $
      all (\(a, f) -> abs (a - f) < 1e-8) (zip analytic fds)

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

-- 1792568198N
-- 1792568203N
-- 1792568338N
