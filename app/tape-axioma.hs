{-# LANGUAGE OverloadedStrings #-}
-- Tape indexing is by construction (parents precede children, one node per
-- post); partial-list head/(!!) are total on that construction.
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | The pin: an agent meeting log perceived as a Wengert tape (reverse-mode
-- AD tape).  One numeric meeting, one tape, one reverse sweep, four oracles.
-- Not a differentiation library — a proof that the perception works.
--
-- Design card: coffee/loom/tape.md ("axioma ⟜ one pin, not a program").
module Main (main) where

import Circuit.Agent
import Circuit.Diff (Diff, Diff' (..), runDiff)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.List (find, foldl')
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

-- | Approximate equality, scaled to the magnitude of the arguments.
approx :: Double -> Double -> Double -> Bool
approx tol a b = abs (a - b) < tol * (1 + abs a + abs b)

-------------------------------------------------------------------------
-- The numeric meeting
--
-- Every agent body function is 'Num'-polymorphic: instantiate at 'Double'
-- for the forward meeting, at 'Diff' for the local partials.  Same code,
-- two carriers.
-------------------------------------------------------------------------

-- | j's step: affine.
fj :: (Num a) => a -> a
fj v = 2 * v + 1

-- | k's step: quadratic, so the local partial depends on the input point.
fk :: (Num a) => a -> a
fk v = v * v + 3

-- | m's merge: weighted sum.  With sorted parent ids the arguments arrive
-- in the order @[seed-b-parent, k-parent]@, so the seed-b weight is 2 and
-- the k weight is 3.
fm :: (Num a) => a -> a -> a
fm xh xk = 2 * xh + 3 * xk

-- | j answers everything it receives, forwarding to k.  Parent ids are the
-- deterministic positions of the received post in the oldest-first log.
jAgent :: Agent (->) [Post Double] (Post Double) [Post Double]
jAgent = tape $ \hist ->
  let p = head hist
      parentId = case length hist of
        1 -> 0 -- seed-a
        2 -> 4 -- first k reply
        3 -> 6 -- second k reply
        _ -> error "jAgent: unexpected input"
   in [Post {from = "j", to = ["k"], thread = [parentId], body = fj (body p)}]

-- | k chains back to j on its first percept, forwards to m on its second.
kAgent :: Agent (->) [Post Double] (Post Double) [Post Double]
kAgent = tape $ \hist ->
  let p = head hist
      dest = if length hist == 1 then ["j"] else ["m"]
      parentId = case length hist of
        1 -> 3 -- first j reply
        2 -> 5 -- second j reply
        _ -> error "kAgent: unexpected input"
   in [Post {from = "k", to = dest, thread = [parentId], body = fk (body p)}]

-- | m stays silent until it has seen both parents, then synthesises.
-- The seed-b seed has id 1 and the final k reply has id 6.
mAgent :: Agent (->) [Post Double] (Post Double) [Post Double]
mAgent = tape $ \hist ->
  case (find ((== "k") . from) hist, find ((== "seed-b") . from) hist) of
    (Just kp, Just hp) -> [synthesis "m" [] [1, 6] (fm (body hp) (body kp))]
    _ -> []

-- | The seed values: one per distinct root sender.
x0Seed, y0Seed, noiseVal :: Double
x0Seed = 0.7
y0Seed = 1.3
noiseVal = 42.0

-- | Run the meeting to quiescence; return the log oldest first.
--
-- The root senders are distinct names ('seed-a', 'seed-b', 'noise') because
-- thread edges resolve by name to the most recent prior post — shared sender
-- names would make the name-resolution ambiguous against the numeric inputs.
meetingLog :: [Post Double]
meetingLog = reverse finalLog
  where
    seedLog :: [Post Double]
    seedLog =
      foldl'
        (flip post)
        (emptyLog @Double)
        [ mkPost "seed-a" ["j"] x0Seed,
          mkPost "seed-b" ["m"] y0Seed,
          mkPost "noise" ["nobody"] noiseVal
        ]
    (_, finalLog, _) = loop roster seedLog
    roster = [("j", jAgent), ("k", kAgent), ("m", mAgent)]

-------------------------------------------------------------------------
-- The tape: one Wengert node per post.
-------------------------------------------------------------------------

-- | A Wengert node: id, value, parent ids, and the local partials
-- @∂(this node)\/∂(parent i)@ evaluated at the node's inputs.
data Node = Node
  { nId :: Int,
    nFrom :: Name,
    nValue :: Double,
    nParents :: [Int],
    nPartials :: [Double]
  }

-- | Perceive a log as a Wengert tape.  Thread edges are exact parent
-- indices, so parent lookup is a direct index into the oldest-first log.
buildTape :: [Post Double] -> [Node]
buildTape ps = buildTapeWithIds ps [0 .. fromIntegral (length ps - 1)]

-- | General tape builder: posts may be in any topological order, and the
-- supplied id list gives each post's own 'PostId' (so position no longer
-- equals identity).  This is the heart of the linearization-invariance
-- oracle: the reverse sweep depends only on the DAG, not on the file order.
buildTapeWithIds :: [Post Double] -> [PostId] -> [Node]
buildTapeWithIds ps ids = zipWith node ids ps
  where
    valueById :: IntMap Double
    valueById = IntMap.fromList (zip (map fromIntegral ids) (map body ps))
    node i p =
      let parIs = map fromIntegral (thread p)
          parVs = map (valueById IntMap.!) parIs
          i' = fromIntegral i
       in Node i' (from p) (body p) parIs (partials (from p) parVs)

-- | Local partials, one per parent, from 'runDiff' on the agent's own
-- 'Num'-polymorphic body function at the node's inputs.
partials :: Name -> [Double] -> [Double]
partials name parVs = case name of
  "j" -> [unary fj (head parVs)]
  "k" -> [unary fk (head parVs)]
  "m" ->
    let V2 dk dh = snd (runDiff fmDiff (V2 (head parVs) (parVs !! 1))) 1.0
     in [dk, dh]
  _ -> [] -- root posts: no parents, no partials

-- | Pullback of a unary body function at a point, seeded with 1.
unary :: (Diff Double Double -> Diff Double Double) -> Double -> Double
unary f x = snd (runDiff (f (Diff' (\s -> (s, id)))) x) 1.0

-- | A two-slot input vector, so a two-parent merge can be a 'Diff' input.
data V2 = V2 Double Double

instance Num V2 where
  V2 a b + V2 c d = V2 (a + c) (b + d)
  V2 a b - V2 c d = V2 (a - c) (b - d)
  V2 a b * V2 c d = V2 (a * c) (b * d)
  negate (V2 a b) = V2 (negate a) (negate b)
  abs (V2 a b) = V2 (abs a) (abs b)
  signum (V2 a b) = V2 (signum a) (signum b)
  fromInteger n = V2 (fromInteger n) (fromInteger n)

-- | The merge as a differentiable arrow, parents in thread order.
fmDiff :: Diff V2 Double
fmDiff = fm (Diff' (\(V2 xk _) -> (xk, \db -> V2 db 0))) (Diff' (\(V2 _ xh) -> (xh, \db -> V2 0 db)))

-------------------------------------------------------------------------
-- The reverse sweep and the forward re-run.
-------------------------------------------------------------------------

-- | The reverse sweep: cotangent 1 at the final post, pushed backward
-- through the transpose of the parent index.  The node list must be in a
-- topological order (parents before children); the result is keyed by 'nId'.
sweep :: [Node] -> IntMap Double
sweep nodes = foldl' step cot0 (reverse nodes)
  where
    finalId = nId (last nodes)
    cot0 = IntMap.fromList [(nId n, if nId n == finalId then 1.0 else 0.0) | n <- nodes]
    step cot n =
      let c = cot IntMap.! nId n
       in foldl' (\c' (p, d) -> IntMap.insertWith (+) p (c * d) c') cot (zip (nParents n) (nPartials n))

-- | Re-run the forward meeting from node @i@ with its value perturbed: node
-- @i@ and its ancestors stay fixed, descendants recompute from the tape.
-- The tape is executable — that is the finite-difference oracle's premise.
fwdFrom :: [Node] -> [Double] -> Int -> Double -> Double
fwdFrom nodes vals i x = last (foldl' recom base [i + 1 .. n - 1])
  where
    n = length nodes
    base = take i vals ++ [x] ++ drop (i + 1) vals
    recom vs j =
      let nd = nodes !! j
       in if null (nParents nd)
            then vs
            else take j vs ++ [apply (nFrom nd) (map (vs !!) (nParents nd))] ++ drop (j + 1) vs

-- | The agent body functions at 'Double', parents in thread order.
apply :: Name -> [Double] -> Double
apply name parVs = case name of
  "j" -> fj (head parVs)
  "k" -> fk (head parVs)
  "m" -> fm (head parVs) (parVs !! 1) -- [seed-b, k]
  _ -> head parVs

main :: IO ()
main = do
  putStrLn "circuits-agent tape axioma: a meeting log perceived as a Wengert tape"

  -------------------------------------------------------------------------
  -- the meeting
  -------------------------------------------------------------------------
  putStrLn "the meeting"
  let ps = meetingLog
  assert "log shape: two seeds, a noise post, a j-k chain, a merge" $
    map from ps == ["seed-a", "seed-b", "noise", "j", "k", "j", "k", "m"]
  assert "the meeting as a function of the seeds" $
    approx 1e-12 (body (last ps)) (fm y0Seed (fk (fj (fk (fj x0Seed)))))

  -------------------------------------------------------------------------
  -- the tape
  -------------------------------------------------------------------------
  putStrLn "the tape"
  let nodes = buildTape ps
      vals = map nValue nodes
  mapM_
    ( \(i, nd) ->
        putStrLn
          ( "  node "
              ++ show i
              ++ ": from="
              ++ show (nFrom nd)
              ++ " value="
              ++ show (nValue nd)
              ++ " parents="
              ++ show (nParents nd)
              ++ " partials="
              ++ show (nPartials nd)
          )
    )
    (zip [0 :: Int ..] nodes)
  assert "thread edges are exact parent indices into the oldest-first log" $
    map nParents nodes == [[], [], [], [0], [3], [4], [5], [1, 6]]
  assert "local partials via runDiff: affine j" $
    nPartials (nodes !! 3) == [2.0]
  assert "local partials via runDiff: quadratic k at its input" $
    nPartials (nodes !! 4) == [2 * nValue (nodes !! 3)]
  assert "local partials via runDiff: merge weights in thread order" $
    nPartials (nodes !! 7) == [2.0, 3.0]

  -------------------------------------------------------------------------
  -- the reverse sweep
  -------------------------------------------------------------------------
  putStrLn "the reverse sweep"
  let cot = sweep nodes
  mapM_ (\(i, c) -> putStrLn ("  cotangent " ++ show i ++ ": " ++ show c)) (IntMap.toAscList cot)

  -------------------------------------------------------------------------
  -- O1: finite differences
  -------------------------------------------------------------------------
  putStrLn "O1: finite differences"
  let h = 1e-5
      fd i = (fwdFrom nodes vals i (vals !! i + h) - fwdFrom nodes vals i (vals !! i - h)) / (2 * h)
  mapM_
    ( \i ->
        assert ("O1: cotangent at node " ++ show i ++ " matches central difference") $
          approx 1e-6 (cot IntMap.! i) (fd i)
    )
    [0 .. length nodes - 1]

  -------------------------------------------------------------------------
  -- O2: chain rule sanity on the pure chain portion (nodes 3-4-5-6-7)
  -------------------------------------------------------------------------
  putStrLn "O2: chain rule"
  let chainPartials =
        [ head (nPartials (nodes !! 3)),
          head (nPartials (nodes !! 4)),
          head (nPartials (nodes !! 5)),
          head (nPartials (nodes !! 6)),
          nPartials (nodes !! 7) !! 1
        ]
  assert "O2: cotangent at the seed is the product of local derivatives along the chain" $
    approx 1e-10 (cot IntMap.! 0) (product chainPartials)

  -------------------------------------------------------------------------
  -- O3: merge splits (node 7 merges nodes 6 and 1)
  -------------------------------------------------------------------------
  putStrLn "O3: merge splits"
  let wh = head (nPartials (nodes !! 7))
      wk = nPartials (nodes !! 7) !! 1
  assert "O3: cotangent to the k parent is the merge weight times the child cotangent" $
    approx 1e-10 (cot IntMap.! 6) (wk * (cot IntMap.! 7))
  assert "O3: cotangent to the seed-b parent is the merge weight times the child cotangent" $
    approx 1e-10 (cot IntMap.! 1) (wh * (cot IntMap.! 7))

  -------------------------------------------------------------------------
  -- O4: zero-gradient certificate (node 2 is off the final post's cone)
  -------------------------------------------------------------------------
  putStrLn "O4: zero-gradient certificate"
  assert "O4: the noise post is off the final post's ancestry cone" $
    "noise" `notElem` coneByIndex (init ps) (last ps)
  assert "O4: the noise post has exactly zero cotangent" $
    cot IntMap.! 2 == 0.0

  -------------------------------------------------------------------------
  -- O5: linearization invariance — the sweep is independent of file order.
  -- Any topological serialization of the same DAG must yield identical
  -- cotangents at every PostId.  This is the async / schedule-invariance
  -- oracle made executable.
  -------------------------------------------------------------------------
  putStrLn "O5: linearization invariance"
  let orderB = [1, 0, 2, 3, 4, 5, 6, 7] :: [PostId]
      postsB = map (ps !!) (map fromIntegral orderB)
      nodesB = buildTapeWithIds postsB orderB
      cotB = sweep nodesB
      allIds :: [PostId]
      allIds = map fromIntegral [0 .. length ps - 1]
  assert "O5: every PostId has the same cotangent under both linearizations" $
    all (\i -> approx 1e-10 (cot IntMap.! fromIntegral i) (cotB IntMap.! fromIntegral i)) allIds
