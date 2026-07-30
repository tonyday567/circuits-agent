-- | Semiring delivery matrices for addressed posts.
--
-- 'deliversTo' in 'Circuit.Agent' is the boolean predicate that gates delivery.
-- This module lifts the same logic to an arbitrary 'NumHask' semiring,
-- producing delivery and topology matrices that can be interpreted under
-- different semirings:
--
-- * Boolean: exactly today's discrete delivery (the regression fence, G2).
-- * Real / probability: weighted delivery for gradient-based routing.
-- * Path-counting: number of delivery paths (useful for G3).
--
-- A post delivers to a recipient when the recipient appears in the post's 'to'
-- list.  The 'from' field is treated as the sender when building agent-to-agent
-- topology matrices.
module Circuit.Agent.Delivery
  ( -- * Semiring predicate
    deliversToSemiring,

    -- * Matrices
    deliveryMatrix,
    topologyMatrix,

    -- * Nilpotency / acyclicity check
    isNilpotent,
    matrixPowers,
  )
where

import Data.Text (Text)
import Data.Vector.Unboxed qualified as VU
import Harpie.Array qualified as A
import Harpie.NumHask.Matrix (Matrix (..), fromLists, matTimes, toLists)
import NumHask.Algebra.Additive (Additive (..))
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import Prelude hiding ((*), (+))

-- | Semiring-generalised delivery predicate.
--
-- A post delivers with the semiring's 'one' when @who@ is in the recipient
-- list; otherwise it delivers with 'zero'.
deliversToSemiring ::
  (Additive r, Multiplicative r) =>
  -- | Recipients on the post.
  [Text] ->
  -- | Recipient name.
  Text ->
  r
deliversToSemiring recipients who
  | who `elem` recipients = one
  | otherwise = zero

-- | Delivery matrix for a fixed list of posts and a roster of agents.
--
-- Rows are posts (in the order given), columns are agents (in the order
-- given), and entry @(p, a)@ is the delivery weight of post @p@ to agent @a@.
deliveryMatrix ::
  (Additive r, Multiplicative r) =>
  -- | Agents (column labels).
  [Text] ->
  -- | Recipient lists for each post (row labels are implicit).
  [[Text]] ->
  Matrix r
deliveryMatrix agents recipients =
  fromLists [map (deliversToSemiring recips) agents | recips <- recipients]

-- | Agent-to-agent delivery topology matrix.
--
-- Rows and columns are agents.  Entry @(i, j)@ is the combined weight with
-- which agent @i@'s authored posts are delivered to agent @j@.  The
-- aggregation uses the semiring addition ('+'), so multiple posts from the
-- same sender to the same recipient accumulate.
--
-- Posts are given as @(author, recipients)@ pairs.
topologyMatrix ::
  (Additive r, Multiplicative r) =>
  -- | Agents (row and column labels, in the same order).
  [Text] ->
  -- | Posts as @(author, recipients)@ pairs.
  [(Text, [Text])] ->
  Matrix r
topologyMatrix agents posts =
  fromLists
    [ [ sum' [deliversToSemiring recipients who | (whoFrom, recipients) <- posts, whoFrom == fromAgent]
      | who <- agents
      ]
    | fromAgent <- agents
    ]
  where
    sum' [] = zero
    sum' (x : xs) = x + sum' xs

-- | Powers of a square matrix, starting from the first power.
matrixPowers ::
  (Additive r, Multiplicative r) =>
  Int ->
  Matrix r ->
  [Matrix r]
matrixPowers n m = take n (iterate (matTimes m) m)

-- | A square matrix is nilpotent when some power is the zero matrix.
--
-- For a delivery topology, nilpotency means the communication graph is a DAG:
-- no directed cycle can return a non-zero weight, so every sufficiently long
-- path multiplies out to zero.
isNilpotent ::
  (Additive r, Multiplicative r, Eq r) =>
  Matrix r ->
  Bool
isNilpotent m = any isZeroMatrix (matrixPowers (rows m) m)
  where
    rows (Matrix a) = case VU.toList (A.shape a) of
      (r : _) -> r
      _ -> 0
    isZeroMatrix = all (all (== zero)) . toLists
