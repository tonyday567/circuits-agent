{-# LANGUAGE OverloadedStrings #-}

-- | Conch custody over addressed posts.
--
-- A named channel has at most one holder.  The holder reserves a set of whole
-- files.  'Claim' requests custody; 'Handover' is the only post that changes
-- it.  System Handovers are proposed for available unowned Claims and for
-- configured strat Claims.  Replaying the binding Handovers reconstructs the
-- same custody without proposing more posts.
module Circuit.Agent.Conch
  ( Conch (..),
    ConchPayload,
    ConchPost,
    ConchConfig (..),
    Custody (..),
    ConchState (..),
    emptyConchState,
    custodyAt,
    reservationsAt,
    reservedFiles,
    stepConch,
    reconstructConch,
  )
where

import Circuit.Agent (Name, Post (..), PostId)
import Circuit.Agent.Framing (PostBody (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import "circuits-parser" Circuit.Parser.Json (Json (..))
import Prelude

-- | The coded Conch operation.  The text beside it is ordinary agent speech.
data Conch
  = Claim [FilePath]
  | Handover
  deriving (Eq, Ord, Show)

-- | JSON body framing for the coded operation.
instance PostBody Conch where
  encodePostBody (Claim paths) = JObject [("claim", JArray (V.fromList (map (JString . T.pack) paths)))]
  encodePostBody Handover = JObject [("handover", JNull)]
  decodePostBody (JObject [("claim", JArray vs)]) = Claim <$> traverse decodePath (V.toList vs)
    where
      decodePath (JString path) = Just (T.unpack path)
      decodePath _ = Nothing
  decodePostBody (JObject [("handover", JNull)]) = Just Handover
  decodePostBody _ = Nothing

-- | Optional coded operation at the Conch boundary.  The wire shape remains
-- null for ordinary conversation and the untagged Conch JSON otherwise.
instance PostBody (Maybe Conch) where
  encodePostBody Nothing = JNull
  encodePostBody (Just operation) = encodePostBody operation
  decodePostBody JNull = Just Nothing
  decodePostBody json = Just <$> decodePostBody json

-- | Conch payload at the existing polymorphic 'Post' boundary.
type ConchPayload = (Maybe Conch, Text)

-- | A post carrying ordinary conversation or one Conch operation.
type ConchPost = Post ConchPayload

-- | Runtime capabilities and identities.  No public seat name is built in.
data ConchConfig = ConchConfig
  { systemSeat :: Name,
    stratSeats :: Set Name,
    recipientSeats :: Set Name
  }
  deriving (Eq, Show)

-- | Current responsibility for one channel and its whole-file reservations.
data Custody = Custody
  { holder :: Name,
    reservations :: Set FilePath
  }
  deriving (Eq, Ord, Show)

-- | Custody indexed by Conch channel.  The unassigned pool is absence here.
newtype ConchState = ConchState
  { custody :: Map Name Custody
  }
  deriving (Eq, Show)

-- | No channel holders and no file reservations.
emptyConchState :: ConchState
emptyConchState = ConchState Map.empty

-- | Current holder and reservations for one channel.
custodyAt :: Name -> ConchState -> Maybe Custody
custodyAt c = Map.lookup c . custody

-- | Files reserved by one channel.  An unowned channel reserves nothing.
reservationsAt :: Name -> ConchState -> Set FilePath
reservationsAt c = maybe Set.empty reservations . custodyAt c

-- | Every currently reserved file.  A file occurs in at most one channel's
-- custody after each binding transition.
reservedFiles :: ConchState -> Set FilePath
reservedFiles = Set.unions . fmap reservations . Map.elems . custody

-- | Process one newly stamped post.
--
-- The state changes only for an authorised 'Handover'.  An eligible 'Claim'
-- returns a system Handover addressed to the claimant and threaded to that
-- Claim; the caller stamps and processes that Handover as a later post.  An
-- authorised Handover with a nonempty invalid nomination also returns one
-- unnominated system Handover threaded to its cause.  The lookup resolves
-- Claim parents already present in the log.
stepConch ::
  ConchConfig ->
  (PostId -> Maybe ConchPost) ->
  ConchState ->
  PostId ->
  ConchPost ->
  (ConchState, [ConchPost])
stepConch cfg lookupPost st pid p =
  case (channel p, fst (body p)) of
    (Just c, Just (Claim paths)) -> (st, claimResponse cfg st pid p c (Set.fromList paths))
    (Just c, Just Handover) -> settleHandover cfg lookupPost st pid p c
    _ -> (st, [])

-- | Reconstruct custody from a chronological stamped log.
--
-- Claims and ordinary posts are inert during reconstruction.  Only binding
-- Handovers are folded, so restart produces no system posts, repeated
-- transfers, or claimant wakes.
reconstructConch :: ConchConfig -> [(PostId, ConchPost)] -> ConchState
reconstructConch cfg posts = foldl' settle emptyConchState posts
  where
    byId = Map.fromList posts
    lookupPost = (`Map.lookup` byId)
    settle st (pid, p) =
      case (channel p, fst (body p)) of
        (Just c, Just Handover) -> fst (settleHandover cfg lookupPost st pid p c)
        _ -> st

claimResponse :: ConchConfig -> ConchState -> PostId -> ConchPost -> Name -> Set FilePath -> [ConchPost]
claimResponse cfg st pid p c requested =
  [ Post
      { from = systemSeat cfg,
        channel = Just c,
        to = [from p],
        thread = [pid],
        body = (Just Handover, "")
      }
  | canGrant && resourcesAvailable
  ]
  where
    current = Map.lookup c (custody st)
    forced = from p `Set.member` stratSeats cfg
    validRecipient = from p `Set.member` recipientSeats cfg
    canGrant = validRecipient && (forced || maybe True (const False) current)
    revocable = if forced then maybe Set.empty reservations current else Set.empty
    unavailable = reservedFiles st `Set.difference` revocable
    resourcesAvailable = Set.null (requested `Set.intersection` unavailable)

settleHandover :: ConchConfig -> (PostId -> Maybe ConchPost) -> ConchState -> PostId -> ConchPost -> Name -> (ConchState, [ConchPost])
settleHandover cfg lookupPost st pid p c
  | not authorised = (st, [])
  | otherwise = (ConchState next, fallback)
  where
    current = Map.lookup c (custody st)
    previousFiles = maybe Set.empty reservations current
    nomination =
      case to p of
        [r] | r `Set.member` recipientSeats cfg -> Just r
        _ -> Nothing
    linked = nomination >>= linkedClaim lookupPost pid p c
    claimedFiles = linked >>= claimPaths
    systemForce =
      from p == systemSeat cfg
        && isJust claimedFiles
        && maybe False ((`Set.member` stratSeats cfg) . from) linked
    authorised =
      case current of
        Just h -> from p == holder h || systemForce
        Nothing -> from p == systemSeat cfg && isJust claimedFiles
    nextFiles = fromMaybe previousFiles claimedFiles
    unavailable = reservedFiles st `Set.difference` previousFiles
    available = Set.null (nextFiles `Set.intersection` unavailable)
    next =
      case nomination of
        Just r | available -> Map.insert c (Custody r nextFiles) (custody st)
        _ -> Map.delete c (custody st)
    invalidNomination = case (to p, nomination) of
      (_ : _, Nothing) -> True
      _ -> False
    fallback =
      [ Post
          { from = systemSeat cfg,
            channel = Just c,
            to = [],
            thread = [pid],
            body = (Just Handover, "")
          }
      | invalidNomination
      ]

linkedClaim :: (PostId -> Maybe ConchPost) -> PostId -> ConchPost -> Name -> Name -> Maybe ConchPost
linkedClaim lookupPost pid p c recipient =
  case thread p of
    [parent]
      | parent < pid ->
          lookupPost parent >>= \q ->
            if channel q == Just c && from q == recipient then Just q else Nothing
    _ -> Nothing

claimPaths :: ConchPost -> Maybe (Set FilePath)
claimPaths q =
  case fst (body q) of
    Just (Claim paths) -> Just (Set.fromList paths)
    _ -> Nothing
