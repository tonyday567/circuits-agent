{-# LANGUAGE OverloadedStrings #-}

-- | Exact pure witnesses for Conch custody.
module Axioma.Conch (conchTopic) where

import Axioma.Common (assert)
import Circuit.Agent (Name, Post (..), PostId)
import Circuit.Agent.Conch
import Circuit.Agent.Framing (PostBody (..), framePost, parsePost)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Prelude

conchTopic :: IO ()
conchTopic =
  putStrLn "Conch custody"
    >> ordinaryWitness
    >> claimWitness
    >> queryWitness
    >> refusalWitness
    >> raceWitness
    >> resourceWitness
    >> nominationWitness
    >> fallbackWitness
    >> theftWitness
    >> forceWitness
    >> renameWitness
    >> restartWitness
    >> channelWitness
    >> authorizationWitness
    >> framingWitness

cfg :: ConchConfig
cfg = ConchConfig "system" (Set.singleton "strat") (Set.fromList ["system", "a", "b", "c", "strat", "tact"])

claimPost :: Name -> Name -> [FilePath] -> ConchPost
claimPost f c paths = Post f (Just c) [] [] (Just (Claim paths), "")

handoverPost :: Name -> Name -> [Name] -> [PostId] -> ConchPost
handoverPost f c recipients parents = Post f (Just c) recipients parents (Just Handover, "")

ordinaryPost :: Name -> Maybe Name -> ConchPost
ordinaryPost f c = Post f c [] [] (Nothing, "[complete] [discover] [error] TASK READY")

ownedLog :: [(PostId, ConchPost)]
ownedLog = [(0, claimPost "a" "one" ["A.hs"]), (1, handoverPost "system" "one" ["a"] [0])]

ownedState :: ConchState
ownedState = reconstructConch cfg ownedLog

stepFixture :: ConchConfig -> [(PostId, ConchPost)] -> ConchState -> (PostId, ConchPost) -> (ConchState, [ConchPost])
stepFixture config posts st (pid, p) = stepConch config (`Map.lookup` Map.fromList posts) st pid p

ordinaryWitness :: IO ()
ordinaryWitness =
  assert "ordinary speech and schedule vocabulary reserve nothing; counterexample: text changes custody" (reconstructConch cfg posts == emptyConchState)
  where
    posts = [(0, ordinaryPost "a" (Just "one")), (1, ordinaryPost "b" Nothing), (2, ordinaryPost "c" (Just "two"))]

claimWitness :: IO ()
claimWitness =
  assert "Claim alone is inert; counterexample: request acquires before Handover" (before == emptyConchState)
    >> assert "available unowned Claim proposes exactly one system Handover; counterexample: missing or duplicate grant" (length responses == 1)
    >> assert "subsequent system Handover installs exactly one holder; counterexample: Claim or Handover grants twice" (after == ConchState (Map.singleton "one" (Custody "a" Set.empty)))
  where
    claim = (0, claimPost "a" "one" [])
    (before, responses) = stepFixture cfg [claim] emptyConchState claim
    after = reconstructConch cfg (claim : zip [1 ..] responses)

queryWitness :: IO ()
queryWitness =
  assert "per-channel custody projection exposes holder and reservations; counterexample: production state cannot identify the responsible seat" (custodyAt "one" ownedState == Just (Custody "a" (Set.singleton "A.hs")) && custodyAt "two" ownedState == Nothing)
    >> assert "channel and global reservation projections agree; counterexample: an unowned channel or foreign file appears reserved" (reservationsAt "one" ownedState == Set.singleton "A.hs" && reservationsAt "two" ownedState == Set.empty && reservedFiles ownedState == Set.singleton "A.hs")

refusalWitness :: IO ()
refusalWitness =
  assert "owned tact Claim is refused without an effect; counterexample: request queues or emits a grant" (after == ownedState && null responses)
    >> assert "refused Claim stays unacquired on replay; counterexample: restart wakes the loser" (reconstructConch cfg (ownedLog <> [refused]) == ownedState)
  where
    refused = (2, claimPost "b" "one" [])
    (after, responses) = stepFixture cfg (ownedLog <> [refused]) ownedState refused

raceWitness :: IO ()
raceWitness =
  assert "serial race has one winner and no loser grant; counterexample: both racing Claims acquire" (length firstResponses == 1 && null loserResponses && firstWinner == loserWinner)
    >> assert "Handover order selects the winner; counterexample: Claim arrival fixes custody" (holderA == "a" && holderB == "b")
  where
    claimA = (0, claimPost "a" "one" [])
    claimB = (1, claimPost "b" "one" [])
    posts = [claimA, claimB]
    (_, firstResponses) = stepFixture cfg posts emptyConchState claimA
    stateA = reconstructConch cfg (claimA : zip [2 ..] firstResponses)
    (_, loserResponses) = stepFixture cfg posts stateA claimB
    (_, responsesB) = stepFixture cfg posts emptyConchState claimB
    stateB = reconstructConch cfg (claimB : zip [2 ..] responsesB)
    holderA = maybe "" holder (Map.lookup "one" (custody stateA))
    holderB = maybe "" holder (Map.lookup "one" (custody stateB))
    firstWinner = holderA
    loserWinner = maybe "" holder (Map.lookup "one" (custody (reconstructConch cfg (posts <> zip [2 ..] firstResponses))))

resourceWitness :: IO ()
resourceWitness =
  assert "multi-file acquisition is all-or-nothing; counterexample: available subset is reserved" (afterConflict == ownedState && null conflictResponses)
    >> assert "available file set transfers with the conch; counterexample: reservations remain with the old holder" (reconstructConch cfg transferLog == expectedTransfer)
    >> assert "conflicting posted Handover releases without stealing; counterexample: another channel's file moves" (reconstructConch cfg conflictHandoverLog == expectedConflictRelease)
  where
    conflict = (2, claimPost "b" "two" ["C.hs", "A.hs"])
    (afterConflict, conflictResponses) = stepFixture cfg (ownedLog <> [conflict]) ownedState conflict
    transfer = (2, handoverPost "a" "one" ["b"] [])
    transferLog = ownedLog <> [transfer]
    expectedTransfer = ConchState (Map.singleton "one" (Custody "b" (Set.fromList ["A.hs"])))
    twoChannelLog = ownedLog <> [(2, claimPost "b" "two" ["B.hs"]), (3, handoverPost "system" "two" ["b"] [2])]
    conflictHandoverLog = twoChannelLog <> [(4, claimPost "c" "one" ["B.hs"]), (5, handoverPost "a" "one" ["c"] [4])]
    expectedConflictRelease = ConchState (Map.singleton "two" (Custody "b" (Set.singleton "B.hs")))

nominationWitness :: IO ()
nominationWitness =
  assert "invalid nomination releases the old holder; counterexample: failed delivery traps custody" (reconstructConch cfg (ownedLog <> [invalid]) == emptyConchState)
    >> assert "unnominated Handover abandons to the pool; counterexample: an outcome tag is required" (reconstructConch cfg (ownedLog <> [abandon]) == emptyConchState)
    >> assert "multiple nominations are invalid and release; counterexample: ambiguous recipients split custody" (reconstructConch cfg (ownedLog <> [multiple]) == emptyConchState)
  where
    invalid = (2, handoverPost "a" "one" ["missing"] [])
    abandon = (2, handoverPost "a" "one" [] [])
    multiple = (2, handoverPost "a" "one" ["b", "c"] [])

fallbackWitness :: IO ()
fallbackWitness =
  assert "authorised invalid nomination releases and emits one threaded system fallback; counterexample: missing, nominated, or unthreaded fallback" (afterInvalid == emptyConchState && isSystemFallback fallbacks)
    >> assert "fallback replay is final and silent; counterexample: replay repeats custody or emits another Handover" (reconstructConch cfg fallbackLog == emptyConchState && afterFallback == emptyConchState && null fallbackResponses)
    >> assert "unnominated abandonment and valid nomination need no fallback; counterexample: a valid release spawns a system post" (null abandonResponses && null validResponses)
    >> assert "unauthorised invalid nomination emits no fallback; counterexample: a third party causes a system transition" (afterTheft == ownedState && null theftResponses)
  where
    invalid = (2, handoverPost "a" "one" ["missing"] [])
    invalidLog = ownedLog <> [invalid]
    (afterInvalid, fallbacks) = stepFixture cfg invalidLog ownedState invalid
    isSystemFallback [h] = from h == "system" && channel h == Just "one" && null (to h) && thread h == [2] && fst (body h) == Just Handover
    isSystemFallback _ = False
    fallbackLog = invalidLog <> zip [3 ..] fallbacks
    (afterFallback, fallbackResponses) = case fallbacks of
      [h] -> stepFixture cfg fallbackLog afterInvalid (3, h)
      _ -> (afterInvalid, [])
    abandon = (2, handoverPost "a" "one" [] [])
    (_, abandonResponses) = stepFixture cfg (ownedLog <> [abandon]) ownedState abandon
    valid = (2, handoverPost "a" "one" ["b"] [])
    (_, validResponses) = stepFixture cfg (ownedLog <> [valid]) ownedState valid
    theft = (2, handoverPost "b" "one" ["missing"] [])
    (afterTheft, theftResponses) = stepFixture cfg (ownedLog <> [theft]) ownedState theft

theftWitness :: IO ()
theftWitness =
  assert "third-party Handover cannot steal custody; counterexample: sender authority is ignored" (reconstructConch cfg (ownedLog <> [theft]) == ownedState)
  where
    theft = (2, handoverPost "b" "one" ["b"] [])

forceWitness :: IO ()
forceWitness =
  assert "ordinary tact cannot force revocation; counterexample: tact Claim emits a system Handover" (null tactResponses && afterTact == ownedState)
    >> assert "configured strat force revokes through one binding Handover; counterexample: force mutates directly or needs consent" (length stratResponses == 1 && forcedState == expectedForce)
    >> assert "force does not steal another channel's reservations; counterexample: strat bypasses file atomicity" (null crossFileResponses)
  where
    tactClaim = (2, claimPost "tact" "one" [])
    (afterTact, tactResponses) = stepFixture cfg (ownedLog <> [tactClaim]) ownedState tactClaim
    stratClaim = (2, claimPost "strat" "one" ["A.hs", "C.hs"])
    (_, stratResponses) = stepFixture cfg (ownedLog <> [stratClaim]) ownedState stratClaim
    forcedState = reconstructConch cfg (ownedLog <> [stratClaim] <> zip [3 ..] stratResponses)
    expectedForce = ConchState (Map.singleton "one" (Custody "strat" (Set.fromList ["A.hs", "C.hs"])))
    crossFileClaim = (4, claimPost "strat" "one" ["B.hs"])
    crossFileResponses = snd (stepFixture cfg twoChannelLog twoChannelState crossFileClaim)
    twoChannelLog = ownedLog <> [(2, claimPost "b" "two" ["B.hs"]), (3, handoverPost "system" "two" ["b"] [2])]
    twoChannelState = reconstructConch cfg twoChannelLog

renameWitness :: IO ()
renameWitness =
  assert "seat rename with configured capabilities preserves behaviour; counterexample: a public name is hardcoded" (reconstructConch renamedCfg renamedLog == renamedState)
  where
    renamedCfg = ConchConfig "kernel" (Set.singleton "strategy") (Set.fromList ["kernel", "worker"])
    renamedLog = [(0, claimPost "worker" "one" ["A.hs"]), (1, handoverPost "kernel" "one" ["worker"] [0])]
    renamedState = ConchState (Map.singleton "one" (Custody "worker" (Set.singleton "A.hs")))

restartWitness :: IO ()
restartWitness =
  assert "restart reconstructs holder and reservations without loser acquisition; counterexample: replay repeats a transfer or wakes a Claim" (reconstructConch cfg history == expected && reconstructConch cfg history == reconstructConch cfg history)
  where
    history = ownedLog <> [(2, claimPost "b" "one" []), (3, handoverPost "a" "one" ["c"] []), (4, ordinaryPost "c" (Just "one"))]
    expected = ConchState (Map.singleton "one" (Custody "c" (Set.singleton "A.hs")))

channelWitness :: IO ()
channelWitness =
  assert "Conch without a channel is invalid and inert; counterexample: addressing alone creates custody" (afterClaim == emptyConchState && null responses && reconstructConch cfg [claim, handover] == emptyConchState)
  where
    claim = (0, Post "a" Nothing [] [] (Just (Claim ["A.hs"]), ""))
    handover = (1, Post "system" Nothing ["a"] [0] (Just Handover, ""))
    (afterClaim, responses) = stepFixture cfg [claim, handover] emptyConchState claim

authorizationWitness :: IO ()
authorizationWitness =
  assert "unknown claimant receives no system response; counterexample: an unconfigured seat causes a wake" (afterUnknown == emptyConchState && null unknownResponses)
    >> assert "bare system Handover cannot acquire an unowned conch; counterexample: system identity alone mints custody" (reconstructConch cfg [bareAcquisition] == emptyConchState)
    >> assert "owned system Handover requires a linked strat Claim; counterexample: bare or tact-linked system posts revoke" (reconstructConch cfg (ownedLog <> [bareForce]) == ownedState && reconstructConch cfg (ownedLog <> [tactClaim, tactForce]) == ownedState)
  where
    unknownClaim = (0, claimPost "unknown" "one" [])
    (afterUnknown, unknownResponses) = stepFixture cfg [unknownClaim] emptyConchState unknownClaim
    bareAcquisition = (0, handoverPost "system" "one" ["a"] [])
    bareForce = (2, handoverPost "system" "one" ["b"] [])
    tactClaim = (2, claimPost "tact" "one" [])
    tactForce = (3, handoverPost "system" "one" ["tact"] [2])

framingWitness :: IO ()
framingWitness =
  assert "Claim JSON round-trip preserves whole-file paths; counterexample: framing drops or reorders the operation" (decodePostBody (encodePostBody (Claim ["A.hs", "B.hs"])) == Just (Claim ["A.hs", "B.hs"]))
    >> assert "Conch payload JSON round-trip preserves speech and absence; counterexample: Maybe/pair framing changes custody meaning" (decodePostBody (encodePostBody payloadHandover) == Just payloadHandover && decodePostBody (encodePostBody payloadOrdinary) == Just payloadOrdinary)
    >> assert "bare post framing preserves channel and parent; counterexample: framePost drops routing or ancestry" (parsePost (framePost framedPost) == Just framedPost)
  where
    payloadHandover = (Just Handover, "ok") :: ConchPayload
    payloadOrdinary = (Nothing, "plain") :: ConchPayload
    framedPost = Post "a" (Just "one") ["b"] [7] payloadHandover
