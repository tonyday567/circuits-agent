{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}
-- | Shared helpers for the circuits-agent axioma topic modules.
module Axioma.Common
  ( assert,
    iterateAgent,
    finalAgent,
    mkPost,
    peek,
    reply,
    diffLog,
    wipe,
    routeToInbox,
    feedState,
    seedState,
    newFor,
    runParallel,
    raceP,
    awaitP,
    silent,
    outcomesRace,
    constAgent,
    constAgentS,
    behA,
    toolCall,
    callCalc,
    llmJ,
    calc,
    selfLoopPolicy,
    cardEcho,
    constShard,
    tagShard,
  )
where

import Algebra.Graph.Labelled qualified as LG
import Circuit.Agent
import Circuit.Agent.Mark (Mark (..), markOf)
import Circuit.Agent.StdPorts
import Circuit.Agent.Tensor
import Circuit.Machine (Body (Body), Moore, MooreT (..), Poles (..), Step (..), scan)
import Control.Monad (when)
import Data.List (nub)
import Data.Text (Text)
import Data.Text qualified as T
import System.Directory (doesFileExist, removeFile)
import System.Exit (ExitCode (..), exitFailure)
import Prelude hiding (read)
import Prelude qualified

default (Text)

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

-- | The runner 'iterateAgent' once was: a body is already observable, so
-- this is 'scan' over a 'MooreT' at constant seed.
iterateAgent :: Moore (,) s (->) i o -> s -> [i] -> [o]
iterateAgent (Body _ k o) s0 = scan (MooreT (Body (\i -> k (s0, i)) k o))

-- | The final state of the run — 'foldProcess' without the observation.
finalAgent :: Moore (,) s (->) i o -> s -> [i] -> s
finalAgent (Body _ k _) s0 is = foldl' (\s i -> k (s, i)) s0 is

-- | Remove a file if present.
wipe :: FilePath -> IO ()
wipe f = do
  e <- doesFileExist f
  when e (removeFile f)

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
constAgent outs = cellToAgent (tape (const outs))

-- | STM agent that ignores its history and always emits the same list.
constAgentS :: [Post Text] -> AgentS [Post Text] (Post Text)
constAgentS outs = agentM (cellToAgent (tape (const outs)))

-- \| Generic behaviour for Tier A agents (output lists are concatenated).
behA :: Moore (,) s (->) a [b] -> s -> [a] -> [b]
behA _sys _s0 [] = []
behA sys s0 (i : ins) =
  let (os, s') = runCell sys s0 i
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
          (T.pack (show (sum [Prelude.read (T.unpack w) :: Int | w <- T.words (body p)])))
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
   in [mkPost name ["xyzzy"] ("🟢 echo: " <> body p) | from p == "human"]


-- Shared shard factories for the tensor topics (a main-do-level let in the
-- monolith, hoisted here so every topic sees them).
constShard :: [Post Text] -> AgentShard [Post Text] [Post Text]
constShard outs = ioShard (const (pure outs))

tagShard :: Text -> AgentShard [Post Text] [Post Text]
tagShard suffix = ioShard (pure . map addSuffix)
  where
    addSuffix x = x {body = body x <> suffix}
-- 1792568338N
