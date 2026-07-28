{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Circuit.Agent
import Circuit.Stream (These (..), uncons)
import Circuit.Poly (Eval (..), Mono, System)
import Circuit.Poly.Process (iterateSystem)
import Control.Arrow (Kleisli (..), runKleisli)
import Control.Monad.State (State, get, gets, modify, put, runState)
import Data.Functor.Identity (Identity (..))
import Data.Text (Text)
import Data.Text qualified as T
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

reply :: Text -> [Post] -> Post
reply name hist =
  mkPost name (author (peek hist)) (channel (peek hist)) ("ack: " <> body (peek hist))

main :: IO ()
main = do
  putStrLn "circuits-agent oracle tests"

  -------------------------------------------------------------------------
  -- The pretense: carrier is invisible at the interface.
  -------------------------------------------------------------------------
  putStrLn "the pretense"
  do
    let sumAgent :: System Int (Mono Int Int)
        sumAgent s = EP (EK s, EE (+ s))
    assert "tape sum == [1,3,6]" $
      iterateSystem (tape sum) [] [1, 2, 3 :: Int] == [1, 3, 6]
    assert "sumAgent == [1,3,6]" $
      iterateSystem sumAgent 0 [1, 2, 3 :: Int] == [1, 3, 6]

  -------------------------------------------------------------------------
  -- Delivery: addressed posts, no redelivery.
  -------------------------------------------------------------------------
  putStrLn "delivery"
  do
    let t0 =
          [ mkPost "human" "k" "beta" "hi k",
            mkPost "human" "j" "alpha" "hi j"
          ]
    let (sj1, t1) = turn "j" (tape (reply "j")) ([], t0)
    let (sk1, t2) = turn "k" (tape (reply "k")) ([], t1)
    assert "j receives only its addressed posts" $
      map body (reverse sj1) == ["hi j"]
    assert "k receives only its addressed posts" $
      map body (reverse sk1) == ["hi k"]

    let t3 = post (mkPost "human" "j" "alpha" "again") t2
    let (sj2, _t4) = turn "j" (tape (reply "j")) (sj1, t3)
    assert "j sees the new post, no redelivery" $
      map body (reverse sj2) == ["hi j", "again"]

  -------------------------------------------------------------------------
  -- Compaction invariance: summary-insensitive folds survive it.
  -------------------------------------------------------------------------
  putStrLn "compaction invariance"
  do
    let a = tape sum :: System [Int] (Mono Int Int)
    let (_, s1) = run1 a [] 1
    let (_, s2) = run1 a s1 2
    let (o3, _) = run1 a [sum s2] 3
    assert "sum survives wholesale compaction" $ o3 == 6

    let b = tape length :: System [Int] (Mono Int Int)
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
    let (sj1, t1) = turn "j" (tape llmJ) ([], t0)
    let (_sc1, t2) = turn "calc" (tape calc) ([], t1)
    let (_sj2, t3) = turn "j" (tape llmJ) (sj1, t2)
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
    let (seens, t1) = loop roster t0
    assert "loop delivers both agents" $
      map body (reverse (maybe [] id (lookup "j" seens))) == ["hi j"]
        && map body (reverse (maybe [] id (lookup "k" seens))) == ["hi k"]
    assert "loop posts both acks" $
      length t1 == 4
    assert "loop reaches quiescence (no pending)" $
      all (\(n, s) -> not (hasPending n s t1)) seens

    let roster2 = [("j", tape llmJ), ("calc", tape calc)]
    let tCalc0 = [mkPost "human" "j" "alpha" "calc:1 2 3"]
    let (_seens2, tCalc) = loop roster2 tCalc0
    assert "loop runs tool-call chain to final" $
      body (peek tCalc) == "final: 6"
    assert "loop tool chain length" $
      length tCalc == 4

    let (_emptySeens, tEmpty) = loop roster []
    assert "loop on empty log is identity" $ null tEmpty

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
                mkPost "nudge" "worker" chan "tell me more."
            )
        worker :: Agent [Post]
        worker =
          tape
            ( \hist ->
                let p = peek hist
                 in mkPost "worker" "nudge" chan ("ack:" <> body p)
            )
        -- seed: human addresses worker
        t0 = [mkPost "human" "worker" chan "start"]
        step (sw, sn, lg) =
          let (sw', lg1) = turn "worker" worker (sw, lg)
              (sn', lg2) = turn "nudge" nudge (sn, lg1)
           in (sw', sn', lg2)
        (_, _, tF) = iterate step ([], [], t0) !! rounds
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

  putStrLn "All tests passed"
  where
    -- | Tool call as data: author = caller, addr = tool, body = args.
    toolCall :: Text -> Text -> Text -> Text -> Post
    toolCall from tool chan args = mkPost from tool chan args

    -- | Agent policy: on a "please sum …" human, emit a calc tool call.
    callCalc :: [Post] -> Post
    callCalc hist =
      let p = peek hist
          args =
            if "please sum " `T.isPrefixOf` body p
              then T.drop (T.length "please sum ") (body p)
              else body p
       in toolCall "j" "calc" (channel p) args

    llmJ :: [Post] -> Post
    llmJ hist =
      let p = peek hist
       in if "calc:" `T.isPrefixOf` body p
            then mkPost "j" "calc" (channel p) (T.drop 5 (body p))
            else
              mkPost
                "j"
                (author (peek (dropWhile ((== "calc") . author) hist)))
                (channel p)
                ("final: " <> body p)

    calc :: [Post] -> Post
    calc hist =
      let p = peek hist
       in mkPost
            "calc"
            (author p)
            (channel p)
            (T.pack (show (sum [read (T.unpack w) :: Int | w <- T.words (body p)])))
