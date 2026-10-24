{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | process ports: death honesty (S1-S3/S5/S6), merged stdio (S4), nonce turns (T1).
module Axioma.Ports
  ( portsTopic,
  )
where

import Axioma.Common
import Circuit.Agent
import Circuit.Agent.StdPorts
import Circuit.Agent.StdPorts qualified as Ports
import Circuit.Agent.Turn qualified as TurnPort
import Circuit.Category (K (..))
import Circuit.Machine (Moore)
import Circuit.Syntax (eval)
import Control.Monad (void)
import Data.ByteString qualified as BS
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import System.Exit (ExitCode (..))
import System.Process (getProcessExitCode)
import System.Timeout (timeout)

default (Text)

portsTopic :: IO ()
portsTopic = do
  putStrLn "death honesty"

  -- S1: frame extraction is invariant under byte-chunk boundaries.
  do
    let runFrames :: ProcMarks -> [Maybe BS.ByteString] -> [BS.ByteString]
        runFrames marks inputs = concat (go (BS.empty, []) inputs)
          where
            sys = frameAgent marks id
            go _ [] = []
            go st (i : is) =
              let (o, st') = runCell sys st i
               in o : go st' is
        whole marks s = runFrames marks [Just s, Nothing]
        cuts2 s = [[BS.take i s, BS.drop i s] | i <- [0 .. BS.length s]]
        cuts3 s =
          [ [a, b, c]
          | i <- [0 .. BS.length s],
            let (a, bc) = BS.splitAt i s,
            j <- [i .. BS.length s],
            let (b, c) = BS.splitAt (j - i) bc
          ]
        samples =
          [ (lineMarks, "a\nb\n"),
            (ghciMarks, "x ghci> y \955> z"),
            (hermesMarks, "output\n❯ rest"),
            (sseMarks, "event: e\ndata: d\n\nevent: e2\n")
          ]
        properPrefixes (ProcMarks ms) =
          [(m1, m2) | m1 <- ms, m2 <- ms, m1 /= m2, m1 `T.isPrefixOf` m2]
        colliding = ProcMarks ["\n\n", "\n"]
    assert "S1 shipped grammars have no proper-prefix mark pairs" $
      all ((null . properPrefixes) . fst) samples
    assert "S1 frames are invariant under every 2- and 3-cut" $
      all
        (\(marks, s) -> all (\cs -> runFrames marks (map Just cs ++ [Nothing]) == whole marks s) (cuts2 s ++ cuts3 s))
        samples
    -- claude's counterexample, pinned so the guard above is not vacuous:
    -- with a prefix collision, the cut a\n | \nb emits ["a","","b"],
    -- not ["a","b"].
    assert "S1 the prefix collision breaks the cut (the guard is load-bearing)" $
      runFrames colliding [Just "a\n", Just "\nb", Nothing]
        /= runFrames colliding [Just "a\n\nb", Nothing]

  -- S2: death is content — a dead child delivers its exit code.
  do
    pp <- runK (eval (openStdPorts id id (defaultProcConfig {procCommand = "sh", procArgs = ["-c", "exit 3"], procMarks = lineMarks}))) ()
    m <- timeout 5_000_000 (runK (emit (stdOut pp)) ())
    assert "S2 a dead child delivers the terminal frame with exit 3" $
      m == Just (Exited (ExitFailure 3))
    stdClose pp

  -- S3: close reaps — terminate, wait, no zombie.
  do
    pp <- runK (eval (openStdPorts id id (defaultProcConfig {procCommand = "sh", procArgs = ["-c", "sleep 30"], procMarks = lineMarks}))) ()
    mClose <- timeout 5_000_000 (void (stdClose pp))
    assert "S3 stdClose terminates and reaps within the bound" $ isJust mClose
    case stdProcess pp of
      Just ph -> do
        mc <- getProcessExitCode ph
        assert "S3 the child is reaped: getProcessExitCode returns Just" $ isJust mc
      Nothing -> assert "S3 openStdPorts carries the process handle" False

  -- S5: a dribbled frame — partial bytes, a pause, then the mark — still
  -- arrives whole, exactly once.
  do
    pp <-
      runK
        ( eval
            ( openStdPorts
                id
                id
                (defaultProcConfig {procCommand = "sh", procArgs = ["-c", "printf 'par'; sleep 0.2; printf 'tial\\n'; exec sleep 5"], procMarks = lineMarks})
            )
        )
        ()
    f1 <- timeout 5_000_000 (runK (emit (stdOut pp)) ())
    assert "S5 a dribbled frame arrives whole, exactly once" $
      f1 == Just (Payload "partial")
    stdClose pp

  -- S6: honest doubles — block, die, zero frames, two frames.
  do
    pp <- Ports.echo pure :: IO (StdPorts String String ())
    mBlocked <- timeout 200_000 (runK (emit (stdOut pp)) ())
    assert "S6 a read before any write blocks" $ mBlocked == Nothing
    runK (commit (stdIn pp)) "hi"
    f <- runK (emit (stdOut pp)) ()
    assert "S6 the echo replies after the write" $ f == Payload "hi"

    sp <- scriptedDouble [Quiet, Reply2 (++ "1") (++ "2"), Die (ExitFailure 7)]
    runK (commit (stdIn sp)) "a"
    mq <- timeout 200_000 (runK (emit (stdOut sp)) ())
    assert "S6 Quiet answers nothing (the read blocks)" $ mq == Nothing
    runK (commit (stdIn sp)) "b"
    g1 <- runK (emit (stdOut sp)) ()
    g2 <- runK (emit (stdOut sp)) ()
    assert "S6 Reply2 emits two frames for one token" $
      [g1, g2] == [Payload "b1", Payload "b2"]
    runK (commit (stdIn sp)) "c"
    g3 <- runK (emit (stdOut sp)) ()
    assert "S6 Die delivers the terminal frame once" $ g3 == Exited (ExitFailure 7)
    runK (commit (stdIn sp)) "d"
    mAfter <- timeout 200_000 (runK (emit (stdOut sp)) ())
    assert "S6 reads block after death" $ mAfter == Nothing

    -- a quiet agent answers nothing: runPort observes the block as absence,
    -- and the carrier still records the committed input.
    let quietAgent :: Agent (->) [Post Text] (Post Text) [Post Text]
        quietAgent = cellToAgent (tape (const []))
        qIn = mkPost "human" ["j"] "quiet-ask"
        (mOut, seat') = runPort quietAgent (PortSeat (AgentSeat [] []) [] []) qIn
    assert "S6 a quiet agent answers nothing (the port emit would block)" $
      mOut == Nothing && asState (psAgent seat') == [qIn]

  putStrLn "merged stdio (S4)"
  do
    pp <-
      runK
        ( eval
            ( openStdPorts
                id
                id
                ( defaultProcConfig
                    { procCommand = "sh",
                      procArgs = ["-c", "printf 'b\\n' >&2; printf 'a\\n'; sleep 1"],
                      procMarks = lineMarks,
                      procMergeStderr = True
                    }
                )
            )
        )
        ()
    f1 <- timeout 5_000_000 (runK (emit (stdOut pp)) ())
    assert "S4 merged: stderr rides the same pipe, ordered before stdout" $
      f1 == Just (Payload "b")
    f2 <- timeout 5_000_000 (runK (emit (stdOut pp)) ())
    assert "S4 merged: the stdout follow-up arrives second" $
      f2 == Just (Payload "a")
    mErr <- timeout 200_000 (runK (emit (stdErr pp)) ())
    assert "S4 merged: the stderr pole has nothing of its own" $ mErr == Nothing
    stdClose pp

  putStrLn "nonce correlation (T1)"

  -- The calculus half: the mediator is multi-pending.  Counterexample
  -- (the old single-pending state): respB finds no match and is dropped,
  -- so only the last pair correlates.
  do
    let sys =
          TurnPort.turnProcess ::
            Moore
              (,)
              (TurnPort.TurnState Text, Maybe (TurnPort.TurnToken Text, TurnPort.TurnToken Text))
              (->)
              (TurnPort.TurnToken Text)
              (Maybe (TurnPort.TurnToken Text, TurnPort.TurnToken Text))
        cmdA = TurnPort.TurnToken "a" []
        cmdB = TurnPort.TurnToken "b" []
        respB = TurnPort.TurnToken "rb" [1]
        respA = TurnPort.TurnToken "ra" [0]
        outs = iterateAgent sys (TurnPort.emptyTurnState, Nothing) [cmdA, cmdB, respB, respA]
        expected =
          [ Nothing,
            Nothing,
            Just (TurnPort.TurnToken "b" [1], respB),
            Just (TurnPort.TurnToken "a" [0], respA)
          ]
    assert "T1 the pending cap is lifted: out-of-order responses both correlate" $
      outs == expected

  -- The runner half: a real nonce-speaking child (an eval loop), two
  -- commands in flight before either response is read.
  do
    let evalCfg =
          defaultProcConfig
            { procCommand = "sh",
              procArgs = ["-c", "while IFS= read -r line; do eval \"$line\"; done"]
            }
    ports <- openNonceStdPorts encodeUtf8 decodeUtf8 evalCfg
    -- The echo prints the nonce with no trailing newline — the payload is
    -- the bytes between nonces, and a stray newline would pollute the
    -- next turn (ghci side: @putStr "⟜<n>"@, not putStrLn).
    pipe <- TurnPort.noncePipeline (\n -> "printf '\x27DC" <> T.pack (show n) <> "'") ports
    a <- TurnPort.tpSend pipe "echo alpha"
    b <- TurnPort.tpSend pipe "echo beta"
    ra <- timeout 5_000_000 (TurnPort.tpRecv pipe a)
    rb <- timeout 5_000_000 (TurnPort.tpRecv pipe b)
    assert "T1 pipelined commands correlate by nonce, in order" $
      ra == Just "alpha\n" && rb == Just "beta\n"
    z <- TurnPort.tpSend pipe "true"
    rz <- timeout 5_000_000 (TurnPort.tpRecv pipe z)
    assert "T1 a zero-frame turn is detectable (empty payload)" $ rz == Just ""
    t2 <- TurnPort.tpSend pipe "echo one; echo two"
    rt2 <- timeout 5_000_000 (TurnPort.tpRecv pipe t2)
    assert "T1 a two-frame turn is detectable in the payload" $
      fmap (filter (not . T.null) . T.splitOn "\n") rt2 == Just ["one", "two"]
    npClose ports

  putStrLn "tool call"
  do
    -- type: tool call ≡ Post addressed to the tool
    let call :: Post Text
        call = toolCall "j" "calc" "1 2 3"
    assert "tool call addr is the tool" $ to call == ["calc"]
    assert "tool call body is the args" $ body call == "1 2 3"

    -- code: pure Agent that emits a tool-call Post
    let caller :: Agent (->) [Post Text] (Post Text) [Post Text]
        caller = cellToAgent (tape callCalc)
        human = mkPost "human" ["j"] "please sum 1 2 3"
        (outs, _) = runAgentShard caller (AgentSeat [] []) [human]
    assert "agent emits one tool-call post" $
      case outs of
        [p] -> to p == ["calc"] && body p == "1 2 3"
        _ -> False

    -- example: one token in, tool-call token out — the pure port turn
    let (pOut, seatPort) = runPort caller (PortSeat (AgentSeat [] []) [] []) human
    assert "port example: human Post in → tool-call Post out" $
      pOut == Just call
    assert "port carrier saw the human input" $
      length (asState (psAgent seatPort)) == 1

  putStrLn "withhold"
  do
    let secret = mkPost "ops" ["j"] "bus emergency — do not show yet"
        public = mkPost "human" ["j"] "hi j"
        held = [secret, public] -- store exists; not all of it is delivered
        agent = cellToAgent (tape (reply "j")) :: Agent (->) [Post Text] (Post Text) [Post Text]

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
