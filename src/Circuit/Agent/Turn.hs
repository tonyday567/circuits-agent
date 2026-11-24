{-# LANGUAGE OverloadedStrings #-}

-- | Named runner circuits that tie free dual ends into a turn.
--
-- A turn is a /runner/ observation: it commits one token, then blocks on one
-- frame.  Framing lives port-side ('Circuit.Agent.StdPorts' stream marks);
-- the queue retry is the blocking boundary.  No polling, no backoff — the
-- halt is decided by content, not inferred from quiet.
--
-- The correlation between a command and its response is carried by the
-- 'TurnToken' envelope, not by pipe adjacency.  The mediator's residual
-- state holds the pending commands — /all/ of them, not one: the pending
-- cap is lifted, so pipelined commands each hold a slot and a response
-- matches when its 'thread' cites the command's id.  This makes zero-frame
-- and two-frame failures detectable in-band rather than by positional
-- guess.
--
-- For children that cannot stamp ids (ghci), correlation is in-band:
-- 'noncePipeline' appends a nonce echo (@⟜<n>@) to each command and reads
-- nonce-framed ports, so the child itself supplies the stamp and
-- pipelining is safe because children execute stdin in order.
--
-- Mark-carrying turns must use a 'Linear' channel policy; weakening policies
-- can drop a command or response and break correlation.
--
-- @
--   turn e        :: IO (Loop (,) (K IO) Text Text)
--   turnTimeout u e :: IO (Loop (,) (K IO) Text (Maybe Text))
-- @
module Circuit.Agent.Turn
  ( -- * Turn envelope
    TurnToken (..),

    -- * Turn process
    TurnState (..),
    emptyTurnState,
    turnProcess,

    -- * Runner circuits
    turn,
    turnTimeout,

    -- * Nonce correlation
    TurnPipeline (..),
    noncePipeline,
  )
where

import Circuit (FreeTrace, Syntax (Lift))
import Circuit.Agent (PostId)
import Circuit.Agent.StdPorts (NonceEvent (..), NoncePorts (..))
import Circuit.Body (Poles (..))
import Circuit.Category (K (..))
import Circuit.Machine (Moore (Moore))
import Data.IORef
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import System.Timeout (timeout)
import Prelude hiding (read)

-- | A turn envelope.  Commands are sent with an empty 'turnThread'; the
-- turn assigns them a fresh id.  Responses must carry that id in their
-- 'turnThread' to be matched with the pending command.
data TurnToken a = TurnToken
  { turnBody :: a,
    turnThread :: [PostId]
  }
  deriving (Eq, Show)

-- | Residual state of the turn mediator.  'nextId' supplies fresh command
-- ids; 'pending' holds every command awaiting its response — the cap is
-- lifted, so pipelined commands coexist and responses route by id.
data TurnState a = TurnState
  { nextId :: PostId,
    pending :: Map.Map PostId (TurnToken a)
  }
  deriving (Eq, Show)

-- | Initial turn state.
emptyTurnState :: TurnState a
emptyTurnState = TurnState 0 Map.empty

-- | Inject a command into the turn state, assigning it the next id.
injectCommand :: TurnState a -> a -> (TurnState a, TurnToken a)
injectCommand st body =
  let cmdId = nextId st
      cmd = TurnToken body [cmdId]
   in (st {nextId = succ cmdId, pending = Map.insert cmdId cmd (pending st)}, cmd)

-- | Match a response against the pending commands.
matchResponse :: TurnState a -> TurnToken a -> (TurnState a, Maybe (TurnToken a, TurnToken a))
matchResponse st@TurnState {pending} resp =
  case turnThread resp of
    [cmdId]
      | Just cmd <- Map.lookup cmdId pending ->
          (st {pending = Map.delete cmdId pending}, Just (cmd, resp))
    _ -> (st, Nothing)

-- | Moore that correlates responses with pending commands by thread.
--
-- * A token with empty thread is treated as a command: it receives the next
--   id and joins the pending map.
-- * A token with non-empty thread is treated as a response: it matches when
--   its thread equals a pending command's id, emitting the pair and leaving
--   every other pending command in place.
turnProcess :: Moore (,) (TurnState a, Maybe (TurnToken a, TurnToken a)) (->) (TurnToken a) (Maybe (TurnToken a, TurnToken a))
turnProcess = Moore (\tok -> step ((emptyTurnState, Nothing), tok)) step snd
  where
    step ((st, _), tok) =
      if null (turnThread tok)
        then (fst (injectCommand st (turnBody tok)), Nothing)
        else matchResponse st tok

-- | Read responses until the one citing @wanted@ arrives.  A response that
-- cites a different pending call is that call's business: it is stashed under
-- its own thread and left for it, so two outstanding calls cannot trade
-- answers.  A response citing no pending call is stashed for the same reason.
awaitResponse ::
  IORef (TurnState Text) ->
  IORef (Map.Map [PostId] (TurnToken Text)) ->
  Poles () (K IO) (TurnToken Text) (TurnToken Text) ->
  [PostId] ->
  IO Text
awaitResponse ref stash e wanted = loop
  where
    loop = do
      hit <- Map.lookup wanted <$> readIORef stash
      case hit of
        Just resp -> pure (turnBody resp)
        Nothing -> do
          resp <- runK (emit e) ()
          matched <- atomicModifyIORef' ref (`matchResponse` resp)
          case matched of
            Just (cmd, resp')
              | turnThread cmd == wanted -> pure (turnBody resp')
              | otherwise -> stashAndRetry (turnThread resp') resp'
            Nothing -> stashAndRetry (turnThread resp) resp
    stashAndRetry k r = do
      atomicModifyIORef' stash (\m -> (Map.insert k r m, ()))
      loop

-- | Run one turn: commit a body, then block until a matching response
-- arrives.  The correlation is by 'thread', not by position.  Responses
-- read while another turn is awaited are stashed by thread and found by
-- the turn they belong to — concurrent turns on one handle are safe.
turn ::
  Poles () (K IO) (TurnToken Text) (TurnToken Text) ->
  IO (FreeTrace (,) (K IO) Text Text)
turn e = do
  ref <- newIORef emptyTurnState
  stash <- newIORef Map.empty
  pure . Lift . K $ \body -> do
    cmd <- atomicModifyIORef' ref $ \st -> injectCommand st body
    runK (commit e) cmd
    awaitResponse ref stash e (turnThread cmd)

-- | 'turn' under a deadline (microseconds).  'Nothing' on expiry; the
-- unarrived response is not lost — the stash and the wire both still
-- hold it for a later turn.
turnTimeout ::
  Int ->
  Poles () (K IO) (TurnToken Text) (TurnToken Text) ->
  IO (FreeTrace (,) (K IO) Text (Maybe Text))
turnTimeout us e = do
  ref <- newIORef emptyTurnState
  stash <- newIORef Map.empty
  pure . Lift . K $ \body -> do
    cmd <- atomicModifyIORef' ref $ \st -> injectCommand st body
    runK (commit e) cmd
    timeout us (awaitResponse ref stash e (turnThread cmd))

-- | A nonce-correlated pipeline: 'tpSend' commits a command and returns
-- its id; 'tpRecv' blocks for that id's response.  Pipelining is safe —
-- children execute stdin in order, so answers arrive in id order — and
-- out-of-order answers route by nonce id anyway.
data TurnPipeline = TurnPipeline
  { tpSend :: Text -> IO PostId,
    tpRecv :: PostId -> IO Text
  }

-- | Turn correlation for children that cannot stamp ids (ghci).  Each
-- commit writes the body and a nonce echo line (@echo@ gives @putStrLn
-- "⟜<n>"@ for ghci, @echo "⟜<n>"@ for shells); the response is everything
-- the child printed before @⟜<n>@ — an empty payload is a zero-frame, a
-- multi-frame payload a two-frame, both visible in-band.
--
-- Precondition: 'tpRecv' only for ids 'tpSend' returned, at most once.
noncePipeline :: (PostId -> Text) -> NoncePorts Text -> IO TurnPipeline
noncePipeline echo ports = do
  ref <- newIORef (0, Map.empty, Map.empty)
  let send body = do
        (n, inbox, outstanding) <- readIORef ref
        npCommit ports (body <> "\n" <> echo n <> "\n")
        writeIORef ref (n + 1, inbox, Map.insert n () outstanding)
        pure n
      recv want = do
        (n, inbox, outstanding) <- readIORef ref
        case Map.lookup want inbox of
          Just payload -> do
            writeIORef ref (n, Map.delete want inbox, Map.delete want outstanding)
            pure payload
          Nothing
            | Map.member want outstanding -> do
                ev <- npEvent ports
                case ev of
                  Answered k payload -> do
                    modifyIORef' ref (\(n', ib, out) -> (n', Map.insert k payload ib, out))
                    recv want
                  Unterminated tail' -> do
                    modifyIORef' ref $ \(n', ib, out) ->
                      case Map.lookupMin out of
                        Just (oldest, _) -> (n', Map.insert oldest tail' ib, out)
                        Nothing -> (n', ib, out)
                    recv want
                  ChildExited _ -> do
                    modifyIORef' ref $ \(n', ib, out) ->
                      (n', Map.union ib (Map.map (const "") out), out)
                    recv want
            | otherwise ->
                error "turn: tpRecv of an unknown or already-received id"
  pure (TurnPipeline send recv)
