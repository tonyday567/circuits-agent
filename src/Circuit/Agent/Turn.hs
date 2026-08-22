-- | Named runner circuits that tie free dual ends into a turn.
--
-- A turn is a /runner/ observation: it commits one token, then blocks on one
-- frame.  Framing lives port-side ('Circuit.Agent.StdPorts' stream marks);
-- the queue retry is the blocking boundary.  No polling, no backoff — the
-- halt is decided by content, not inferred from quiet.
--
-- The correlation between a command and its response is carried by the
-- 'TurnToken' envelope, not by pipe adjacency.  The mediator's residual
-- state holds the pending command; a response matches when its 'thread'
-- cites the command's id.  This makes zero-frame and two-frame failures
-- detectable in-band rather than by positional guess.
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

    -- * Turn mediator
    TurnState (..),
    turnMediator,

    -- * Runner circuits
    turn,
    turnTimeout,
  )
where

import Circuit (Loop (..))
import Circuit.Agent (PostId)
import Circuit.Category (K (..))
import Circuit.Ends (Ends (..), commit, emit, open)
import Circuit.Mediate (Mediator (..))
import Data.IORef
import Data.Text (Text)
import System.Timeout (timeout)
import Prelude

-- | A turn envelope.  Commands are sent with an empty 'turnThread'; the
-- turn assigns them a fresh id.  Responses must carry that id in their
-- 'turnThread' to be matched with the pending command.
data TurnToken a = TurnToken
  { turnBody :: a,
    turnThread :: [PostId]
  }
  deriving (Eq, Show)

-- | Residual state of the turn mediator.  'nextId' supplies fresh command
-- ids; 'pending' holds the command awaiting its response.
data TurnState a = TurnState
  { nextId :: PostId,
    pending :: Maybe (PostId, TurnToken a)
  }
  deriving (Eq, Show)

-- | Initial turn state.
emptyTurnState :: TurnState a
emptyTurnState = TurnState 0 Nothing

-- | Inject a command into the turn state, assigning it the next id.
injectCommand :: TurnState a -> a -> (TurnState a, TurnToken a)
injectCommand st body =
  let cmdId = nextId st
      cmd = TurnToken body [cmdId]
   in (st {nextId = succ cmdId, pending = Just (cmdId, cmd)}, cmd)

-- | Match a response against the pending command.
matchResponse :: TurnState a -> TurnToken a -> (TurnState a, Maybe (TurnToken a, TurnToken a))
matchResponse st@TurnState {pending = Nothing} _ = (st, Nothing)
matchResponse st@TurnState {pending = Just (cmdId, cmd)} resp
  | turnThread resp == [cmdId] = (st {pending = Nothing}, Just (cmd, resp))
  | otherwise = (st, Nothing)

-- | Mediator that correlates responses with the pending command by thread.
--
-- * A token with empty thread is treated as a command: it receives the next
--   id and is stored as the pending command.
-- * A token with non-empty thread is treated as a response: it matches when
--   its thread equals the pending command's id, emitting the pair.
turnMediator :: Mediator (TurnState a) (TurnToken a) (TurnToken a, TurnToken a)
turnMediator =
  Mediator
    { medInit = emptyTurnState,
      medStep = \st tok ->
        if null (turnThread tok)
          then (fst (injectCommand st (turnBody tok)), Nothing)
          else matchResponse st tok,
      medOwed = \st -> case pending st of Nothing -> False; Just _ -> True,
      medDraw = \_ _ -> Nothing
    }

-- | Read the unit ends used to plug the unused side of a commit or emit.
unitEnds :: Ends (K IO) () ()
unitEnds = open

-- | Run one turn: commit a body, then block until a matching response
-- arrives.  The correlation is by 'thread', not by position.
turn ::
  Ends (K IO) (TurnToken Text) (TurnToken Text) ->
  IO (Loop (,) (K IO) Text Text)
turn e = do
  ref <- newIORef emptyTurnState
  pure . Lift . K $ \body -> do
    cmd <- atomicModifyIORef' ref $ \st -> injectCommand st body
    runK (commit (conjoint e) outU) cmd
    let loop = do
          resp <- runK (emit (companion e) inU) ()
          mResult <- atomicModifyIORef' ref $ \st -> matchResponse st resp
          case mResult of
            Just (_, resp') -> pure (turnBody resp')
            Nothing -> loop
    loop
  where
    Ends _ outU = unitEnds
    Ends inU _ = unitEnds

-- | 'turn' under a deadline (microseconds).  'Nothing' on expiry; the
-- unarrived response is not lost — the next emit still receives it.
turnTimeout ::
  Int ->
  Ends (K IO) (TurnToken Text) (TurnToken Text) ->
  IO (Loop (,) (K IO) Text (Maybe Text))
turnTimeout us e = do
  ref <- newIORef emptyTurnState
  pure . Lift . K $ \body -> do
    cmd <- atomicModifyIORef' ref $ \st -> injectCommand st body
    runK (commit (conjoint e) outU) cmd
    timeout us $ do
      let loop = do
            resp <- runK (emit (companion e) inU) ()
            mResult <- atomicModifyIORef' ref $ \st -> matchResponse st resp
            case mResult of
              Just (_, resp') -> pure (turnBody resp')
              Nothing -> loop
      loop
  where
    Ends _ outU = unitEnds
    Ends inU _ = unitEnds
