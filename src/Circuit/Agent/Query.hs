{-# LANGUAGE OverloadedStrings #-}

-- | Generic query-to-shard adapters.
--
-- Turns any @Text -> IO Text@ boundary into a 'Shard' that consumes addressed
-- posts and emits reply posts.  The functions here know nothing about external
-- CLI processes, session files, or concrete binaries — that operational layer
-- lives in @Free.Agent.Cli@.
module Circuit.Agent.Query
  ( -- * Session assembly and reply building
    sessionPrompt,
    replyPosts,
    synthesisPosts,

    -- * Shard adapters
    queryShard,
    queryShardWith,
    synthShard,
    echoShard,
    runShardIO,
  )
where

import Circuit.Agent (Ends (..), Post (..), PostId, Shard, close, mkPost, replyTo, shard, sortNub, synthesis)
import Circuit.Category (K (..))
import Data.IORef (atomicModifyIORef', newIORef, writeIORef)
import Data.Maybe (listToMaybe)
import Data.Text (Text)
import Data.Text qualified as T

-- | Session assembly for the opaque seat: bodies, oldest-first, one per line.
--
-- This is the discoverable side of the boundary (data).  How the query folds
-- it is not.
sessionPrompt :: [Post Text] -> Text
sessionPrompt = T.intercalate "\n" . map body

-- | Build reply posts from a cleaned agent response.
--
-- Addresses the last input's sender, preserves any other names on the
-- original wire (e.g. the bus channel), and threads onto the last input's
-- 'PostId' when one is supplied.  Empty reply → no posts (quiet).
--
-- The caller passes one 'PostId' per input post in the same order.  If the
-- ids are missing or misaligned, the reply is still addressed correctly but
-- carries no thread edge (see 'mkPost') — the honest fallback when a shard
-- does not have access to the stamped log.
replyPosts :: Text -> [Post Text] -> [PostId] -> Text -> [Post Text]
replyPosts who ins ids reply =
  case (listToMaybe (reverse ins), T.strip reply) of
    (_, r) | T.null r -> []
    (Nothing, _) -> []
    (Just lastIn, r) ->
      let to' = from lastIn : filter (/= who) (to lastIn)
       in case listToMaybe (reverse ids) of
            Just parentId -> [replyTo who parentId lastIn r]
            Nothing -> [mkPost who to' r]

-- | Build one synthesis post from a cleaned agent response.
--
-- The honest twin of 'replyPosts' for seats that fold /every/ input into
-- their answer: ancestry cites every input's 'PostId' (see 'synthesis'),
-- and the audience is every input's sender and wire name, minus self.
-- Empty reply or no inputs → no posts (quiet).
--
-- The caller passes one 'PostId' per input post.  If ids are missing the
-- synthesis is still addressed correctly but carries no thread edge.
synthesisPosts :: Text -> [Post Text] -> [PostId] -> Text -> [Post Text]
synthesisPosts who ins ids reply =
  case (ins, T.strip reply) of
    (_, r) | T.null r -> []
    ([], _) -> []
    (_, r) ->
      let audience = filter (/= who) (sortNub (concatMap (\p -> from p : to p) ins))
          parentIds = take (length ins) ids
       in [if null parentIds then mkPost who audience r else synthesis who audience parentIds r]

-- | Opaque evaluate seat: any @Text -> IO Text@ behind list ends.
--
-- Commit assembles a session prompt from the input posts; emit is
-- 'replyPosts' of the query result (empty = quiet).
--
-- TODO: this generic seat does not have access to stamped log ids, so
-- emitted replies carry no thread edge.  Callers that need provenance
-- should use a variant that supplies parent ids.
queryShard :: Text -> (Text -> IO Text) -> IO (Shard IO [Post Text] [Post Text])
queryShard = queryShardWith replyPosts

-- | Opaque synthesis seat: like 'queryShard', but the emit cites every
-- input's sender as ancestry ('synthesisPosts').  For seats that fold the
-- whole input into one answer — the honest-provenance twin of
-- 'queryShard'.
--
-- TODO: like 'queryShard', the generic seat has no ids and therefore emits
-- syntheses without thread edges.
synthShard :: Text -> (Text -> IO Text) -> IO (Shard IO [Post Text] [Post Text])
synthShard = queryShardWith synthesisPosts

-- | 'queryShard' parameterised on the reply-to-posts builder.
queryShardWith ::
  (Text -> [Post Text] -> [PostId] -> Text -> [Post Text]) ->
  Text ->
  (Text -> IO Text) ->
  IO (Shard IO [Post Text] [Post Text])
queryShardWith posts who query = do
  outbox <- newIORef []
  pure $
    shard
      ( \ins ->
          if null ins
            then writeIORef outbox []
            else do
              reply <- query (sessionPrompt ins)
              -- Generic seats have no stamped parent ids; the builder's
              -- fallback (mkPost) keeps addressing honest.
              writeIORef outbox (posts who ins [] reply)
      )
      (atomicModifyIORef' outbox ([],))

-- | Mock seat: reply body is the session prompt (echo).
--
-- Demonstrates the living-agent path without a real query.
echoShard :: Text -> IO (Shard IO [Post Text] [Post Text])
echoShard who = queryShard who pure

-- | One closed shard turn: commit @ins@, emit replies.
runShardIO :: Shard IO [Post Text] [Post Text] -> [Post Text] -> IO [Post Text]
runShardIO sh = runK (close (conjoint sh) (companion sh))
