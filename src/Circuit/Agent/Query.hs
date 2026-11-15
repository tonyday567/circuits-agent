{-# LANGUAGE OverloadedStrings #-}

-- | Generic query-to-agent adapters.
--
-- Turns any @Text -> IO Text@ boundary into an input-seeded 'Agent' that
-- consumes addressed posts and emits reply posts. The functions here know
-- nothing about external CLI processes, session files, or concrete binaries.
module Circuit.Agent.Query
  ( -- * Session assembly and reply building
    sessionPrompt,
    replyPosts,
    synthesisPosts,

    -- * Agent adapters
    queryBody,
    queryBodyWith,
    synthBody,
    echoBody,
  )
where

import Circuit.Agent (Agent, Post (..), PostId, ioAgent, mkPost, replyTo, sortNub, synthesis)
import Data.Maybe (listToMaybe)
import Data.Text (Text)
import Data.Text qualified as T

-- | Session assembly for the opaque seat: bodies, oldest-first, one per line.
sessionPrompt :: [Post Text] -> Text
sessionPrompt = T.intercalate "\n" . map body

-- | Build reply posts from a cleaned agent response.
--
-- Addresses the last input's sender, preserves any other names on the
-- original wire, and threads onto the last input's 'PostId' when supplied.
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
synthesisPosts :: Text -> [Post Text] -> [PostId] -> Text -> [Post Text]
synthesisPosts who ins ids reply =
  case (ins, T.strip reply) of
    (_, r) | T.null r -> []
    ([], _) -> []
    (_, r) ->
      let audience = filter (/= who) (sortNub (concatMap (\p -> from p : to p) ins))
          parentIds = take (length ins) ids
       in [if null parentIds then mkPost who audience r else synthesis who audience parentIds r]

-- | Opaque evaluate seat. Commits collect the independent input posts; the
-- first emit runs the query once and returns its reply beside 'Done'.
queryBody :: Text -> (Text -> IO Text) -> IO (Agent [Post Text])
queryBody = queryBodyWith replyPosts

-- | Opaque synthesis seat: the reply cites every input's sender as ancestry.
synthBody :: Text -> (Text -> IO Text) -> IO (Agent [Post Text])
synthBody = queryBodyWith synthesisPosts

-- | 'queryBody' parameterised on the reply-to-posts builder. Bare posts do
-- not carry log stamps, so thread ids are supplied by the delivery runner.
queryBodyWith ::
  (Text -> [Post Text] -> [PostId] -> Text -> [Post Text]) ->
  Text ->
  (Text -> IO Text) ->
  IO (Agent [Post Text])
queryBodyWith posts who query =
  pure $ ioAgent $ \ins -> do
    if null ins
      then pure []
      else do
        reply <- query (sessionPrompt ins)
        pure (posts who ins [] reply)

-- | Mock seat: reply body is the session prompt.
echoBody :: Text -> IO (Agent [Post Text])
echoBody who = queryBody who pure
