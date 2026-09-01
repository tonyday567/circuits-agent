{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-pattern-namespace-specifier #-}

-- | Bus message framing.
--
-- Storage format is JSON Lines: one stamped 'Post' per line with fields
-- @id@, @ts@, @from@, @to@, @thread@ and @body@.  The body is never mutated
-- for framing; JSON string encoding handles newlines in the standard way.
--
-- The file image is a stream with the same 'Circuit.Stream' ends as the pure
-- log: 'Log' is oldest-first on disk, so append is 'snoc' and read is
-- 'uncons'.  The pure 'Log' is newest-first; that is the dual linearisation of
-- the same thread DAG, not a different algebra.
--
-- 'Log a' stores 'Stamped a' values in memory — no encoding in the hot path.
-- File persistence uses 'frameStored'/'unframeStored' via 'PostBody' at the
-- storage boundary.
--
-- Backwards compatibility: 'parseLineAt' also accepts the legacy flat triple
-- @{\"ts\":..., \"sender\":..., \"body\":...}@ and the bracket format
-- @[timestamp] sender: body@ so existing log files remain readable.  Those
-- legacy lines are assigned the supplied line index as their id and empty
-- @to@/@thread@ lists.
module Circuit.Agent.Framing
  ( -- * Types
    PostId,
    PostBody (..),
    Stamped,
    pattern Stamped,
    stamp,
    stamped,
    Log (..),

    -- * Stream ends (re-exported from Circuit.Stream)
    Cons (..),
    Snoc (..),
    Uncons (..),
    These (..),

    -- * Encoding
    frameStored,
    framePost,

    -- * Parsing
    unframeStored,
    parseLineAt,
    parsePost,
    parseMessage,
    parseMessageTs,

    -- * Rendering
    renderStored,
    renderMessage,

    -- * Time
    formatNow,
    parseTimeText,

    -- * File helpers
    readLogFile,
    encodeLog,
  )
where

import Circuit.Agent (Post (..), PostId)
import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Maybe (mapMaybe)
import Data.Scientific (Scientific, base10Exponent, coefficient)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Data.Text.IO qualified as TIO
import Data.Time (UTCTime, defaultTimeLocale, formatTime, getCurrentTime, parseTimeM)
import Data.Vector qualified as V
import Numeric.Natural (Natural)
import "circuits" Circuit.Boundary (stamp, stamped)
import "circuits" Circuit.Boundary qualified as Stamped
import "circuits" Circuit.Stream (Cons (..), Snoc (..), These (..), Uncons (..))
import "circuits-parser" Circuit.Parser.Json (Json (..), decodeJson, encodeJson)
import Prelude

-- | Encodable/decodable post body. Every body type in the bus must
-- support JSON round-trip through 'circuits-parser''s 'Json' type.
class PostBody a where
  encodePostBody :: a -> Json
  decodePostBody :: Json -> Maybe a

instance PostBody Text where
  encodePostBody = JString
  decodePostBody (JString t) = Just t
  decodePostBody _ = Nothing

-- | Storage boundary: a post with its assigned id and timestamp.
--
-- This is the agent-side specialisation of 'Circuit.Boundary.Stamped' from
-- @circuits@ core: the occurrence token is the @(UTCTime, PostId)@ pair and
-- the payload is a @Post a@.  The core type carries the free theorem that
-- 'fmap' cannot touch the stamp, so the agent shares it rather than
-- duplicating it.
type Stamped a = Stamped.Stamped (UTCTime, PostId) (Post a)

-- | The core 'Circuit.Boundary.Stamped' constructor specialised to the agent's
-- occurrence token @(UTCTime, PostId)@.
pattern Stamped :: (UTCTime, PostId) -> Post a -> Stamped a
pattern Stamped tok post = Stamped.Stamped tok post

{-# COMPLETE Stamped #-}

-- | The log image: a stream of stamped posts, oldest first.
newtype Log a = Log {unLog :: [Stamped a]}
  deriving (Show, Eq, Functor)

-- | Append is the natural operation: one element at the end.
instance Snoc (Log a) (Stamped a) where
  snoc (Log xs) p = Log (xs ++ [p])
  snocNil = Log []

-- | Read peels the oldest element first.
instance Uncons (Log a) (Stamped a) where
  uncons (Log []) = That (Log [])
  uncons (Log [x]) = This x
  uncons (Log (x : xs)) = These x (Log xs)
  nil = Log []

-- | Prepend is the dual view: a newest-first stream over the same image.
instance Cons (Log a) (Stamped a) where
  cons p (Log xs) = Log (p : xs)
  consNil = Log []

-- | Current UTC time as an ISO-8601 string.
formatNow :: IO Text
formatNow = T.pack . formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" <$> getCurrentTime

-- | Parse an ISO-8601 string to UTCTime, accepting the format we write.
parseTimeText :: Text -> Maybe UTCTime
parseTimeText = parseTimeM True defaultTimeLocale "%Y-%m-%dT%H:%M:%S" . T.unpack

-- | Encode a 'Stamped a' as a single canonical JSON Lines object.
frameStored :: (PostBody a) => Stamped a -> Text
frameStored (Stamped (ts, i) (Post from' to' thread' body')) =
  decodeUtf8 $
    encodeJson $
      JObject
        [ ("id", JNumber (fromIntegral i)),
          ("ts", JString (T.pack (formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" ts))),
          ("from", JString from'),
          ("to", JArray (V.fromList (map JString to'))),
          ("thread", JArray (V.fromList (map (JNumber . fromIntegral) thread'))),
          ("body", encodePostBody body')
        ]

-- | Encode a bare 'Post a' as a single JSON Lines object (the protocol
-- format sent to the stamping bus daemon).
framePost :: (PostBody a) => Post a -> Text
framePost p =
  decodeUtf8 $
    encodeJson $
      JObject
        [ ("from", JString (from p)),
          ("to", JArray (V.fromList (map JString (to p)))),
          ("thread", JArray (V.fromList (map (JNumber . fromIntegral) (thread p)))),
          ("body", encodePostBody (body p))
        ]

-- | Unframe a canonical stamped storage line (the inverse of 'frameStored').
-- Returns 'Nothing' if the line is not valid JSON with the expected fields.
unframeStored :: (PostBody a) => Text -> Maybe (Stamped a)
unframeStored line =
  case decodeJson (encodeUtf8 line) of
    Right (JObject o) -> do
      pid <- lookupNumber "id" (JObject o) >>= naturalFromScientific
      JString tsStr <- lookup "ts" o
      ts <- parseTimeText tsStr
      JString from' <- lookup "from" o
      to' <- lookupStrings "to" (JObject o)
      thread' <- lookupPostIds "thread" (JObject o)
      bodyVal <- lookup "body" o
      body' <- decodePostBody bodyVal
      pure (Stamped (ts, pid) (Post from' to' thread' body'))
    _ -> Nothing

-- | Parse a bare 'Post a' line (no stamp).
parsePost :: (PostBody a) => Text -> Maybe (Post a)
parsePost line =
  case decodeJson (encodeUtf8 line) of
    Right (JObject o) -> do
      JString from' <- lookup "from" o
      to' <- lookupStrings "to" (JObject o)
      thread' <- lookupPostIds "thread" (JObject o)
      bodyVal <- lookup "body" o
      body' <- decodePostBody bodyVal
      pure (Post from' to' thread' body')
    _ -> Nothing

-- | Like 'unframeStored', but also accepts the legacy flat triple and bracket
-- formats, assigning the supplied line index as the id. Legacy-only, 'Text' body.
parseLineAt :: Int -> Text -> Maybe (Stamped Text)
parseLineAt idx line =
  unframeStored line
    <|> parseLegacyTriple idx line
    <|> parseLegacyBracket idx line

-- | Parse a raw log line into @(from, body)@, accepting the stamped format
-- and both legacy formats.
parseMessage :: Text -> Maybe (Text, Text)
parseMessage line = do
  Stamped _ p <- parseLineAt 0 line
  pure (from p, body p)

-- | Extract just the timestamp from a raw log line.
parseMessageTs :: Text -> Maybe Text
parseMessageTs line = do
  Stamped (ts, _) _ <- parseLineAt 0 line
  pure (T.pack (formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" ts))

-- | Render a 'Stamped a' for human display as @[id@ts] from: body@.
renderStored :: (PostBody a) => Stamped a -> Text
renderStored (Stamped (ts, i) (Post from' _to' _thread' body')) =
  T.concat ["[", T.pack (show i), "@", T.pack (formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" ts), "] ", from', ": ", renderBody body']
  where
    renderBody b = case decodeUtf8 (encodeJson (encodePostBody b)) of
      t -> T.strip t

-- | Render a raw log line for human display.
renderMessage :: Text -> Maybe Text
renderMessage line = renderStored <$> parseLineAt 0 line

-- | Read a log file into a 'Log a', oldest first. Malformed lines are skipped.
readLogFile :: (PostBody a) => FilePath -> IO (Log a)
readLogFile path = do
  content <- TIO.readFile path
  let ls = filter (not . T.null) (T.lines content)
  pure (Log (mapMaybe unframeStored ls))

-- | Encode a 'Log a' to raw JSONL text for file persistence.
encodeLog :: (PostBody a) => Log a -> [Text]
encodeLog = map frameStored . reverse . unLog

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

naturalFromScientific :: Scientific -> Maybe Natural
naturalFromScientific s
  | base10Exponent s >= 0 = Just (fromIntegral (coefficient s) * 10 ^ base10Exponent s)
  | otherwise = Nothing

lookupNumber :: Text -> Json -> Maybe Scientific
lookupNumber k (JObject o) = case lookup k o of
  Just (JNumber n) -> Just n
  _ -> Nothing
lookupNumber _ _ = Nothing

lookupStrings :: Text -> Json -> Maybe [Text]
lookupStrings k (JObject o) = case lookup k o of
  Just (JArray vs) -> Just [s | JString s <- V.toList vs]
  _ -> Nothing
lookupStrings _ _ = Nothing

lookupPostIds :: Text -> Json -> Maybe [PostId]
lookupPostIds k (JObject o) = case lookup k o of
  Just (JArray vs) -> Just [i | JNumber s <- V.toList vs, Just i <- [naturalFromScientific s]]
  _ -> Nothing
lookupPostIds _ _ = Nothing

-- ---------------------------------------------------------------------------
-- Legacy formats
-- ---------------------------------------------------------------------------

-- | Legacy flat triple: @{\"ts\":\"...\", \"sender\":\"...\", \"body\":\"...\"}@.
parseLegacyTriple :: Int -> Text -> Maybe (Stamped Text)
parseLegacyTriple idx line =
  case decodeJson (encodeUtf8 line) of
    Right (JObject o) -> do
      JString tsStr <- lookup "ts" o
      ts <- parseTimeText tsStr
      JString sender' <- lookup "sender" o
      JString body' <- lookup "body" o
      pure (Stamped (ts, fromIntegral idx) (Post sender' [] [] body'))
    _ -> Nothing

-- | Legacy bracket format: @[timestamp] sender: body@.
parseLegacyBracket :: Int -> Text -> Maybe (Stamped Text)
parseLegacyBracket idx line =
  case T.breakOnEnd "]" line of
    (pref, rest)
      | not (T.null pref),
        let tsStr = T.dropWhile (== '[') (T.init pref) -> do
          ts <- parseTimeText tsStr
          let (sender', body') = T.breakOn ":" (T.strip rest)
          guard (not (T.null sender'))
          pure (Stamped (ts, fromIntegral idx) (Post (T.strip sender') [] [] (T.strip (T.drop 1 body'))))
    _ -> Nothing
