{-# LANGUAGE OverloadedStrings #-}

-- | Bus message framing.
--
-- Storage format is JSON Lines: one stamped 'Post' per line with fields
-- @id@, @ts@, @from@, @to@, @thread@ and @body@.  The body is never mutated
-- for framing; JSON string encoding handles newlines in the standard way.
--
-- The file image is a stream with the same 'Circuit.Stream' ends as the pure
-- log: 'Jsonl' is oldest-first on disk, so append is 'snoc' and read is
-- 'uncons'.  The pure 'Log' is newest-first; that is the dual linearisation of
-- the same thread DAG, not a different algebra.
--
-- Backwards compatibility: 'parseLineAt' also accepts the legacy flat triple
-- @{\"ts\":..., \"sender\":..., \"body\":...}@ and the bracket format
-- @[timestamp] sender: body@ so existing log files remain readable.  Those
-- legacy lines are assigned the supplied line index as their id and empty
-- @to@/@thread@ lists.
module Circuit.Agent.Framing
  ( -- * Types
    PostId,
    Stamped (..),
    Jsonl (..),

    -- * Stream ends (re-exported from Circuit.Stream)
    Cons (..),
    Snoc (..),
    Uncons (..),
    These (..),

    -- * Encoding
    frameStored,
    framePost,

    -- * Parsing
    parseLine,
    parseLineAt,
    parsePost,
    parseMessage,
    parseMessageTs,

    -- * Rendering
    renderStored,
    renderMessage,

    -- * Time
    formatNow,
  )
where

import Circuit.Agent (Post (..), PostId)
import "circuits-parser" Circuit.Parser.Json (Json (..), decodeJson, encodeJson)
import "circuits" Circuit.Stream (Cons (..), Snoc (..), These (..), Uncons (..))
import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Scientific (Scientific, base10Exponent, coefficient)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Data.Time (UTCTime, defaultTimeLocale, formatTime, getCurrentTime, parseTimeM)
import Data.Vector qualified as V
import Numeric.Natural (Natural)
import Prelude

-- | Storage boundary: a post with its assigned id and timestamp.
data Stamped a = Stamped
  { timeStamp :: UTCTime,
    stamp :: PostId,
    stamped :: Post a
  }
  deriving (Show, Eq, Functor)

-- | The file image: a stream of raw JSONL lines, oldest first.
newtype Jsonl = Jsonl { unJsonl :: [Text] }
  deriving (Show, Eq)

-- | Append is the natural file operation: a new line at the end.
instance Snoc Jsonl (Stamped Text) where
  snoc (Jsonl xs) p = Jsonl (xs ++ [frameStored p])
  snocNil = Jsonl []

-- | Read peels the oldest line first.  A malformed or partial line is treated
-- as end-of-stream on a singleton, or skipped if more lines follow — the
-- cursor should have trimmed trailing partials before streaming.
instance Uncons Jsonl (Stamped Text) where
  uncons (Jsonl []) = That (Jsonl [])
  uncons (Jsonl [line]) =
    case parseLine line of
      Just p -> This p
      Nothing -> That (Jsonl [])
  uncons (Jsonl (line : rest)) =
    case parseLine line of
      Just p -> These p (Jsonl rest)
      Nothing -> uncons (Jsonl rest)
  nil = Jsonl []

-- | Prepend is the dual view: a newest-first stream over the same image.
instance Cons Jsonl (Stamped Text) where
  cons p (Jsonl xs) = Jsonl (frameStored p : xs)
  consNil = Jsonl []

-- | Current UTC time as an ISO-8601 string.
formatNow :: IO Text
formatNow = T.pack . formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" <$> getCurrentTime

-- | Parse an ISO-8601 string to UTCTime, accepting the format we write.
parseTimeText :: Text -> Maybe UTCTime
parseTimeText = parseTimeM True defaultTimeLocale "%Y-%m-%dT%H:%M:%S" . T.unpack

-- | Encode a 'Stamped Text' as a single canonical JSON Lines object.
frameStored :: Stamped Text -> Text
frameStored (Stamped ts i (Post from' to' thread' body')) =
  decodeUtf8 $
    encodeJson $
      JObject
        [ ("id", JNumber (fromIntegral i)),
          ("ts", JString (T.pack (formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" ts))),
          ("from", JString from'),
          ("to", JArray (V.fromList (map JString to'))),
          ("thread", JArray (V.fromList (map (JNumber . fromIntegral) thread'))),
          ("body", JString body')
        ]

-- | Encode a bare 'Post Text' as a single JSON Lines object (the protocol
-- format sent to the stamping bus daemon).
framePost :: Post Text -> Text
framePost p =
  decodeUtf8 $
    encodeJson $
      JObject
        [ ("from", JString (from p)),
          ("to", JArray (V.fromList (map JString (to p)))),
          ("thread", JArray (V.fromList (map (JNumber . fromIntegral) (thread p)))),
          ("body", JString (body p))
        ]

-- | Parse a canonical stamped storage line.  Returns 'Nothing' if the line is
-- not valid JSON with the expected fields.
parseLine :: Text -> Maybe (Stamped Text)
parseLine line =
  case decodeJson (encodeUtf8 line) of
    Right (JObject o) -> do
      pid <- lookupNumber "id" (JObject o) >>= naturalFromScientific
      JString tsStr <- lookup "ts" o
      ts <- parseTimeText tsStr
      JString from' <- lookup "from" o
      to' <- lookupStrings "to" (JObject o)
      thread' <- lookupPostIds "thread" (JObject o)
      JString body' <- lookup "body" o
      pure (Stamped ts pid (Post from' to' thread' body'))
    _ -> Nothing

-- | Parse a bare 'Post Text' line (no stamp).
parsePost :: Text -> Maybe (Post Text)
parsePost line =
  case decodeJson (encodeUtf8 line) of
    Right (JObject o) -> do
      JString from' <- lookup "from" o
      to' <- lookupStrings "to" (JObject o)
      thread' <- lookupPostIds "thread" (JObject o)
      JString body' <- lookup "body" o
      pure (Post from' to' thread' body')
    _ -> Nothing

-- | Like 'parseLine', but also accepts the legacy flat triple and bracket
-- formats, assigning the supplied line index as the id.
parseLineAt :: Int -> Text -> Maybe (Stamped Text)
parseLineAt idx line =
  parseLine line
    <|> parseLegacyTriple idx line
    <|> parseLegacyBracket idx line

-- | Parse a raw log line into @(from, body)@, accepting the stamped format
-- and both legacy formats.
parseMessage :: Text -> Maybe (Text, Text)
parseMessage line = do
  Stamped{stamped = p} <- parseLineAt 0 line
  pure (from p, body p)

-- | Extract just the timestamp from a raw log line.
parseMessageTs :: Text -> Maybe Text
parseMessageTs line = do
  Stamped{timeStamp = ts} <- parseLineAt 0 line
  pure (T.pack (formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" ts))

-- | Render a 'Stamped Text' for human display as @[id@ts] from: body@.
renderStored :: Stamped Text -> Text
renderStored (Stamped ts i (Post from' _to' _thread' body')) =
  T.concat ["[", T.pack (show i), "@", T.pack (formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" ts), "] ", from', ": ", body']

-- | Render a raw log line for human display.
renderMessage :: Text -> Maybe Text
renderMessage line = renderStored <$> parseLineAt 0 line

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

lookupString :: Text -> Json -> Maybe Text
lookupString k (JObject o) = case lookup k o of
  Just (JString s) -> Just s
  _ -> Nothing
lookupString _ _ = Nothing

lookupStrings :: Text -> Json -> Maybe [Text]
lookupStrings k (JObject o) = case lookup k o of
  Just (JArray vs) -> Just [s | JString s <- V.toList vs]
  _ -> Nothing

lookupPostIds :: Text -> Json -> Maybe [PostId]
lookupPostIds k (JObject o) = case lookup k o of
  Just (JArray vs) -> Just [i | JNumber s <- V.toList vs, Just i <- [naturalFromScientific s]]
  _ -> Nothing

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
      pure (Stamped ts (fromIntegral idx) (Post sender' [] [] body'))
    _ -> Nothing

-- | Legacy bracket format: @[timestamp] sender: body@.
parseLegacyBracket :: Int -> Text -> Maybe (Stamped Text)
parseLegacyBracket idx line =
  case T.breakOnEnd "]" line of
    (pref, rest)
      | not (T.null pref)
      , let tsStr = T.dropWhile (== '[') (T.init pref) -> do
          ts <- parseTimeText tsStr
          let (sender', body') = T.breakOn ":" (T.strip rest)
          guard (not (T.null sender'))
          pure (Stamped ts (fromIntegral idx) (Post (T.strip sender') [] [] (T.strip (T.drop 1 body'))))
    _ -> Nothing
