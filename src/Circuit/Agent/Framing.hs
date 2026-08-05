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
-- @{"ts":..., "sender":..., "body":...}@ and the bracket format
-- @[timestamp] sender: body@ so existing log files remain readable.  Those
-- legacy lines are assigned the supplied line index as their id and empty
-- @to@/@thread@ lists.
module Circuit.Agent.Framing
  ( -- * Types
    PostId,
    Stamped (..),
    StoredPost,
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
import Data.Time (defaultTimeLocale, formatTime, getCurrentTime)
import Data.Vector qualified as V
import Numeric.Natural (Natural)
import Prelude

-- | Storage boundary wrapper: an absolute id and a timestamp assigned by the
-- single writer when the value is appended to the log.
data Stamped a = Stamped
  { stampId :: PostId,
    stampTs :: Text,
    stamped :: a
  }
  deriving (Show, Eq, Functor)

-- | A timestamped text post as it appears in the log.
type StoredPost = Stamped (Post Text)

-- | The file image: a stream of raw JSONL lines, oldest first.
newtype Jsonl = Jsonl { unJsonl :: [Text] }
  deriving (Show, Eq)

-- | Append is the natural file operation: a new line at the end.
instance Snoc Jsonl StoredPost where
  snoc (Jsonl xs) p = Jsonl (xs ++ [frameStored p])
  snocNil = Jsonl []

-- | Read peels the oldest line first.  A malformed or partial line is treated
-- as end-of-stream on a singleton, or skipped if more lines follow — the
-- cursor should have trimmed trailing partials before streaming.
instance Uncons Jsonl StoredPost where
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
instance Cons Jsonl StoredPost where
  cons p (Jsonl xs) = Jsonl (frameStored p : xs)
  consNil = Jsonl []

-- | Current UTC timestamp as an ISO-8601 string without brackets.
formatNow :: IO Text
formatNow = T.pack . formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S" <$> getCurrentTime

-- | Encode a 'StoredPost' as a single canonical JSON Lines object.
frameStored :: StoredPost -> Text
frameStored (Stamped i ts p) =
  decodeUtf8 $
    encodeJson $
      JObject
        [ ("id", JNumber (fromIntegral i)),
          ("ts", JString ts),
          ("from", JString (from p)),
          ("to", JArray (V.fromList (map JString (to p)))),
          ("thread", JArray (V.fromList (map (JNumber . fromIntegral) (thread p)))),
          ("body", JString (body p))
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
parseLine :: Text -> Maybe StoredPost
parseLine line =
  case decodeJson (encodeUtf8 line) of
    Right (JObject o) -> do
      pid <- lookupNumber "id" o >>= naturalFromScientific
      JString ts <- lookup "ts" o
      JString from' <- lookup "from" o
      to' <- lookupStrings "to" o
      thread' <- lookupPostIds "thread" o
      JString body' <- lookup "body" o
      pure (Stamped pid ts (Post from' to' thread' body'))
    _ -> Nothing

-- | Parse a bare 'Post Text' line (no stamp).
parsePost :: Text -> Maybe (Post Text)
parsePost line =
  case decodeJson (encodeUtf8 line) of
    Right (JObject o) -> do
      JString from' <- lookup "from" o
      to' <- lookupStrings "to" o
      thread' <- lookupPostIds "thread" o
      JString body' <- lookup "body" o
      pure (Post from' to' thread' body')
    _ -> Nothing

-- | Like 'parseLine', but also accepts the legacy flat triple and bracket
-- formats, assigning the supplied line index as the id.
parseLineAt :: Int -> Text -> Maybe StoredPost
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
parseMessageTs line = stampTs <$> parseLineAt 0 line

-- | Render a 'StoredPost' for human display as @[id@ts] from: body@.
renderStored :: StoredPost -> Text
renderStored (Stamped i ts p) =
  T.concat ["[", T.pack (show i), "@", ts, "] ", from p, ": ", body p]

-- | Render a raw log line for human display.
--
--   * stamped format -> @[id@ts] from: body@
--   * legacy triple or bracket -> @[ts] sender: body@
--   * unparseable -> returned unchanged
renderMessage :: Text -> Text
renderMessage line =
  case parseLine line of
    Just stored -> renderStored stored
    Nothing ->
      case parseLegacyTriple 0 line <|> parseLegacyBracket 0 line of
        Just (Stamped _ ts p) ->
          T.concat ["[", ts, "] ", from p, ": ", body p]
        Nothing -> line

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

lookupNumber :: Text -> [(Text, Json)] -> Maybe Scientific
lookupNumber k o = case lookup k o of
  Just (JNumber n) -> Just n
  _ -> Nothing

lookupStrings :: Text -> [(Text, Json)] -> Maybe [Text]
lookupStrings k o = case lookup k o of
  Just (JArray a) -> traverse jstring (V.toList a)
  _ -> Nothing
  where
    jstring (JString s) = Just s
    jstring _ = Nothing

-- | Decode a JSON array of non-negative integers into 'PostId's.
-- Legacy lines that carry a string array or no array fall back to @[]@.
lookupPostIds :: Text -> [(Text, Json)] -> Maybe [PostId]
lookupPostIds k o = case lookup k o of
  Just (JArray a) -> traverse toPostId (V.toList a)
  _ -> Just []
  where
    toPostId (JNumber n) = naturalFromScientific n
    toPostId _ = Nothing

naturalFromScientific :: Scientific -> Maybe Natural
naturalFromScientific n
  | c < 0 = Nothing
  | e < 0 = Nothing
  | otherwise = Just (fromInteger (c * 10 ^ e))
  where
    c = coefficient n
    e = base10Exponent n

parseLegacyTriple :: Int -> Text -> Maybe StoredPost
parseLegacyTriple idx line =
  case decodeJson (encodeUtf8 line) of
    Right (JObject o) -> do
      JString ts <- lookup "ts" o
      JString sender <- lookup "sender" o
      JString body' <- lookup "body" o
      pure (Stamped (fromIntegral idx) ts (Post sender [] [] body'))
    _ -> Nothing

parseLegacyBracket :: Int -> Text -> Maybe StoredPost
parseLegacyBracket idx line = do
  guard ("[" `T.isPrefixOf` line)
  rest1 <- T.stripPrefix "[" line
  let (tsPart, rest2) = T.break (== ']') rest1
  guard (not $ T.null tsPart)
  rest3 <- T.stripPrefix "]" rest2
  rest4 <- case T.uncons rest3 of
    Just (' ', r) -> Just r
    _ -> Nothing
  let (sender, rest5) = T.break (== ':') rest4
  guard (not $ T.null sender)
  body' <- case T.stripPrefix ": " rest5 of
    Just b -> pure b
    Nothing -> pure (T.drop 1 rest5) -- tolerate no space after colon
  pure (Stamped (fromIntegral idx) tsPart (Post sender [] [] body'))
