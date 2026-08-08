{-# LANGUAGE OverloadedStrings #-}

-- | The halt-mark grammar as a type.
--
-- Marks are the bus's boundary vocabulary: a finite set of glyphs that
-- prefix a post body and announce the post's role in an exchange. This is
-- the level-0 grammar of the quiescence thread — the free boundary
-- @K + payload@ with @K@ finite, the stateless 'isMark' of the mark
-- machine (@spinMark@). Anything stateful (round counters, roles) lives
-- above this layer.
--
-- The glyphs:
--
--   * 🟡 'Motion' — a claim: "I pick this up".
--   * ✓ 'Consent' — no objection.
--   * ↩ 'Amendment' — an amendment offered.
--   * 🔴 'Escalate' — "I can't move this"; the human's door.
--   * 🟢 'Landed' — halt: the claim landed.
--   * 🔵 'StandDown' — halt: standing down. Also the quiescence mark:
--     a runner that judges observed quiet posts this to convert its
--     judgment into decided quiet for everyone downstream.
--
-- History note: the quiescence marker was previously posted under 🟡,
-- colliding with 'Motion'. Legacy bodies like @"🟡 quiescent after N
-- empty cycles"@ parse as 'Motion' under this grammar — that ambiguity is
-- exactly why quiescence moved to 🔵. Do not reintroduce it.
--
-- Design card: @coffee\/loom\/board.md@ ("what the halt-mark grammar is").
module Circuit.Agent.Mark
  ( Mark (..),
    markGlyph,
    parseMark,
    markOf,
    isHalt,
    isEscalate,
  )
where

import Circuit.Agent (Post (..))
import Data.Text (Text)
import Data.Text qualified as T

-- | A boundary mark.
data Mark
  = -- | 🟡 claim: "I pick this up".
    Motion
  | -- | ✓ no objection.
    Consent
  | -- | ↩ amendment offered.
    Amendment
  | -- | 🔴 escalation: "I can't move this".
    Escalate
  | -- | 🟢 halt: landed.
    Landed
  | -- | 🔵 halt: standing down / quiescent.
    StandDown
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The glyph that renders a mark.
markGlyph :: Mark -> Text
markGlyph = \case
  Motion -> "\x1F7E1" -- 🟡
  Consent -> "\x2713" -- ✓
  Amendment -> "\x21A9" -- ↩
  Escalate -> "\x1F534" -- 🔴
  Landed -> "\x1F7E2" -- 🟢
  StandDown -> "\x1F535" -- 🔵

-- | Parse a mark from the start of a body. Tolerates the emoji variation
-- selector (U+FE0F) between glyph and rest. Exact glyphs only — no fuzzy
-- matching, so a body that merely talks about marks is not one.
parseMark :: Text -> Maybe Mark
parseMark t = go [minBound .. maxBound]
  where
    go [] = Nothing
    go (m : ms)
      | glyph `T.isPrefixOf` t = Just m
      | (glyph <> "\xFE0F") `T.isPrefixOf` t = Just m
      | otherwise = go ms
      where
        glyph = markGlyph m

-- | The mark carried by a post's body, if any.
markOf :: Post Text -> Maybe Mark
markOf = parseMark . body

-- | Halt marks: the exchange is over. 'Landed' and 'StandDown'.
isHalt :: Mark -> Bool
isHalt = \case
  Landed -> True
  StandDown -> True
  _ -> False

-- | Escalation: leave the loop, wake the human.
isEscalate :: Mark -> Bool
isEscalate = (== Escalate)
