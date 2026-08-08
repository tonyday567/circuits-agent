# Revision history for circuits-agent

## unreleased

- Multi-seat cards: additive `*Subs` API in `Circuit.Agent` — `RosterEntry`,
  `turnAs`, `loopSubs`, `loopWithSubs`, `loopsSubs`, `loopHeteroSubs`,
  `meetingLoopSubs`. Backwards-compatible wrappers keep the old names.
  `meetingPass` now routes by subscription map, so several agents can share a
  card subscription. `Circuit.Agent.Graph.runGraph` uses `loopWithSubs` with
  graph-computed subscriptions; graph oracles were updated to use guarded
  agents that only reply to the original stimulus, since routed replies now
  re-enter the shared channel.
- `Circuit.Agent.Mark`: the halt-mark grammar as a type — `Mark`
  (🟡 `Motion`, ✓ `Consent`, ↩ `Amendment`, 🔴 `Escalate`, 🟢 `Landed`,
  🔵 `StandDown`) with `markGlyph`/`parseMark`/`markOf`/`isHalt`/
  `isEscalate`. The level-0 grammar: finite K, stateless predicate. The
  legacy 🟡-quiescent collision is pinned by oracle (quiescence is 🔵
  `StandDown`); `selfLoopPolicy` in the axioma now parses marks via
  `markOf`.
- Moved population churn (`Circuit.Agent.Population`) to package `agent-evolve`
  (`Agent.Evolve.Population`). Kernel is fixed-roster meetings only.
- Retired `Circuit.Agent.Comm` (cat-FIFO channel); product bus lives in muster.
- `ProcessSeat`: dual `Ends` sharing stdin (`psOut` / `psErr`); `stderrEnds`.
- Stream coalgebra (`These`, `Uncons`, `Snoc`) now imported from `Circuit.Stream`
  (`circuits-parser`); local `peel` and local `Snoc` class removed. API unchanged
  for consumers.
- Generalized `Log` from `[Post]` to `Log f`; delivery (`watch`, `post`, `turn`,
  `loop`, `hasPending`, `session`) now works over any stream with `Cons f Post`
  and `Uncons f Post`.
- Added `emptyLog` as the polymorphic empty `Log f`.

## 0.1.0.0 — 2026-07-27

- Type pin (`coffee/loom/agent.md`):
  - `type Agent s = System s (Mono [Post] Post)` — free carrier; output is a list of posts per input
  - `Inbox` replaces the `Int` cursor; per-agent unread stream with `emptyInbox`, `appendInbox`, `unconsInbox`, `inboxWho`
  - `type Shard m = Ends (Kleisli m) [Post] [Post]` — symmetric lists both ways
  - `type LogEnds m = Shard m` — same shape; dual seat
  - one-post reality via `prefixIn (:[])` (re-exported)
  - **removed** `Final`; withdrawn asymmetric `Shard`/`LogEnds` pins
  - `shard` / `logEnds` via `endsK`
- Pure core: `Post`, `Log`, `watch`, `post`, `turn`, `hasPending`, `loop`, `session`, `tape`, `selfrec`.
- `loop` v0: round-robin until quiescence (no pending deliveries).
- Verify: pretense, delivery, compaction invariance, turn integrity, loop quiescence.
- Absorbed process-port / framing / turn layer from circuits-repl.
