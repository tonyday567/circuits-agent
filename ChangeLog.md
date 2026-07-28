# Revision history for circuits-agent

## unreleased

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
  - `type Agent s = System s (Mono Post Post)` — free carrier; turn uses `Agent [Post]`
  - `type Shard m = Ends (Kleisli m) [Post] [Post]` — symmetric lists both ways
  - `type LogEnds m = Shard m` — same shape; dual seat
  - one-post reality via `prefixIn (:[])` (re-exported)
  - **removed** `Final`; withdrawn asymmetric `Shard`/`LogEnds` pins
  - `shard` / `logEnds` via `endsK`
- Pure core: `Post`, `Log`, `watch`, `post`, `turn`, `hasPending`, `loop`, `session`, `tape`, `selfrec`.
- `loop` v0: round-robin until quiescence (no pending deliveries).
- Verify: pretense, delivery, compaction invariance, turn integrity, loop quiescence.
- Absorbed process-port / framing / turn layer from circuits-repl.
