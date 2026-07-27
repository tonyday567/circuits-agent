# Revision history for circuits-agent

## unreleased

- Retired `Circuit.Agent.Comm` (cat-FIFO channel); product bus lives in muster.
- `ProcessSeat`: dual `Ends` sharing stdin (`psOut` / `psErr`); `stderrEnds`.

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
