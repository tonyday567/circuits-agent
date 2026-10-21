# Revision history for circuits-agent

## unreleased

- **Conversation honesty (S-b).** Nonce correlation for children that
  cannot stamp ids (ghci): a nonce echo (`⟜<n>`, no trailing newline)
  after each command, streams split on the nonce family (`NoncePorts`),
  zero-frame (`Unterminated` / empty payload) and two-frame (multi-frame
  payload) both visible in-band. Merged stdio behind
  `procMergeStderr`: one pipe for both streams, so diagnostics are
  kernel-ordered against the dialogue. The Turn pending cap is lifted —
  `TurnState` holds every pending command, responses route by id, the
  runners stash wire responses for the turn they belong to, and
  `noncePipeline` pipelines safely (children execute stdin in order).
  Pinned by the S4/T1 oracles in `circuits-agent-axioma`.
- **Death honesty (S-a).** Process reads now end by content: the pumper
  collects the child's exit code and sinks exactly one terminal `Exited`
  frame after the flushed payloads, so a blocked read on a dead child
  returns instead of hanging (`Frame a = Payload a | Exited ExitCode` on
  the read poles). `stdClose` terminates, waits, and reaps (no zombies;
  `stdProcess` exposes the handle); a setup exception after the spawn
  terminates and reaps the child (no orphans). The doubles model reality —
  `echo` blocks instead of throwing, `scriptedDouble` scripts block /
  die / zero frames / two frames, `unbatchEnds` blocks on a quiet stream
  instead of returning `undefined`. Shipped mark grammars have no
  proper-prefix collisions (chunking invariance needs none). Pinned by the
  S1-S6 oracles in `circuits-agent-axioma`.
- **M3: `run1` steps once; the monologue is honest.** `run1` no longer
  steps the coalgebra twice per input: the output it reports is the output
  the step produced (verified trace of the old shape:
  `run1 (selfrec sum) [] 1 == (2, [1, 1])` — a phantom second step). The
  observation point moved into `cellToAgent` (post-step state) and
  `routeAgent` routes output in the step that produced it, replacing three
  sites that each compensated for the double step. `selfrec` now emits the
  utterance it records, so output equals the recorded head. Query shards
  stay id-blind by protocol — the ancestry law lives at the runner layer.
  Pinned by the M1b/M3 oracles in `circuits-agent-axioma`.
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
