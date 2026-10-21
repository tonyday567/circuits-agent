# circuits-agent

> Moore agents on a shared, addressed log; opaque shards for effects.

Design card: `coffee/loom/agent.md`.

```haskell
type Agent arr s a b = Step (,) (,) s s arr (Either Void a) (b, ())
type Shard m a b     = Poles () (K m) a b        -- effectful ends
```

- Pure agents: `Agent (->) s a b`; common addressed-log case
  `Agent (->) [Post a] (Post a) [Post a]`.
- Effectful agents: `Agent (K m) s a b` — the same coalgebra, each step in `m`.
- Shard: commit `a`, emit `b`. Common log case `Shard m [Post a] [Post a]`;
  a single post commits as a one-element list.
- Opacity: commit/emit only; no interior.

## What is here

- `Circuit.Agent` — `Post`, `Log`, `Agent`, `Inbox`, `AgentState`, `Shard`,
  `watch`, `post`, `turn`, `hasPending`, `loop`, `meetingLoop`, `tape`,
  `selfrec`, `shard`, plus shard combinators `prefixShard`, `suffixShard`,
  `codecShard`, `composeShard`.
- Agent as Shard — `AgentSeat`, `feedAgent`, `agentShard`, `runAgentShard`
  (change of base: pure Moore to `K m` ends).
- Token seat — `Port`, `batchEnds` / `unbatchEnds` / `portShard`; queue ends
  (`Queue`, `ChannelPolicy`, `openSTM`, `openIO`).
- `Circuit.Agent.StdPorts` — child-process ports: stdin/stdout/stderr as
  blocking frame poles; a dead child delivers its exit as one terminal
  `Exited` frame; `NoncePorts` split streams on an in-band `⟜<n>` stamp for
  children that cannot carry ids (ghci).
- `Circuit.Agent.Turn` — turn runners: thread-correlated `turn` /
  `turnTimeout`, nonce-correlated `noncePipeline` (pipelining-safe).
- `Circuit.Agent.Framing` — `Stamped` posts, JSONL log framing, cursors.
- `Circuit.Agent.Mark` — the boundary-mark grammar: 🟡 ✓ ↩ 🔴 🟢 🔵 ⌛.
- `Circuit.Agent.Query` — generic query-to-shard adapters (`queryShard`,
  `replyPosts`, `sessionPrompt`); `echoShard` is the exact mock.
- `Circuit.Agent.Graph` — wiring graphs (`runGraph`): bus/star/chain topologies.
- `Circuit.Agent.Delivery` — addressed-delivery relations (FinRel matrices).
- `Circuit.Agent.Machina.Mark` — `spinMark` / `markLoop`: halt decided by
  content, never inferred from quiet.
- `Cursor` — in-memory cursor polling.

## What is not here

Operational seats, bus plumbing, CLI adapters → `free-agent`.

## Status

Experimental. Symmetric shard pin 2026-07-27; asymmetric `[Post]/Post` and
`Post`/`[Post]` pins withdrawn.
