# circuits-agent

> Moore agents on a shared, addressed log; opaque shards for effects.

Design card: `coffee/loom/agent.md`.

```haskell
type Agent s   = System s (Mono [Post] Post)            -- pure Moore agent
type Shard m   = Ends (Kleisli m) [Post] [Post]         -- effectful ends (lists both ways)
type LogEnds m = Shard m                                -- same shape; dual seat on the log
```

- Pure agents: free carrier `s`; common case `Agent [Post]` (received stream).
- Shard: commit `[Post]`, emit `[Post]`. One-post keyboard: `prefixIn (:[])`.
- Opacity: commit/emit only; no interior.

## What is here

- `Circuit.Agent` — `Post`, `Log`, `Agent`, `Inbox`, `AgentState`, `Shard`, `LogEnds`,
  `watch`, `post`, `turn`, `hasPending`, `loop`, `session`, `tape`, `selfrec`,
  `shard`, `logEnds`, `prefixIn`, plus shard combinators `prefixShard`, `suffixShard`,
  `codecShard`, `composeShard`, `>:>`.
- Agent as Shard — `AgentSeat`, `feedAgent`, `agentShard`, `runAgentShard`
  (change of base: pure Moore → `Ends (Kleisli m) [Post] [Post]`).
- Token seat — `Port`, `batchEnds` / `unbatchEnds` / `portShard` (parser
  stream coalgebra around a list shard → `Ends Post Post`); queue ends
  re-exported (`Queue`, `openSTM`, `openIO`).
- Process / Framing / Turn — process dual seats (`ProcessSeat`: shared `In`,
  stdout + stderr `Ends`); framing; turn runners.

## What is not here

Live LLM as `Shard IO`, STM logs, timing → `circuits-agent-observe`.

## Status

Experimental. Symmetric shard pin 2026-07-27; asymmetric `[Post]/Post` and
`Post`/`[Post]` pins withdrawn.
