# circuits-agent

> Moore agents on a shared, addressed log; opaque shards for effects.

Design card: `coffee/loom/agent.md`.

```haskell
type Agent arr s a b = System arr s (Mono a b)          -- Moore agent, polymorphic arrow
type Shard m a b     = Ends (Kleisli m) a b             -- effectful ends
type LogEnds m a b   = Shard m a b                      -- same shape; dual seat on the log
```

- Pure agents: `Agent (->) s a b`; common addressed-log case `Agent (->) [Post] Post [Post]`.
- Effectful agents: `Agent (Kleisli m) s a b`.
- Shard: commit `a`, emit `b`. Common log case `Shard m [Post] [Post]`; one-post keyboard: `prefixIn (:[])`.
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
- `Circuit.Agent.Cli` — live CLI agents as `Shard IO [Post] [Post]`: the
  invocation recipe is data (`Cli`), session ids are scraped and resumed
  with stale fallback, prompts travel via argv/stdin (no shell quoting,
  multi-line bodies survive); `hermesCli`, `kimiCli`, `grokCli` presets;
  `echoShard` is the exact mock oracle.

## What is not here

HTTP API hosts, STM logs, timing → `circuits-agent-observe`.

## Status

Experimental. Symmetric shard pin 2026-07-27; asymmetric `[Post]/Post` and
`Post`/`[Post]` pins withdrawn.
