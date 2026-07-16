# jadx Control-Flow Deflatten (`deflatten`)

A [jadx](https://github.com/skylot/jadx) plugin that **undoes control-flow flattening** of the
`while (true) switch (str.hashCode() ^ K)` form used by several Android string/control-flow
obfuscators (e.g. the Enigma runtime helper seen in the wild), rebuilding the method's original
control-flow graph.

Flattening replaces a method's real control flow with a dispatcher loop: a `String` *state*
variable is fed through `state.hashCode()` folded with a chain of constants, and a big `switch`
routes each state to a case block that does a little work and then assigns the *next* state. Because
every state string is a compile-time constant, the executed sequence of case blocks is fully
static, so it can be statically devirtualized. This plugin computes `hashCode(state) ^ K` for each
state, follows the `state = …` transitions to reconstruct the real CFG, and collapses the
dispatcher, leaving ordinary control flow for jadx to structure normally.

It is **sound by construction**: a dispatcher is only rewritten when *every* state string resolves
to a compile-time constant that routes to a concrete (non-default) switch case, and the whole plan
is validated before any mutation — so an unrecognised shape bails cleanly and the method is left
untouched. Enabling it on an unrelated app is safe (it just no-ops on non-dispatcher code).

---

## Install

```bash
# Recommended (when listed on the marketplace):
jadx plugins --install deflatten

# From a GitHub release jar:
jadx plugins --install-jar jadx-deflatten-<version>.jar

# Directly from this repo:
jadx plugins --install github:Arsylk:jadx-deflatten

jadx plugins --list
```

In jadx-gui the plugin appears under **Preferences → Plugins → Control-Flow Deflatten**.

## What it handles

- **Linear dispatchers** — a chain of relay states ending in a terminal (`return`) case.
- **Loop-carried values** — accumulators and object handles (e.g. a `Pattern`/`StringBuilder`
  built across states) are threaded to the concrete value each state sees.
- **Conditional transitions** — `state = cond ? "X" : "Y"` becomes a real `if` with two direct
  edges.
- **Reconvergence & loops** — two states advancing to a common third, or a loop-header state
  reached from both an initialiser and a back-edge, are reconstructed as real merges / loops by
  inserting a merge phi (per loop-carried variable) at each shared target.
- **Nested dispatchers** — removed one per fixpoint round, so inner dispatchers are handled in a
  later pass.

The real dispatcher shape produced by production obfuscators (a *two-phi* dispatcher: a header phi
plus a back-edge merge phi with a "state unchanged" default self-loop) is detected and torn down.

## How it works

The plugin adds two `JadxDecompilePass`es on the block/SSA IR:

1. **DeflattenUnlock** (`after BlockProcessor`, `before BlockFinisher`) sets
   `AFlag.DISABLE_BLOCKS_LOCK` on methods that have both a `SWITCH` and a `String.hashCode()` call,
   so their basic-block graph stays mutable for the rewrite (jadx normally locks pred/succ lists
   into immutable collections). Ordinary methods keep the default locked CFG and are unaffected.
2. **Deflatten** (`after ReplaceNewArray`, `before RegionMakerVisitor`) detects a dispatcher,
   statically evaluates the selector for each state (`SelectorEval`), rebuilds the state graph, and
   rewires every transition edge directly to the case block that selector routes to — inserting
   merge phis for loop-carried variables at reconvergence / loop headers. The dispatcher header,
   selector, `hashCode` calls and the constant chain then fall out as dead code.

## Settings

| Option | Default | Description |
|---|---|---|
| `deflatten.enabled` | `true` | Master switch for the pass. |
| `deflatten.comments` | `true` | Add a `Control-flow deflattened: N dispatcher(s)` info comment to rewritten methods. |

## Build

```bash
# Standalone (this repo):
mv settings.gradle.kts.disabled settings.gradle.kts   # only needed outside the jadx tree
./gradlew jar          # -> build/libs/jadx-deflatten-<version>.jar
./gradlew test         # golden tests: fixtures are compiled + decompiled through jadx
```

The plugin compiles against `io.github.skylot:jadx-core` (provided by the host jadx at runtime);
it is never bundled. Keep the `version` in `build.gradle.kts`, `DeflattenPlugin.VERSION`, and the
release tag in sync.

## License

Apache License 2.0 — see [LICENSE](LICENSE).
