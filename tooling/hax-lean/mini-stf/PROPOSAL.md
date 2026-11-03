# Getting ethlambda's state transition into Lean

This crate is a working demonstration: it contains ethlambda's lean state
transition function, and running the Rust → Lean toolchain on it produces a
Lean project that typechecks, with all twelve functions translated and no
`sorry`.

It is not a fork and not a rewrite. **Eight of the twelve functions are
byte-identical to yours.** The rest of this document says exactly what the
other four needed, why, and what it costs.

Everything here was measured by running the toolchain, not inferred from
documentation. Where a claim has a number, the number came from a run.

## Which version this is against

`lambdaclass/ethlambda`, MIT. The files were copied on 28 Oct 2026, and the
baseline is pinned to the commit that last touched each of them, not to
whatever `main` happens to be:

| File | Last changed by | Date |
|---|---|---|
| `state_transition/src/lib.rs` | `35c074b` *(feat: add Beacon Chain support, #661)* | 2026-10-20 |

Verified unchanged through `6168a0e` (2026-11-03), which is where the line
counts below were measured. The repository moves — there are commits from
2 and 3 Nov — but not in this file.

To re-check before acting on any number here:

```bash
git log --oneline -1 -- crates/blockchain/state_transition/src/lib.rs
```

If that is no longer `35c074b`, the diff below is stale and has to be redone.

Toolchain: `cargo-hax 0.4.2`, `charon nightly-2026.09.02`, `aeneas build-183e4f0`.

## Run it

```bash
cargo hax into lean \
  --charon-args="--opaque '{impl core::fmt::Debug for _}' \
                 --opaque '{impl core::fmt::Display for _}'"
cd proofs/lean && lake build
```

And the tests — yours, unchanged except for the `use` lines:

```bash
cargo test
```

Six pass.

## What is yours and what is ours

| File | Origin |
|---|---|
| `src/stf.rs` | **yours** — `state_transition/src/lib.rs`, 8 of 12 functions untouched |
| `src/justified_slots_ops.rs` | **yours** — unchanged except the `use` lines |
| the test module at the end of `stf.rs` | **yours** — unchanged except the `use` lines |
| `src/tipos.rs` | **your type definitions**, with the serialization derives removed |
| `src/ssz.rs` | ours — stand-ins for `SszList` and `SszBitlist` |
| `src/mapa.rs` | ours — an association list replacing one `HashMap` |
| `src/stubs.rs` | ours — no-op `tracing` and metrics |

## What changed in your code

Measured against `35c074b`, ignoring comments:

| Function | Changed |
|---|---|
| `state_transition` | — |
| `process_slots` | — |
| `process_block` | — |
| `is_valid_vote` | — |
| `attestation_data_matches_chain` | — |
| `slot_is_justifiable_after` | — |
| `is_proposer` | — |
| `current_proposer` | — |
| `process_block_header` | 3 lines |
| `try_finalize` | ~18 lines |
| `serialize_justifications` | ~23 lines |
| `process_attestations` | ~87 lines |

Plus nineteen new helper functions, which are ours.

Your six tests pass before and after every one of these changes. That is not a
proof of equivalence, but it is the evidence we have, and it is yours.

### The rules behind each change

None of these are in any documentation. Each one cost a run to find.

**Iterator closures don't translate.** Anything with `.iter().map()`,
`.filter()`, `.any()`, `.find()`, `.enumerate()`, `.retain()` becomes an index
loop. `.find()` is worse than the others: it fails *inside `core`*, with a
lifetime error that aborts the whole extraction and writes no files at all.

**`return` inside a `for` is not supported.** There were exactly two, in
`process_attestations`. Turning them into `break` is not enough either: a loop
with four exits (the normal end plus three breaks) fails with "Could not match
the contexts". The loop now has a single exit and uses a flag.

**A loop inside another loop does not translate**, but the same loop moved into
its own function does. That is why there are so many small helpers.

**A loop that mutates one collection cannot bind a reference taken from
another.** Either alone is fine; together they produce "Internal error". That is
why every read goes through a helper that returns a copy.

**`HashMap` cannot be iterated.** `justifications` is read with `.retain()`,
`.keys()` and indexing, and a `HashMap` has no order to index by. It became an
association list (`src/mapa.rs`). `root_to_slot` is still a `HashMap`: it is
built with up to `HISTORICAL_ROOTS_LIMIT` entries and only ever queried with
`get`, never iterated.

**`std::iter::repeat_n` and `Vec::extend` have no model**, which is the three-line
change in `process_block_header`.

## What it costs you

**One complexity regression.** Lookup in `justifications` goes from constant to
linear. In practice that map holds the roots awaiting finalization, which is
small — but the type allows up to `HISTORICAL_ROOTS_LIMIT` entries, so with
finalization stalled for a long time this is a real regression. We are naming
it rather than letting you find it.

**Less idiomatic code.** A `for` with indices where there was
`.iter().filter().count()` is uglier and easier to get wrong when reading. That
is a maintenance cost, and it is the honest price of the whole exercise.

## Folding this into your tree

This crate works as delivered: clone it, run the three commands, and you have
the STF in Lean. Nothing here is pending on our side.

What is a decision on yours is whether to fold it into `ethlambda` itself, and
there is exactly one thing in the way. It is not code:

`state_transition` depends on `ethlambda-storage`, and a single `dyn Error` in
that dependency aborts the extraction — 413 errors, zero files written. Charon
compiles the crate *and all its dependencies*, but Aeneas only emits
definitions for the local crate, so you inherit a dependency's failures without
inheriting its definitions. The lean STF has to sit in a crate whose dependency
closure is free of `dyn`.

The same mechanism is why `src/tipos.rs` exists. For `State` and `Block` to
exist on the Lean side they must live in the crate being extracted; otherwise
the generated Lean names them and never defines them, and the project does not
typecheck. We verified that separately, with a four-function crate that did
nothing but touch `State` and `Block`: the extraction ran clean and
`Types.lean` came out with an empty namespace.

Both are packaging, not behaviour — moving files between crates, with the code
unchanged. How you want to do that in your layout is yours to decide, and it is
the one thing we could not do from outside your repo.

## What you get

The first theorem is already proved, in `teoremas/ProofObligations.lean`. Your
comment in `slot_is_justifiable_after` asserts an identity:

```rust
// Mathematical insight: For pronic delta = n(n+1), we have:
//   4*delta + 1 = 4n(n+1) + 1 = (2n+1)^2
```

That is now a theorem, depending only on Lean's three standard axioms:

```lean
theorem pronic_iff_cuadrado (n : ℕ) :
    (∃ m, m * m = 4 * n + 1) ↔ (∃ k, n = k * (k + 1))
```

Writing it also surfaced something: the parity check beside it (`m % 2 == 1`)
**can never fail**. `4·delta + 1` is always odd, so its root is too. Not a bug,
but a condition that does nothing.

The target beyond that is `ST-3` from
[`NyxFoundation/formal-leanSpec`](https://github.com/NyxFoundation/formal-leanSpec) —
*`latest_justified.slot` and `latest_finalized.slot` never go backwards*. Two
things make it the right one: the statement is not ours, and your own suite
already asserts it by example, in
`latest_justified_does_not_regress_within_block`. The theorem would make it
universal.

## Honest limits

**The hash is not SSZ.** `hash_tree_root` here is a polynomial hash written in
the translatable subset. It gives different roots for different states, which
is all the STF asks of it, but it is not interoperable. On the Lean side the
right treatment is to declare it opaque and carry injectivity as an explicit
hypothesis.

**Nine native axioms, and nobody chose them.** The trust base of the generated
definitions includes nine `_native.decide.ax_*` axioms — facts the Lean kernel
did not check, computed by the compiler instead. They do not come from your
code or ours: they come from Aeneas's own tactic library
(`Tactic/Simproc/BvSimprocs.lean`, `Tactic/Step/StepArraySpec.lean`), discharging
array and scalar bounds. There is no flag to turn them off. Any theorem about
these functions inherits them, so the honest phrasing is "proved, modulo nine
arithmetic facts the kernel did not verify". This is worth reporting upstream.

**The vendored types drift.** `src/tipos.rs` is a copy of your definitions. If
`State` changes, someone has to sync it. The way out is the architectural ask
above: types and STF in one crate, so the verified code *is* the production
code.
