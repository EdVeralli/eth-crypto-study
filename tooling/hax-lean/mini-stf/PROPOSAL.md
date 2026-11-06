# Getting ethlambda's state transition into Lean

This crate is a working demonstration: it contains ethlambda's lean state
transition function, and running the Rust → Lean toolchain on it produces a
Lean project that typechecks, with all twelve functions translated and no
`sorry`.

It is not a fork and not a rewrite. **Eight of the twelve functions are
byte-identical to yours.** The rest of this document says exactly what the
other four needed, why, and what it costs.

The theorems in it are there for the second half of that claim: that what comes
out the other end is **usable**, not a dead artifact. They are not a coverage
claim against any catalog. What they do cover is the property your own
regression test asserts by example after the devnet freeze at slot 27984 —
proved for every input, on the function where it froze.

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

### Where it is, and how to diff it

The crate lives at `tooling/hax-lean/mini-stf/` in
[`EdVeralli/eth-crypto-study`](https://github.com/EdVeralli/eth-crypto-study).
The file to compare is `src/stf.rs`; yours is
`crates/blockchain/state_transition/src/lib.rs` at `35c074b`.

```bash
diff -u ethlambda/crates/blockchain/state_transition/src/lib.rs \
        mini-stf/src/stf.rs
```

Three kinds of difference come out of that, and only the third is behavioural:

1. the `use` block — our types come from this crate instead of yours;
2. nineteen helper functions that are new and ours;
3. the four functions in the table below.

Comments differ too, ours included, since each change carries a note saying why
it is there. So to check the "eight of twelve unchanged" claim specifically,
strip comments and blank lines first — crudely, but enough to eyeball:

```bash
plain() { sed 's://.*::' "$1" | grep -v '^[[:space:]]*$'; }
diff -u <(plain ethlambda/.../lib.rs) <(plain mini-stf/src/stf.rs)
```

That is a blunt instrument — it would also cut a `//` inside a string literal,
though there are none in either file. It is for reading, not for CI.

Please do this before trusting any number here. Every figure in this document
came from a run, but a diff you performed yourself is worth more than a figure
we are asserting.

## Run it

You need `cargo-hax 0.4.2`, `charon nightly-2026.09.02`,
`aeneas build-183e4f0` and `elan`. We ran everything on x86-64 Linux; on Intel
macOS the toolchain is unsupported, so we used a `linux/amd64` container.

One command, from the crate root:

```bash
bash regenerar.sh
```

It does three things in order, and **the middle one is not optional**:

1. extract — `cargo hax into lean` with the two flags below;
2. **restore the hand-written Lean**;
3. `lake build`.

Step 2 is there because `proofs/` is generated output and is not in version
control, while the Lean we wrote by hand is. On a fresh checkout hax seeds
`Assumptions/` from its own templates — skeletons, not our models of
`HashMap::get`, `U64::isqrt`, `mem::take` and the rest — so a bare
`cargo hax into lean && lake build` **fails** with unknown identifiers. The same
thing happens after any failed extraction, which clears those files. The copies
that matter are tracked:

```
supuestos/TypesExternal.lean    →  proofs/lean/MiniStf/Assumptions/
supuestos/FunsExternal.lean     →  proofs/lean/MiniStf/Assumptions/
teoremas/ProofObligations.lean  →  proofs/lean/MiniStf/Verification/
```

The extraction itself, if you want to run it by hand:

```bash
cargo hax into lean \
  --charon-args="--opaque '{impl core::fmt::Debug for _}' \
                 --opaque '{impl core::fmt::Display for _}'"
cd proofs/lean && lake build
```

Both `--opaque` are required. Without them every `#[derive(Debug)]` fails with
`[Error] Unreachable`, and removing the derive is not a way out: `.expect()`
needs it. The first `lake build` also compiles Aeneas, `CoreModels` and the hax
tactic library, which takes a while; later ones do not.

What a successful run looks like: `Build completed successfully (1742 jobs)`,
no `sorry`, and the twelve functions present as `def`s in
`proofs/lean/MiniStf/Extraction/Funs.lean`.

And the tests — your six, unchanged except for the `use` lines, plus two we
added:

```bash
cargo test
```

Eight pass.

## What is yours and what is ours

Everything in the crate, nothing held back. Line counts are the files as
shipped.

| File | Lines | Origin |
|---|---|---|
| `src/stf.rs` | 1484 | **yours** — `state_transition/src/lib.rs`. Eight of twelve functions unchanged, four rewritten, nineteen helpers of ours, and your 437-line test module with two tests added. |
| `src/justified_slots_ops.rs` | 90 | **yours** — unchanged except the `use` lines. |
| `src/tipos.rs` | 431 | **your type definitions**, with the serialization derives removed, plus our stand-in `hash_tree_root`. |
| `src/ssz.rs` | 154 | ours — stand-ins for `SszList` and `SszBitlist`. |
| `src/mapa.rs` | 245 | ours — an association list replacing one `HashMap`. |
| `src/stubs.rs` | 49 | ours — no-op `tracing` and metrics. |
| `src/lib.rs` | 51 | ours — module wiring. |
| `Cargo.toml` | 10 | ours. |
| `regenerar.sh` | 36 | ours — extract, restore, build. |
| `supuestos/TypesExternal.lean` | 49 | **ours, and required** — models of `HashMap` and `RandomState`. |
| `supuestos/FunsExternal.lean` | 309 | **ours, and required** — models of the `core`/`std` operations `CoreModels` does not cover, plus seventeen `fmt` signatures corrected by hand. |
| `supuestos/RevisarAxiomas.lean` | 25 | ours — prints the trust base of each theorem. |
| `teoremas/ProofObligations.lean` | 686 | ours — the theorems. |
| `axiomas.txt` | 56 | ours — the raw `#print axioms` output, so the trust base can be read without building. |
| `README.md` | 602 | ours — the working log: every obstacle in the order we hit it, including the ones that turned out to be our own mistakes. |

The two Lean files marked **required** are not optional extras: `proofs/` is
generated and not in version control, so without them a fresh extraction does
not build. See **Run it**.

## What changed in your code

Counted on the twelve functions with comments and blank lines removed;
*removed* and *added* come from a per-function unified diff against `35c074b`.

| Function | Yours | Ours | Removed | Added |
|---|---|---|---|---|
| `state_transition` | 13 | 13 | — | — |
| `process_slots` | 16 | 16 | — | — |
| `process_block` | 6 | 6 | — | — |
| `is_valid_vote` | 28 | 28 | — | — |
| `attestation_data_matches_chain` | 23 | 23 | — | — |
| `slot_is_justifiable_after` | 11 | 11 | — | — |
| `is_proposer` | 3 | 3 | — | — |
| `current_proposer` | 3 | 3 | — | — |
| `process_block_header` | 68 | 70 | 1 | 3 |
| `try_finalize` | 43 | 48 | 15 | 20 |
| `serialize_justifications` | 28 | 20 | 16 | 8 |
| `process_attestations` | 110 | 96 | 79 | 65 |
| **total** | **352** | **337** | **111** | **96** |

Plus nineteen helper functions that are ours, 179 lines in all.

Your six tests pass before and after every one of these changes. That is the
evidence we have, and it is yours — but it is weaker than it looks, and we found
out the hard way.

`process_attestations` has three error exits inside its loop: the `?` on
`is_valid_vote`, `EmptyAggregationBits`, and `AggregationBitsOutOfBounds`. Aeneas
rejects early returns inside loops, so ours collects the error in a flag. The
first version of that rewrite **set the flag and never read it**: it returned
`Ok(())` on a block your code rejects, and it called `serialize_justifications`,
which your code never reaches when it cuts. Two divergences.

All six of your tests passed anyway. The two that check errors
(`rejects_justification_votes_length_mismatch`,
`rejects_empty_validator_registry`) cover the exits **before** the loop; none
cover the three inside it. So we added two tests that do:

| Test | What it forces |
|---|---|
| `process_attestations_rejects_empty_aggregation_bits` | the valid vote from your regression test, with no bit set → `EmptyAggregationBits` |
| `process_attestations_rejects_an_out_of_range_bit` | bits of length 6 with index 5 set over 4 validators → `AggregationBitsOutOfBounds { index: 5, validator_count: 4 }` |

Both were verified against the bug: with the fix removed, your six pass and these
two fail. A test that does not fail when the defect is present proves nothing.

The lesson generalizes past this crate. Where a rewrite replaces control flow
with data flow — a `return` with a flag — the tests that would catch a mistake
are exactly the ones a suite built around the original control flow tends not to
have.

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

Four theorems, in `teoremas/ProofObligations.lean`. They were not picked for
count — each one demonstrates a different thing the generated Lean supports:

| Theorem | What it demonstrates |
|---|---|
| the pronic identity | reasoning about the protocol's arithmetic |
| `try_finalize` (two) | branches, record updates, functions that pass through `HashMap` axioms |
| the attestation loop | **induction over a loop** — the part everyone assumes is out of reach on generated code |
| `process_attestations` | composition: a whole function, with early exits and a `match` |

The first one is the smallest. Your
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

### Finality does not roll back, on `try_finalize`

`ST-3` from
[`NyxFoundation/formal-leanSpec`](https://github.com/NyxFoundation/formal-leanSpec)
says *`latest_justified.slot` and `latest_finalized.slot` never go backwards*.
The finality half of it is now proved about your `try_finalize`:

```lean
theorem try_finalize_no_retrocede
    (state state' : tipos.State) (source target : tipos.Checkpoint) ... :
    stf.try_finalize state source target j rts = ok (state', j') →
    state.latest_finalized.slot ≤ state'.latest_finalized.slot
```

The proof is short because your guard is the property:

```rust
if source.slot <= state.latest_finalized.slot { return; }
...
state.latest_finalized = source;
```

Its trust base is twelve axioms: Lean's three, three type declarations that
only exist so signatures typecheck, three `std` operations with no model
(`HashMap::get` and the `Hash` of `[T; N]`), one formatting stub — and **three
of the native axioms described below**. None of the opaque declarations are
load-bearing here; the property comes from the guard, not from anything the
map or the hash does.

A companion theorem is proved alongside it, and the other half needs it:

```lean
theorem try_finalize_no_toca_justified
    (state state' : tipos.State) (source target : tipos.Checkpoint) ... :
    stf.try_finalize state source target j rts = ok (state', j') →
    state'.latest_justified = state.latest_justified
```

`try_finalize` is called from inside the loop that moves `latest_justified`, so
proving that field never regresses there requires knowing this one leaves it
alone.

### Justification does not roll back, on `process_attestations`

`latest_justified` moves inside the loop, so this one needed induction over the
loop. It is proved, and not only about the loop — about the function you call:

```lean
theorem ST3.process_attestations_no_retrocede
    (state state' : tipos.State) (atts : ...) (res : ...) :
    stf.process_attestations state atts = ok (res, state') →
    state.latest_justified.slot ≤ state'.latest_justified.slot
```

**What this is, stated exactly.** `ST-3` in
[`NyxFoundation/formal-leanSpec`](https://github.com/NyxFoundation/formal-leanSpec)
is stated over `State.transition` — the whole one-block transition — and bounds
both checkpoint slots at once. What is proved here is each of its two halves
over the component where that field actually moves: justification over
`process_attestations`, finality over `try_finalize`. That is not the catalog
proposition, and we are not claiming it is.

Lifting both to `state_transition` is the remaining step, and it is mostly
mechanical with the two bridges below: `process_slots` has to leave the
checkpoints alone, `process_block_header` must not lower them, and the finality
half has to come up through the same loop. One caveat is already visible in the
catalog and worth passing on: the first block's genesis anchoring force-assigns
slot-0 checkpoints, which makes the bare statement **false** for adversarial
states — the formalization carries an extra `AnchorWF` hypothesis for exactly
that. A lift that ignores it will not close.

What the two halves do cover is the failure you actually hit. This is the
property your own test asserts by example
(`latest_justified_does_not_regress_within_block`), and its comment says why it
exists: on devnet at slot 27984, a block carried three supermajority
attestations targeting slots 27978, 27981 and 27974 in that order, the
unconditional assignment kept the last one, and the chain froze. The test
covers that scenario. The theorem covers every input.

How it was done — which tactic, which loop lemma, and the two hazards we hit —
is in **Proving on the output** below, because it applies to anything you prove
on this code, not just to this theorem.

The justification theorem's trust base is twenty axioms: Lean's three, six native ones (see below),
`HashMap`'s `get`/`insert`/`new` and the `Hash`/`Ord`/`Borrow` declarations that
only exist so signatures typecheck, and one formatting stub. Neither dead axiom
appears, which is how you can tell the theorem is about the generated code.

### Why this statement and not another

Neither half was chosen because it looked provable. `ST-3` is one of
thirty-five propositions in
[`NyxFoundation/formal-leanSpec`](https://github.com/NyxFoundation/formal-leanSpec)
— seven of which are about the state transition, the rest about fork choice,
SSZ, the validator, networking, storage and sync. The statement predates our
work on it, which matters: picking your own properties makes the exercise
circular.

And it is not academic. Your suite already asserts it by example, in a test
written after the chain froze. The theorem covers the inputs the test does not.

## Proving on the output

These theorems were not written by hand against raw equations. There is a
proving workflow for hax-generated Lean, it lands in your `.lake` as soon as you
build, and most of what we needed came from it — documented at
[hax.cryspen.com/manual/lean/](https://hax.cryspen.com/manual/lean/). What
follows is what each piece did here, because two of the choices are
counter-intuitive and cost a day each.

| Piece | Where from | What it did here |
|---|---|---|
| `hax_mvcgen` | hax | the workhorse. Splits a program into verification conditions — over 250 for the attestation loop — and steps through every call that has a `@[spec]` lemma. |
| Hoare triples and `@[spec]` lemmas | hax, over `Std.Do` | the idiom: one lemma per function, and the tactic names the one that is missing. |
| `Aeneas.Std.loop_spec` | **Aeneas, not hax** | loop induction. This is the one to use. |
| `Hax.loop_range_spec_unsigned` | hax | tried, rejected — below. |
| `--charon-args="--start-from f"` | hax | tried, rejected: it extracts the call graph, not a dependency's type definitions. |
| `triple_mayThrow_of`, `of_triple_mayThrow` | ours | bridges between an equation and a triple. |
| `bind_da_ok` | ours | opens one `RustM` bind, for proofs done equationally. |

**Prefer Aeneas's loop lemma over hax's.** `Hax.loop_range_spec_unsigned` states
its step obligation with `⇓`, which demands the body **never fail**. On
`process_attestations` that turns "the justified slot does not go backwards"
into a far larger theorem: absence of panic in all twelve functions the body
calls, six of which contain loops of their own. `Aeneas.Std.loop_spec` takes a
full postcondition, with failure and divergence branches. Choosing
`PostCond.mayThrow` discharges those for free, makes the
`attestations_processed + 1` overflow irrelevant, and — because divergence is
tolerated — removes the need for a termination measure entirely.

The statement that comes out is conditional on success, and that is the right
shape rather than a weakened one: the property is about a state transition, and
if the transition fails the block is rejected and there is no new state to say
anything about.

**The two bridges are the reusable part.**

```lean
triple_mayThrow_of : (∀ v, x = ok v → P v) → ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄
of_triple_mayThrow : ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄ → x = ok v → P v
```

`triple_mayThrow_of` is the dual of `bind_da_ok`: it turns any theorem you
already have **as an equation** into the `@[spec]` lemma the tactic consumes, so
a result proved the hard way stays usable without being redone. The other
direction brings a triple back to an equation, which is how the final statements
above are phrased. Of the twenty-three `@[spec]` lemmas feeding the two proofs,
all but two are content-free: the invariant concerns `latest_justified`, and
those functions never touch it.

**`hax_mvcgen` stops silently, and that is the trap.** It decides whether more
work remains from the *shape* of the goal: `goalNeedsMvcgen` recognizes a
`Triple`, an `entails` carrying a `wp`, or a `.down` carrying a
`PredTrans.apply`. A `.down` carrying a bare `WP.wp` matches none of the three,
so the tactic treats the goal as a finished verification condition and reports
success — leaving the entire function body wrapped in one `wp`. It does not say
a spec is missing, because it never tried. If a goal comes back with a `wp` in
it, the next call is yours to make, not the tactic's.

**A dead axiom can shadow a real definition, and nothing warns you.**
`Assumptions/FunsExternal.lean` still declared `axiom stf.process_attestations`
and `axiom stf.serialize_justifications` from when both were `--opaque`, with
their old signatures. They did not clash with the generated definitions,
because that file declares `stf.foo` while the generated code declares
`mini_stf.stf.foo` — two different names. Under `open mini_stf`, the ambiguous
`stf.foo` resolves to the axiom. A theorem written that way **compiles, proves
nothing, and looks right**; only `#print axioms` reveals it. Ours were clean and
both axioms are now gone.

The hazard is structural rather than careless: hax seeds that file once and
never revisits it, so dropping an `--opaque` leaves its axiom behind forever.
When you remove an `--opaque`, remove its axiom too, and read `#print axioms` on
anything you prove.

Two concrete gotchas in the same family. `core.option.Option.is_none` needs its
own `@[spec]` lemma — it is `let b ← is_some self; ok (b = false)`, and without
the lemma the tactic cannot get past it; the attestation loop chains four of
them. And the iterator spec is stated for the literal form
`{ start := i, «end» := e }`, so a `Range` arriving as a variable has to be
destructured first or `mvcgen` will not take the first step.

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

We checked whether the toolchain offers a way around the copy, and it does not.
hax's manual documents `--charon-args="--start-from <function>"`, which extracts
a function *"along with all its dependencies"*. That holds for the call graph,
not for types. On a one-function crate that uses `State` from `ethlambda-types`,
the function came out translated and the type did not — and
`TypesExternal_Template.lean` came out empty, so the toolchain does not even ask
for it as an external type. The dangling name surfaces at `lake build`, not at
extraction. Charon compiles the crate and all its dependencies; Aeneas emits
definitions **only for the local crate**, and `--start-from` changes the first
filter, not the second. So the copy is not a shortcut we took: it is the only
route the toolchain leaves.

**`source.slot + 1` can overflow, and it is reachable in principle.** Stating
the `try_finalize` theorem as a Hoare triple rather than an equation surfaced
this: with `source.slot = u64::MAX`, the increment feeding
`slot_is_justifiable_after` panics in a debug build. The equational form hides
it, because it assumes the call returned `ok`. No slot will realistically get
there, and the guard above requires `source.slot > state.latest_finalized.slot`,
so it is not a live bug — but it is an unstated precondition, and you may prefer
a `checked_add` or a saturating form.
