# Getting ethlambda's state transition into Lean

This crate is a working demonstration. It holds the state transition function
from `crates/blockchain/state_transition`, and running the Rust → Lean
toolchain on it produces a Lean project that typechecks: all twelve functions
translated, no `sorry`.

It is not a fork and not a reimplementation. Eight of the twelve functions are
unchanged apart from comments; the other four were rewritten, and this document
says exactly what each one needed and why.

It also carries theorems, because a translation that typechecks is only half
the question — the other half is whether you can prove anything on the output.
They are not a coverage claim against any catalog. What they do cover is the
property your own regression test asserts by example after the devnet freeze at
slot 27984.

Every number here came from a run.

## Which version this is against

`lambdaclass/ethlambda`, MIT. The file was copied on 28 Oct 2026 from
`crates/blockchain/state_transition/src/lib.rs`, at `35c074b` *(feat: add
Beacon Chain support, #661, 2026-10-20)* — the commit that last touched it, not
whatever `main` happened to be.

Checked again on 6 Nov 2026: the file on `main` is byte-identical to the one at
`35c074b`. We compared contents rather than tracking commits, since contents
are what the numbers depend on. The same check, so you need not take our word:

```bash
P=crates/blockchain/state_transition/src/lib.rs
curl -sS https://raw.githubusercontent.com/lambdaclass/ethlambda/35c074b/$P | sha256sum
curl -sS https://raw.githubusercontent.com/lambdaclass/ethlambda/main/$P | sha256sum
```

If those hashes differ, every figure below is stale and the diff has to be
redone.

Toolchain: `cargo-hax 0.4.2`, `charon nightly-2026.09.02`,
`aeneas build-183e4f0`, and `elan` for Lean. We ran on x86-64 Linux; the
toolchain does not support Intel macOS, so we used a `linux/amd64` container.

## Diff it yourself

The crate is at `tooling/hax-lean/mini-stf/` in
[`EdVeralli/eth-crypto-study`](https://github.com/EdVeralli/eth-crypto-study).
Compare `src/stf.rs` against your `lib.rs`:

```bash
diff -u ethlambda/crates/blockchain/state_transition/src/lib.rs \
        mini-stf/src/stf.rs
```

Four kinds of difference come out of it:

1. the `use` block — our types come from this crate instead of yours;
2. nineteen helper functions, new and ours, which the rewritten functions call;
3. the four functions in the table under **What changed in your code**;
4. two tests of ours appended to your test module, which lives in this file.

Comments differ throughout, so to check the "eight of twelve unchanged" claim
specifically, strip comments and blank lines first:

```bash
plain() { sed 's://.*::' "$1" | grep -v '^[[:space:]]*$'; }
diff -u <(plain ethlambda/.../lib.rs) <(plain mini-stf/src/stf.rs)
```

That is a blunt instrument — it would also cut a `//` inside a string literal,
though there are none in either file. It is for reading, not for CI.

## Run it

One command, from the crate root:

```bash
bash regenerar.sh
```

It does three things in order, and **the middle one is not optional**:

1. extract — `cargo hax into lean`, with the two flags below;
2. restore the hand-written Lean;
3. `lake build`.

Step 2 exists because `proofs/` is generated output and is not in version
control, while the Lean we wrote by hand is. On a fresh checkout hax seeds
`Assumptions/` from its own templates — skeletons, not our models of
`HashMap::get`, `U64::isqrt`, `mem::take` and the rest — so extraction followed
straight by `lake build` fails with unknown identifiers. The same happens after
any failed extraction, which clears those files. The three copies that matter
are tracked:

```
supuestos/TypesExternal.lean    →  proofs/lean/MiniStf/Assumptions/
supuestos/FunsExternal.lean     →  proofs/lean/MiniStf/Assumptions/
teoremas/ProofObligations.lean  →  proofs/lean/MiniStf/Verification/
```

By hand, the same three steps are:

```bash
cargo hax into lean \
  --charon-args="--opaque '{impl core::fmt::Debug for _}' \
                 --opaque '{impl core::fmt::Display for _}'"
cp supuestos/TypesExternal.lean supuestos/FunsExternal.lean \
   proofs/lean/MiniStf/Assumptions/
cp teoremas/ProofObligations.lean proofs/lean/MiniStf/Verification/
cd proofs/lean && lake build
```

Both `--opaque` are required: without them every `#[derive(Debug)]` fails with
`[Error] Unreachable`, and dropping the derive is not a way out because
`.expect()` needs it. The first `lake build` also compiles Aeneas, `CoreModels`
and the hax tactic library, which takes a while; later ones do not.

A successful run ends in `Build completed successfully (1742 jobs)`, with no
`sorry` and the twelve functions present as `def`s in
`proofs/lean/MiniStf/Extraction/Funs.lean`.

The tests — your six plus two of ours:

```bash
cargo test
```

Eight pass.

## What the crate contains

Everything, with line counts as shipped.

| File | Lines | Origin |
|---|---|---|
| `src/stf.rs` | 1484 | **yours** — `state_transition/src/lib.rs`: eight of twelve functions unchanged, four rewritten, nineteen helpers of ours, and your 437-line test module with two tests appended. |
| `src/justified_slots_ops.rs` | 90 | **yours** — unchanged except the `use` lines. |
| `src/tipos.rs` | 431 | **your type definitions**, serialization derives removed, plus our stand-in `hash_tree_root`. |
| `src/ssz.rs` | 154 | ours — stand-ins for `SszList` and `SszBitlist`. |
| `src/mapa.rs` | 245 | ours — an association list replacing one `HashMap`. |
| `src/stubs.rs` | 49 | ours — no-op `tracing` and metrics. |
| `src/lib.rs` | 51 | ours — module wiring. |
| `Cargo.toml` | 10 | ours. |
| `regenerar.sh` | 36 | ours — extract, restore, build. |
| `supuestos/TypesExternal.lean` | 49 | **ours, required** — models of `HashMap` and `RandomState`. |
| `supuestos/FunsExternal.lean` | 309 | **ours, required** — models of the `core`/`std` operations `CoreModels` does not cover, plus seventeen `fmt` signatures corrected by hand. |
| `supuestos/RevisarAxiomas.lean` | 25 | ours — prints the trust base of each theorem. |
| `teoremas/ProofObligations.lean` | 686 | ours — the theorems. |
| `axiomas.txt` | 56 | ours — the `#print axioms` output, so the trust base can be read without building. |
| `README.md` | 602 | ours — the working log: every obstacle in the order we hit it. |

The two files marked **required** are not optional extras; see **Run it**.

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

Plus nineteen helper functions of ours, 179 lines in all.

### The rules behind each change

None of these is in the hax manual. Each one cost a run to find.

**Iterator closures do not translate.** Anything with `.iter().map()`,
`.filter()`, `.any()`, `.find()`, `.enumerate()` or `.retain()` becomes an
index loop. `.find()` is the worst of them: it fails *inside `core`*, with a
lifetime error that aborts the whole extraction and writes no files at all.

**`return` inside a `for` is not supported.** `process_attestations` had two
literal `return Err(...)` inside its loop, plus the `?` on `is_valid_vote`,
which propagates the same way. Turning them into `break` is not enough either:
a loop with four exits — the normal end plus three breaks — fails with "Could
not match the contexts". The loop now has a single exit and carries the error in
a flag.

**A loop inside another loop does not translate**, but the same loop moved into
its own function does. That is why there are so many small helpers.

**A loop that mutates one collection cannot bind a reference taken from
another.** Either alone is fine; together they produce "Internal error". That is
why every read goes through a helper that returns a copy.

**`HashMap` cannot be iterated.** `justifications` is read with `.retain()`,
`.keys()` and indexing, and a `HashMap` has no order to index by, so it became
an association list (`src/mapa.rs`). `root_to_slot` is still a `HashMap`: it is
built with up to `HISTORICAL_ROOTS_LIMIT` entries and only ever queried with
`get`, never iterated.

**`std::iter::repeat_n` and `Vec::extend` have no model**, which accounts for
the small change in `process_block_header`.

### A bug the rewrite introduced, and how we found it

Your six tests pass before and after every change above. That is the evidence we
have, and it is weaker than it looks.

`process_attestations` has three error exits inside its loop: the `?` on
`is_valid_vote`, `EmptyAggregationBits`, and `AggregationBitsOutOfBounds`.
Because Aeneas rejects early returns inside loops, ours collects the error in a
flag — and the first version of that rewrite set the flag and never read it. It
returned `Ok(())` on a block your code rejects, and it called
`serialize_justifications`, which your code never reaches when it cuts. Two
divergences.

All six of your tests passed anyway. The two that check errors
(`rejects_justification_votes_length_mismatch`,
`rejects_empty_validator_registry`) cover the exits **before** the loop; none
cover the three inside it. So we added two that do:

| Test | What it forces |
|---|---|
| `process_attestations_rejects_empty_aggregation_bits` | the valid vote from your regression test, with no bit set → `EmptyAggregationBits` |
| `process_attestations_rejects_an_out_of_range_bit` | bits of length 6 with index 5 set over 4 validators → `AggregationBitsOutOfBounds { index: 5, validator_count: 4 }` |

Both were checked against the defect: with the fix removed, your six pass and
these two fail.

## What you get

`teoremas/ProofObligations.lean` holds seven named results:

| Result | What it is |
|---|---|
| `pronic_iff_cuadrado` | the identity your own comment asserts |
| `chequeo_de_paridad_redundante` | its corollary: the parity check beside it can never fail |
| `try_finalize_no_retrocede` | finality does not roll back |
| `try_finalize_no_toca_justified` | `try_finalize` leaves `latest_justified` alone |
| `ST3.process_attestations_loop_no_retrocede` | justification does not roll back, over one turn of the loop |
| `ST3.process_attestations_no_retrocede` | the same, over the whole function |
| `bind_da_ok` | a tool: opens one `RustM` bind |

They were not picked for count. Between them they cover arithmetic, branching
and record updates, induction over a loop, and composition across a whole
function with early exits and a `match`.

### The arithmetic

Your comment in `slot_is_justifiable_after` asserts an identity:

```rust
// Mathematical insight: For pronic delta = n(n+1), we have:
//   4*delta + 1 = 4n(n+1) + 1 = (2n+1)^2
```

It is now a theorem, resting on Lean's three standard axioms and nothing else:

```lean
theorem pronic_iff_cuadrado (n : ℕ) :
    (∃ m, m * m = 4 * n + 1) ↔ (∃ k, n = k * (k + 1))
```

Writing it surfaced something small: the parity check beside it (`m % 2 == 1`)
**can never fail**, because `4·delta + 1` is always odd and so is its root. Not
a bug, but a condition that does nothing.

### Finality does not roll back

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

A companion result goes with it, and the other half needs it:

```lean
theorem try_finalize_no_toca_justified
    ... :
    stf.try_finalize state source target j rts = ok (state', j') →
    state'.latest_justified = state.latest_justified
```

`try_finalize` is called from inside the loop that moves `latest_justified`, so
proving that field never regresses there requires knowing this one leaves it
alone.

### Justification does not roll back

`latest_justified` moves inside the loop, so this one needed induction over the
loop. It is proved not only about the loop but about the function you call:

```lean
theorem ST3.process_attestations_no_retrocede
    (state state' : tipos.State) (atts : ...) (res : ...) :
    stf.process_attestations state atts = ok (res, state') →
    state.latest_justified.slot ≤ state'.latest_justified.slot
```

Note the hypothesis: these statements are conditional on the call returning
`ok`. They say nothing about inputs on which the transition fails — and that is
the right shape rather than a weakened one, because a failed transition rejects
the block and leaves no new state to say anything about.

This is the property your own test asserts by example, in
`latest_justified_does_not_regress_within_block`. Its comment says why it
exists: on devnet at slot 27984 a block carried three supermajority
attestations targeting slots 27978, 27981 and 27974 in that order, the
unconditional assignment kept the last, and the chain froze. The test covers
that scenario; the theorem covers every input the transition accepts.

### What this is against the catalog, stated exactly

`ST-3` in
[`NyxFoundation/formal-leanSpec`](https://github.com/NyxFoundation/formal-leanSpec)
is stated over `State.transition` — the whole one-block transition — and bounds
both checkpoint slots at once. What is proved here is each of its two halves
over the component where that field actually moves: justification over
`process_attestations`, finality over `try_finalize`. **That is not the catalog
proposition, and we are not claiming it is.**

Lifting both to `state_transition` is the step that would make it one, and it
needs three lemmas we have not written: that `process_slots` leaves the
checkpoints alone, that `process_block_header` does not lower them, and the
finality half carried up through the attestation loop. One caveat is already
visible in the catalog and worth passing on: the first block's genesis anchoring
force-assigns slot-0 checkpoints, which makes the bare statement **false** for
adversarial states, and the formalization carries an extra `AnchorWF` hypothesis
for exactly that. A lift that ignores it will not close.

Neither half was chosen because it looked provable. `ST-3` is one of thirty-five
propositions in that catalog — seven about the state transition, the rest about
fork choice, SSZ, the validator, networking, storage and sync. The statement
predates our work on it, which matters: picking your own properties makes the
exercise circular.

### The trust base

`#print axioms` on each result, with the output in `axiomas.txt`:

| Result | Total | Lean's | Native | Declarations |
|---|---|---|---|---|
| the two arithmetic ones | 3 | 3 | — | — |
| `bind_da_ok` | 1 | 1 | — | — |
| the two `try_finalize` ones | 13 | 3 | 3 | 7 |
| the loop theorem | 14 | 3 | 4 | 7 |
| `process_attestations` | 20 | 3 | 7 | 10 |

Three categories, with three different weights.

**Lean's three** — `propext`, `Classical.choice`, `Quot.sound` — underpin any
classical proof and say nothing about this code.

**The native ones** are `_native.decide.ax_*`: facts the Lean kernel did not
check, computed by the compiler instead. Seven distinct ones appear across the
build. They are not ours and not yours. Defining a function in Lean can require
proofs — a scalar literal carries a proof that it fits its type, indexing
carries a proof that the index is in range — and Aeneas generates those
obligations as it translates, then discharges the bound-related ones with
`native_decide`. Its tactic library is where that choice is made
(`Tactic/Simproc/BvSimprocs.lean`, `Tactic/Step/StepArraySpec.lean`), and no
flag turns it off. The names are prefixed with *your* functions because that is
where each appeared, not because anyone put it there.

They arrive with the **translated definitions**, before any theorem exists:

```
#print axioms mini_stf.stf.try_finalize   -- a `def`, no theorem involved
```

returns the same thirteen axioms as our `try_finalize` theorem, item for item.
Translate the STF with this toolchain and prove nothing at all, and you already
have them; proving on top of the output does not widen the trust base by one
entry. What we did not do is open each of the seven to name the fact it stands
for.

**The declarations** are ours, in `supuestos/FunsExternal.lean`: twenty-eight
axioms that are signatures and no more — `HashMap`'s `get`, `insert` and `new`,
the `Borrow` and `BuildHasher` trait types, the `cmp` and `hash` of `[T; N]`,
`mem::take`, `bool::then`, and seventeen `Debug::fmt` stubs. They exist so the
generated Lean compiles: `try_finalize` calls `root_to_slot.get(…)`, Aeneas
names `HashMap::get` in the output, `CoreModels` has no model for it, and
without the declaration the module dies with `Unknown identifier` and nothing
builds.

That is a milder gap than the native axioms. An axiom that states nothing yields
nothing — you cannot derive a falsehood from it because you cannot derive
anything. What it costs is reach: any property depending on how the map behaves
is out of bounds. Models *with* content would buy those properties at the price
of asserting things that could be wrong, and we declined that trade.

The one real assertion we make is `U64::isqrt`, modeled as `Nat.sqrt`. Both are
the floor of the square root, so we believe it, but it is our claim and not
something the toolchain checked. `HashMap` also gets a representation in
`TypesExternal.lean` — a list of pairs — but `get` and `insert` stay opaque over
it, so no behaviour is asserted there.

None of the twenty-eight carries weight in the theorems above: the properties
come from the guards and the assignments, not from anything the map, the hash or
the formatter does. That is a claim about the proofs, read off them. `#print
axioms` tells you what a theorem depends on, not whether it leans on that
dependency's behaviour, and that distinction is ours to argue rather than the
tool's to measure.

## Proving on the output

These theorems were not written by hand against raw equations. There is a
proving workflow for hax-generated Lean, it lands in your `.lake` as soon as you
build, and most of what we needed came from it —
[hax.cryspen.com/manual/lean/](https://hax.cryspen.com/manual/lean/). What each
piece did here:

| Piece | From | What it did |
|---|---|---|
| `hax_mvcgen` | hax | the workhorse. Splits a program into verification conditions — over 250 for the attestation loop — and steps through every call that has a `@[spec]` lemma. |
| Hoare triples and `@[spec]` lemmas | hax, over `Std.Do` | the idiom: one lemma per function, and the tactic names the one that is missing. |
| `Aeneas.Std.loop_spec` | **Aeneas, not hax** | loop induction. This is the one to use. |
| `Hax.loop_range_spec_unsigned` | hax | tried, rejected — below. |
| `--charon-args="--start-from f"` | hax | tried, rejected — see **Folding this into your tree**. |
| `triple_mayThrow_of`, `of_triple_mayThrow` | ours | bridges between an equation and a Hoare triple. |
| `bind_da_ok` | ours | opens one `RustM` bind, for proofs done equationally. |

**Prefer Aeneas's loop lemma over hax's.** `Hax.loop_range_spec_unsigned` states
its step obligation with `⇓`, which demands the body **never fail**. On
`process_attestations` that turns "the justified slot does not go backwards"
into a far larger theorem: absence of panic in all twelve functions the body
calls, six of which contain loops of their own. `Aeneas.Std.loop_spec` takes a
full postcondition, with failure and divergence branches; choosing
`PostCond.mayThrow` discharges those for free, makes the
`attestations_processed + 1` overflow irrelevant, and — because divergence is
tolerated — removes the need for a termination measure. That is where the
conditional-on-success shape of the statements comes from.

**Two bridges, and they are the reusable part.**

```lean
triple_mayThrow_of : (∀ v, x = ok v → P v) → ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄
of_triple_mayThrow : ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄ → x = ok v → P v
```

`triple_mayThrow_of` is the dual of `bind_da_ok`: it turns a theorem you already
have **as an equation** into the `@[spec]` lemma the tactic consumes, so a result
proved the hard way stays usable without being redone. The other direction
brings a triple back to an equation, which is how the statements above are
phrased. Twenty-three `@[spec]` lemmas feed the two loop-related proofs; all but
two have a trivially true postcondition, present only so the tactic can step
over a call that cannot move `latest_justified`.

**`hax_mvcgen` stops silently.** It decides whether work remains from the
*shape* of the goal: `goalNeedsMvcgen` recognizes a `Triple`, an `entails`
carrying a `wp`, or a `.down` carrying a `PredTrans.apply`. A `.down` carrying a
bare `WP.wp` matches none of the three, so the tactic treats the goal as a
finished verification condition and reports success — leaving the whole function
body wrapped in one `wp`. It does not report a missing spec, because it never
tried. If a goal comes back with a `wp` in it, the next move is yours.

Two smaller traps of the same kind. `core.option.Option.is_none` needs its own
`@[spec]` lemma — it is `let b ← is_some self; ok (b = false)`, and without the
lemma the tactic cannot get past it; the attestation loop chains four. And the
iterator spec is stated for the literal form `{ start := i, «end» := e }`, so a
`Range` arriving as a variable has to be destructured first or `mvcgen` will not
take the first step.

**A dead axiom can shadow a real definition, and nothing warns you.**
`Assumptions/FunsExternal.lean` still declared `axiom stf.process_attestations`
and `axiom stf.serialize_justifications` from when both were `--opaque`, with
their old signatures. They did not clash with the generated definitions, because
that file declares `stf.foo` while the generated code declares `mini_stf.stf.foo`
— two different names — and under `open mini_stf` the ambiguous `stf.foo`
resolves to the axiom. A theorem written that way compiles, proves nothing, and
looks right; only `#print axioms` reveals it. Both axioms are now gone, and
neither appears in the trust base of any result above.

The hazard is structural rather than careless: hax seeds that file once and never
revisits it, so dropping an `--opaque` leaves its axiom behind. When you remove
an `--opaque`, remove its axiom too.

## What it costs you

**One complexity regression.** Lookup in `justifications` goes from constant to
linear. In practice that map holds the roots awaiting finalization, which is
small — but the type allows up to `HISTORICAL_ROOTS_LIMIT` entries, so with
finalization stalled for a long time it is a real regression.

**Less idiomatic code.** A `for` with indices where there was
`.iter().filter().count()` is uglier and easier to misread. That is a
maintenance cost, and it is the price of the exercise.

## Folding this into your tree

The crate works as delivered: clone it, run `bash regenerar.sh`, and the STF is
in Lean. Nothing in it is pending on our side.

Whether to fold it into `ethlambda` is a decision on yours, and there are two
things in the way. Neither is code; both are packaging.

**The dependency closure has to be free of `dyn`.** `state_transition` depends
on `ethlambda-storage`, and a single `dyn Error` in that dependency aborts the
extraction: 413 errors, zero files written. Charon compiles the crate *and all
its dependencies*, but Aeneas emits definitions only for the local crate, so you
inherit a dependency's failures without inheriting its definitions.

**The types have to live in the crate being extracted.** That is the same
asymmetry seen from the other side, and it is why `src/tipos.rs` is a copy of
your definitions rather than a `use`. We checked whether the toolchain offers a
way around the copy, on a small crate that did nothing but touch `State` and
`Block` from `ethlambda-types`. hax's manual documents
`--charon-args="--start-from <function>"`, which extracts a function *"along
with all its dependencies"* — and that holds for the call graph, not for types.
The function came out translated, the type did not, and
`TypesExternal_Template.lean` came out empty, so the toolchain does not even ask
for the type as an external one. The dangling name surfaces at `lake build`, not
at extraction. `--start-from` changes which items Charon emits, not which crate
Aeneas defines, so the copy is not a shortcut we took: it is the only route the
toolchain leaves.

The cost of the copy is drift. If `State` changes, someone has to sync
`src/tipos.rs`. Both problems disappear together if the types and the STF end up
in one crate, which is also what would make the verified code *be* the
production code.

## Honest limits

**The hash is not SSZ.** `hash_tree_root` here is a polynomial hash written in
the translatable subset. It gives different roots for different states, which is
all the STF asks of it, but it is not interoperable. On the Lean side the right
treatment is to declare it opaque and carry injectivity as an explicit
hypothesis.

**`source.slot + 1` can overflow.** Stating the `try_finalize` theorem as a
Hoare triple rather than an equation surfaced this: with `source.slot =
u64::MAX`, the increment feeding `slot_is_justifiable_after` panics in a debug
build. The equational form hides it, because it assumes the call returned `ok`.
No slot will realistically get there, and the guard above requires
`source.slot > state.latest_finalized.slot`, so it is not a live bug — but it is
an unstated precondition, and you may prefer `checked_add` or a saturating form.

**The trust base is not empty**, and what is in it is set out under **The trust
base** above: seven native axioms that come with the translation, twenty-eight
declarations of ours that assert nothing, and one modeling claim we do make.
