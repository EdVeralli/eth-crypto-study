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
propositions that catalog has about the state transition, which are seven of
thirty-five. Two go end to end and say the most. One: neither checkpoint slot
goes backwards across the transition of a block — the property your own
regression test asserts by example after the devnet freeze at slot 27984. The
other: no checkpoint changes root without moving to a higher slot — which holds
of your code for a different reason than the spec's, and only under a
hypothesis, because on a slot tie your code and the spec choose differently. Of
the other five, one is left at its inductive step and one is not stated because
it is trivial; which is which is spelled out.

Outside the catalog there are four more, about the justified-slots window: the
ones we set ourselves on first reading your code. The last says that when
finality advances and the window shifts, no justified slot is lost. For that
module there is also what the rest lacks: that its functions do not panic or
hang, with the exact condition under which one of them does abort. And a comment
in your code about that window is checked, with the hypothesis it was missing.

Every number here came from a run.

## What this package claims and what it does not

There are two different things here, and they should not be mixed up.

**The translation is complete.** All twelve functions of the STF are in Lean,
and Lean accepts them with no `sorry`. That says the program got written in
Lean. It does not say it is correct.

**The proofs are of specific properties.** A program is not "proved": statements
about it are. There are sixty-nine here, listed under **What you get**. Each
says one precise thing, with its hypotheses in plain sight.

What is **not** proved, said once:

- **That the code never panics.** It is proved for the four functions of one
  helper module, the justified-slots window (`justified_slots_ops.rs`), and for
  ten of the twelve of the transition proper (`stf.rs`), five of them under
  written hypotheses. The other two, `process_block` and `state_transition`,
  keep the "if the function returns" conditional.
- **That the code is equivalent to the spec.** On arbitrary states it is not:
  we found two points where they behave differently, and they are set out
  below.
- **That the properties hold from genesis.** Several are stated as "if it held
  before the block, it holds after", without the initial case.
- **That the Lean is faithful to your Rust.** There are two links. That our four
  rewritten functions do what the originals do is backed by your tests, which
  run on this crate. That the toolchain translates correctly is taken on trust
  from the toolchain.

"No `sorry`" means there is no gap in what is claimed. It does not mean
everything is claimed.

## Which version this is against

`lambdaclass/ethlambda`, MIT. The file was copied on 28 Oct 2026 from
`crates/blockchain/state_transition/src/lib.rs`, at `35c074b` *(feat: add
Beacon Chain support, #661, 2026-10-20)* — the commit that last touched it, not
whatever `main` happened to be.

Checked again on 15 Nov 2026: the file on `main` is byte-identical to the one at
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
4. three tests of ours appended to your test module, which lives in this file.

Comments differ throughout, so to check the "eight of twelve unchanged" claim
specifically, strip comments and blank lines first:

```bash
plain() { sed 's://.*::' "$1" | grep -v '^[[:space:]]*$'; }
diff -u <(plain ethlambda/.../lib.rs) <(plain mini-stf/src/stf.rs)
```

That is a blunt instrument — it would also cut a `//` inside a string literal,
though there are none in either file. It is for reading, not for CI.

## Run it

### From nothing to the theorems

The only things you need installed are **Docker** and `git`. Rust, Lean, hax,
Charon and Aeneas are not installed on your machine: they live inside the
image. The whole sequence, from a terminal:

```bash
# 1. get the repo
git clone https://github.com/EdVeralli/eth-crypto-study.git
cd eth-crypto-study/tooling/hax-lean

# 2. build the image (once; it takes a while and several GB)
docker build --platform linux/amd64 -t hax-lean .

# 3. enter the container, with the crate mounted at /work
docker run --platform linux/amd64 -it \
  -v "$PWD/mini-stf:/work" \
  -v hax-cargo:/root/.cargo/registry \
  -v hax-cache:/root/.cache/hax \
  -v hax-elan:/root/.elan \
  hax-lean bash
```

Inside the container the prompt becomes `root@…` and you are already in
`/work`, which is the crate root:

```bash
# 4. the Rust tests
cargo test

# 5. translate to Lean and build the theorems
bash regenerar.sh 2>&1 | tee /tmp/build.log

# 6. count what came out
grep -c "depends on axioms" /tmp/build.log
grep -c sorryAx /tmp/build.log
```

What each step should give:

| Step | Result |
|---|---|
| 4 | `test result: ok. 9 passed` |
| 5 | `Build completed successfully (1742 jobs).` and then `=== listo ===` (1743 jobs the first time on a clean checkout) |
| 6 | `69` — one axiom block per result — and `0` |

There is no separate "run the proofs" step. The theorems are in
`teoremas/ProofObligations.lean`; step 5 copies that file into the Lean project
and `lake build` checks all of it. If the build ends green, Lean accepted the
sixty-nine proofs. At the end it prints which axioms each one depends on, which
is what step 6 counts.

To convince yourself the check is real, break a statement by hand. In
`proofs/lean/MiniStf/Verification/ProofObligations.lean`, inside
`ST3.state_transition_no_retrocede`, change the `≤` on `latest_justified.slot`
to a `<` and run:

```bash
cd /work/proofs/lean && lake build
```

It fails with `Type mismatch` at that theorem. `bash regenerar.sh` from `/work`
copies the good file back and leaves everything green again.

The rest of this section explains each step and what to do if you already have
the tools installed.

### The environment

The toolchain has no macOS-Intel build, so we ran it in a container. The
`Dockerfile` sits one level up from this crate, at `tooling/hax-lean/`, and it
pins `cargo-hax` to **0.4.2** — the version every number in this document was
measured against.

That pin matters more than it looks: `0.5.0` is already published, so an
unpinned build today would install it and would not reproduce this environment.
Charon's and Aeneas's versions follow from the hax version, which downloads them
itself; Lean's is fixed by each project's `lean-toolchain`, which is in version
control.

```bash
cd tooling/hax-lean
docker build --platform linux/amd64 -t hax-lean .
docker run --platform linux/amd64 -it \
  -v "$PWD/mini-stf:/work" \
  -v hax-cargo:/root/.cargo/registry \
  -v hax-cache:/root/.cache/hax \
  -v hax-elan:/root/.elan \
  hax-lean bash
```

The first build takes a while: it compiles `cargo-hax`, then pre-warms Charon,
Aeneas and the Rust nightly Charon asks for — several GB in all. The named
volumes mean later runs download nothing. If you already have the three tools at
those versions, skip this and go straight to the command below.

### One command

From the crate root:

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

`regenerar.sh` also copies `supuestos/RevisarAxiomas.lean` next to the lakefile.
That one is not part of the build: it is the script that prints the axioms of
each translated function, run by hand with `lake env lean RevisarAxiomas.lean`.

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

A successful run ends in `Build completed successfully`, with no `sorry` and
the twelve functions present as `def`s in
`proofs/lean/MiniStf/Extraction/Funs.lean`. The job count is 1742; the very
first build on a clean checkout reports 1743, one more than every build after
it.

The tests — your six plus three of ours:

```bash
cargo test
```

Nine pass.

## What the crate contains

Everything, with line counts as shipped.

| File | Lines | Origin |
|---|---|---|
| `src/stf.rs` | 1585 | **yours** — `state_transition/src/lib.rs`: eight of twelve functions unchanged, four rewritten, nineteen helpers of ours, and your 437-line test module with three tests appended. |
| `src/justified_slots_ops.rs` | 90 | **yours** — unchanged except the `use` lines. |
| `src/tipos.rs` | 431 | **your type definitions**, serialization derives removed, plus our stand-in `hash_tree_root`. |
| `src/ssz.rs` | 154 | ours — stand-ins for `SszList` and `SszBitlist`. |
| `src/mapa.rs` | 245 | ours — an association list replacing one `HashMap`. |
| `src/stubs.rs` | 49 | ours — no-op `tracing` and metrics. |
| `src/lib.rs` | 51 | ours — module wiring. |
| `Cargo.toml` | 10 | ours. |
| `Cargo.lock` | 65 | ours, and versioned on purpose — it pins the dependency versions, the same concern as the `cargo-hax` pin in the Dockerfile. |
| `regenerar.sh` | 36 | ours — extract, restore, build. |
| `supuestos/TypesExternal.lean` | 49 | **ours, required** — models of `HashMap` and `RandomState`. |
| `supuestos/FunsExternal.lean` | 336 | **ours, required** — models of the `core`/`std` operations `CoreModels` does not cover, plus seventeen `fmt` signatures corrected by hand. |
| `supuestos/RevisarAxiomas.lean` | 25 | ours — prints the axioms each translated function depends on, with no theorem involved. |
| `teoremas/ProofObligations.lean` | 8657 | ours — the theorems. |
| `axiomas.txt` | 748 | ours — the `#print axioms` output, so the trust base can be read without building. |
| `r2.log`, `r3.log`, `r4.log`, `resultado.log` | 16 KB | ours — raw output of the first extraction attempts, kept for the record. The rules they produced are written up in `README.md`. |
| `README.md` | 1227 | ours — the working log: every obstacle in the order we hit it. |
| `PROPOSAL.md` | — | ours — this document. |
| `PROPUESTA.md` | — | ours — the same document in Spanish; the two are kept in step. |

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
(`process_attestations_rejects_justification_votes_length_mismatch`,
`process_attestations_rejects_empty_validator_registry`) cover the exits **before** the loop; none
cover the three inside it. So we added two that do:

| Test | What it forces |
|---|---|
| `process_attestations_rejects_empty_aggregation_bits` | the valid vote from your regression test, with no bit set → `EmptyAggregationBits` |
| `process_attestations_rejects_an_out_of_range_bit` | bits of length 6 with index 5 set over 4 validators → `AggregationBitsOutOfBounds { index: 5, validator_count: 4 }` |

Both were checked against the defect: with the fix removed, your six pass and
these two fail.

The third test of ours is of a different kind: it does not cover our rewrite
but a behaviour of your code. It is under **Checkpoint replacement**, further
down.

## What you get

`teoremas/ProofObligations.lean` holds sixty-nine named results:

| Result | What it is |
|---|---|
| `pronic_iff_cuadrado` | the identity your own comment asserts |
| `chequeo_de_paridad_redundante` | its corollary: the parity check beside it can never fail |
| `try_finalize_no_retrocede` | finality does not roll back |
| `try_finalize_no_toca_justified` | `try_finalize` leaves `latest_justified` alone |
| `ST3.process_attestations_loop_no_retrocede` | justification does not roll back, over the whole attestation loop |
| `ST3.process_attestations_no_retrocede` | the same, over the whole function |
| `ST3F.process_attestations_fin_no_retrocede` | finality does not roll back either, over the whole of `process_attestations` |
| `ST3.process_slots_no_toca_checkpoints` | `process_slots` leaves both checkpoints alone |
| `ST3H.process_block_header_no_mueve_slots` | `process_block_header` keeps both checkpoint slots, genesis anchoring included |
| `ST3T.process_block_no_retrocede` | neither slot rolls back across `process_block` |
| `ST3.state_transition_no_retrocede` | **neither slot rolls back across `state_transition`** — the whole one-block transition |
| `ST7.h256_eq_true` | the translated equality on `H256` is equality |
| `ST7.process_attestations_adelante` | no checkpoint changes root without moving to a higher slot, over the whole of `process_attestations` |
| `ST7.process_block_header_no_toca_checkpoints` | outside genesis anchoring, `process_block_header` leaves both checkpoints whole and only appends to the history |
| `ST7.state_transition_adelante` | **no checkpoint changes root without moving to a higher slot across `state_transition`**, if the justified one is in the history |
| `ST1.process_slots_avanza` | if `process_slots` accepts, the state is at the requested slot |
| `ST1.process_slots_rechaza` | if the requested slot is not in the future, it rejects and leaves the state untouched |
| `ST2.process_block_header_slot` | if `process_block_header` accepts, the latest header is at the block's slot |
| `ST2.state_transition_conserva_no_genesis` | if the latest header was not the genesis one, it still is not after `state_transition` |
| `ST4.state_transition_justificado_ge_finalizado` | **if the finalized slot does not exceed the justified one before `state_transition`, it does not after** |
| `ST6.finalizacion_irreversible` | finality does not roll back across `state_transition` — the `ST-3` half, under its own name |
| `JS.set_luego_is_justified` | after `set_justified(s)`, `is_slot_justified(s)` returns `Ok(true)` |
| `JS.extend_to_slot_no_pierde_bits` | `extend_to_slot` changes no bit's value or place |
| `JS.extend_to_slot_conserva_respuestas` | whatever `is_slot_justified` answered before extending, it answers after |
| `JS.shift_window_corre` | after `shift_window`, the bit at `i` is the one that was at `i + delta` |
| `JS.finalizar_conserva_justificados` | **when finality advances and the window shifts, every slot above the new boundary is reported as before** |
| `NP.is_slot_justified_total` | `is_slot_justified` never panics |
| `NP.set_justified_total` | if `is_slot_justified` answers `Ok`, `set_justified` returns |
| `NP.set_justified_panico` | if it answers `Err`, `set_justified` panics |
| `NP.set_justified_tras_voto_valido` | after a valid vote, `set_justified` on its target returns |
| `NP.extend_to_slot_devuelve` | `extend_to_slot` returns, if the requested slot is no more than 262144 from the finalized one |
| `NP.shift_window_devuelve` | `shift_window` returns, if the list is no longer than 262144 bits |
| `NP.finalizar_conserva_justificados_total` | **the composite, with no panic conditional** |
| `VC.tras_header_cubre` | after `process_block_header`, `is_slot_justified` answers `Ok` for every slot before the block's |
| `VC.tras_header_rechaza` | and answers `Err` from the block's slot onwards, if the input window was not longer than it should be |
| `VI.state_transition_conserva_ventana` | the transition preserves that the window does not reach past the last materialized slot |
| `VI.state_transition_ventana_justa` | **after an accepted block, the window ends exactly at the slot before the block's** |
| `VI.tras_header_rechaza_inv` | the "exactly" in the `is_valid_vote` comment, with that invariant instead of the loose hypothesis |
| `HC.header_acepta_slot_acotado` | **`process_block_header` accepts no block with a slot above 262144** |
| `HC.state_transition_conserva_acotado` | the transition preserves both invariants: where the window ends, and one hash per slot with the slot bounded |
| `HC.shift_window_no_falla` | with those invariants, `shift_window` on the state's window returns |
| `NP2.current_proposer_eq` | `current_proposer` always returns: `None` with no validators, `Some(slot % n)` with validators |
| `NP2.is_proposer_total` | `is_proposer` never panics |
| `NP2.slot_is_justifiable_total` | `slot_is_justifiable_after` never panics |
| `NP2.matches_chain_total` | `attestation_data_matches_chain` never panics |
| `NP2.is_valid_vote_total` | **`is_valid_vote` never panics, for any state and any vote** |
| `NP3.process_slots_devuelve` | `process_slots` does not panic, if the state hash returns |
| `NP3.process_block_header_devuelve` | **`process_block_header` does not panic**, with one hash per slot in the history and if its two hashes return |
| `NP4.claves_ordenadas_devuelve` | the hand-written sort of the roots terminates and does not change how many there are, if `H256` comparison returns |
| `NP4.serialize_justifications_devuelve` | **`serialize_justifications` does not panic**, with the vote map within the limits and if `H256` comparison returns |
| `MV.construir_mapa_acotado` | the vote map built from the state has no list longer than `validator_count` |
| `MV.loop_conserva_acotado` | the attestation loop preserves that bound |
| `MV.serialize_tras_attestations_devuelve` | with the map `process_attestations` leaves, `serialize_justifications` returns with one hypothesis fewer |
| `NP5.filtrado_devuelve` | `filtrado`, the replacement for `retain`, does not panic |
| `NP5.try_finalize_devuelve` | **`try_finalize` does not panic**, with the source before the target, the window within capacity and if the `HashMap` lookup returns |
| `NP5.try_finalize_devuelve_inv` | the same, with the window's capacity taken from the transition's invariants |
| `NP6.contar_datos_devuelve` | counting a block's distinct attestation data does not panic |
| `NP6.hay_raiz_cero_devuelve` | looking for the zero root does not panic |
| `NP6.primer_bit_devuelve` | looking for the first out-of-range bit does not panic |
| `NP6.votos_vacios_devuelve` | `votos_vacios(n)` returns, and returns `n` votes |
| `NP6.poner_si_falta_devuelve` | adding a root to the map does not panic if there is room, and adds at most one |
| `NP6.marcar_votos_devuelve` | marking an aggregation's votes does not panic nor change how many entries there are |
| `NP6.cuenta_votos_devuelve` | counting a root's votes does not panic |
| `NP6.sin_devuelve` | dropping a root from the map does not panic nor leave more entries |
| `NP6.construir_mapa_devuelve` | building the vote map from the state does not panic, if `roots * validator_count` does not overflow |
| `NP6.construir_rts_devuelve` | building the root-to-slot `HashMap` does not panic, if the `HashMap` returns |
| `NP7.process_attestations_devuelve` | **`process_attestations` does not panic**, with the limits of its types and if the `HashMap` and `H256` comparison return |
| `NP7.process_attestations_devuelve_inv` | the same, with the window and finality taken from the transition's invariants |
| `bind_da_ok` | a tool: opens one `RustM` bind |

They were not picked for count. Between them they cover arithmetic, branching
and record updates, induction over a loop, composition across a whole
function with early exits and a `match`, composition of five functions up to
the entry point, a property that depends on the contents of a list and not
only on guards and assignments, exact statements about two copy loops, and
total correctness — that the function returns, termination included — for a
whole module.

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
`ok` — and that `ok` is the toolchain's, not Rust's. Aeneas wraps every
translated function in `RustM`, which has three outcomes: `ok`, `fail` (a panic
— an arithmetic overflow, an index out of range) and `div` (non-termination).
`process_attestations` translates to `RustM (Result<(), Error> × State)`, so a
block your code rejects is `ok (Err e, state')` and **is covered**: the
justified slot does not go backwards on that path either.

What the statements leave out is the runs that panic or do not terminate. That
is a real limit and not a matter of shape: a panic in the STF does not reject a
block, it takes the node down. Absence of panic is a separate and much larger
theorem. It is proved for the justified-slots window and for five functions of
the transition — see **The window does not panic** and the section on the five
functions — and not for the rest.

This is the property your own test asserts by example, in
`latest_justified_does_not_regress_within_block`. Its comment says why it
exists: on devnet at slot 27984 a block carried three supermajority
attestations targeting slots 27978, 27981 and 27974 in that order, the
unconditional assignment kept the last, and the chain froze. The test covers
that scenario; the theorem covers every input on
which the function returns at all, whether it accepts the block or rejects it.

### The whole transition

The two halves above are each about the component where a field moves. Three
more lemmas carry them up to the function you call per block:

- `process_slots` leaves both checkpoints untouched;
- `process_block_header` keeps both checkpoint **slots**;
- finality, proved above for `try_finalize` alone, carried through the
  attestation loop and the rest of `process_attestations`.

Composed through `process_block`, they give:

```lean
theorem ST3.state_transition_no_retrocede
    (state state' : tipos.State) (block : tipos.Block) (res : ...) :
    stf.state_transition state block = ok (res, state') →
    state.latest_justified.slot ≤ state'.latest_justified.slot ∧
    state.latest_finalized.slot ≤ state'.latest_finalized.slot
```

The same conditional applies: `ok` is `RustM`'s, so rejected blocks are covered
and panics are not.

The header lemma is the one with a trap in it. On the first block after genesis
your code anchors the checkpoints:

```rust
state.latest_justified.root = parent_root;
state.latest_finalized.root = parent_root;
```

It writes the **root** and leaves the slot alone, so the statement about slots
holds for every state, with no well-formedness hypothesis. What does not hold is
equality of the whole checkpoint, and Lean says so: as a control we stated that
false version and ran the same proof script, and it stops with exactly the
anchoring branch open — `{ root := r, slot := state.latest_justified.slot } =
state.latest_justified`.

### Checkpoint replacement, and where your code departs from the spec

`ST-3` bounds only the slots. It still admits a transition that swaps a
checkpoint's **root** without moving its slot. The catalog closes that with
`ST-7`: across a transition each checkpoint is either unchanged as a whole —
root included — or moves to a strictly higher slot.

In the catalog's model that holds for every post-genesis state, because the
spec compares with a strict `>`:

```python
# leanSpec, state_transition.py
if target.slot > latest_justified.slot:
    latest_justified = target
```

Your code does not:

```rust
state.latest_justified =
    std::cmp::max_by_key(state.latest_justified, target, |c| c.slot);
```

`max_by_key` returns the **second** argument when the keys tie. Given a target
at the same slot as the justified checkpoint, the spec keeps the one it had and
you keep the target. Our rewrite preserves that behaviour: `if target.slot >=
state.latest_justified.slot`.

**As stated, `ST-7` is false of your code.** The test
`same_slot_root_swap_needs_a_justified_root_off_the_chain` shows it. It starts
from a state with `latest_justified = (4, X)` where
`historical_block_hashes[4]` is a different root and slot 4 is not marked in
`justified_slots`; a supermajority votes for the target
`(4, historical_block_hashes[4])`; after `process_attestations` the justified
checkpoint is still at slot 4 and has a different root. On that same state the
spec does not replace it: `4 > 4` is false. That last part we read off the
leanSpec source, we did not run it; the catalog has it proved of its model.

We do not believe that state is reachable by applying blocks to a well-formed
genesis, but we did not prove it (see the end of this section). And you already
treat a state with broken cross-field invariants as a possible input: the
comment on `process_attestations_rejects_justification_votes_length_mismatch`
says a malformed checkpoint-sync anchor can carry one, because SSZ decoding
does not check them.

What does hold, and is proved:

```lean
theorem ST7.state_transition_adelante
    (state state' : tipos.State) (block : tipos.Block) (res : ...)
    (hnz : state.latest_block_header.slot ≠ 0#u64)
    (hhist : ST7.EnElHistorial state.historical_block_hashes
               state.latest_justified) :
    stf.state_transition state block = ok (res, state') →
    (state'.latest_justified = state.latest_justified ∨
       state.latest_justified.slot < state'.latest_justified.slot) ∧
    (state'.latest_finalized = state.latest_finalized ∨
       state.latest_finalized.slot < state'.latest_finalized.slot) ∧
    ST7.EnElHistorial state'.historical_block_hashes state'.latest_justified
```

`hnz` is the catalog's hypothesis: it excludes genesis anchoring, the one place
where the root changes on purpose. `hhist` is ours: `EnElHistorial hist c` says
`hist[c.slot] = c.root`, that is, the justified checkpoint is the block the
history holds at that slot. The third part of the conclusion says `hhist` is
preserved.

The reason it holds is not the spec's reason. `is_valid_vote` only lets a vote
through if `attestation_data_matches_chain` accepts it, and that requires
`historical_block_hashes[target.slot] == target.root`. A target that ties on
slot with the justified checkpoint therefore has the same root as it, and is
the same checkpoint: the assignment happens and changes nothing. The spec is
safe because of the comparison; your code, because of the check against the
history. With the spec's `>`, `hhist` would not be needed.

The finality half does not need `hhist`: `try_finalize` assigns only if
`source.slot > latest_finalized.slot`.

As a negative control we ran the same loop script without `hhist`. One goal is
left open, and it is the `target.slot ≥ latest_justified.slot` branch.

Three things this needed that are useful beyond this theorem:

- **The translated equality on `H256` is equality.** `==` on `[u8; 32]`
  translates to a `CoreModels` loop comparing byte by byte. `ST7.h256_eq_true`
  proves that if it returns `true` the two values are equal. Without it you
  cannot get from "the code compared and got equal" to an equality in Lean.
- **`mem::take` is no longer an axiom.** `process_block_header` takes
  `historical_block_hashes` out of the state with `std::mem::take`, appends the
  parent root and stores it back. With `take` as a contentless signature it was
  impossible to prove the old history is still there. It is now a definition —
  it returns what was there and leaves the `Default` — and it is one of the
  three modeling claims we make, next to `isqrt` and `bool::then`.
- **`process_block_header` only appends to the history**, and outside the
  anchoring it leaves both checkpoints whole
  (`ST7.process_block_header_no_toca_checkpoints`).

What is **not** proved: that the first block after genesis leaves the state
satisfying `hhist`. That is the lemma missing to say "it holds on every state
reachable from genesis". The other hypothesis is preserved: that `hnz` carries
from one block to the next is proved further down, with `ST-2`.

### The other four state-transition propositions

The catalog has seven propositions about the state transition. With the two
above, these complete the list.

**`ST-1`, slot advancement.** The catalog states it with `slot ≤ target`,
because its model of `process_slots` returns a state and does not reject. The
Python spec and your code both reject when `slot >= target`, so here it is two
statements: if it accepts, the state is at the requested slot
(`ST1.process_slots_avanza`); and if the requested slot is not in the future,
it returns `StateSlotIsNewer` and the state untouched
(`ST1.process_slots_rechaza`). The second is not conditional: it says what is
returned.

**`ST-2`, the header.** If `process_block_header` accepts, the latest header is
at the block's slot. The same lemma gives what `ST-7` was missing: if the latest
header was not the genesis one, it still is not, accepted or rejected. That is
lifted to the whole transition (`ST2.state_transition_conserva_no_genesis`),
which needed a proof that the rest of `state_transition` leaves
`latest_block_header` alone.

**`ST-4`, justified ≥ finalized.**

```lean
theorem ST4.state_transition_justificado_ge_finalizado
    (state state' : tipos.State) (block : tipos.Block) (res : ...)
    (hinv : state.latest_finalized.slot ≤ state.latest_justified.slot) :
    stf.state_transition state block = ok (res, state') →
    state'.latest_finalized.slot ≤ state'.latest_justified.slot
```

In the catalog this is an invariant of reachable states. This is its inductive
step, and it holds for every state: if it holds before the transition, it holds
after. The reason is in plain sight in your code. `try_finalize` only runs right
after a target is justified; what it finalizes is that vote's `source`; and
`is_valid_vote` requires `target.slot > source.slot`. The new finalized slot is
therefore below the target, which in turn does not exceed the new justified
slot. No reasoning about the `justified_slots` bitlist was needed.

As a negative control we ran the same script with an `is_valid_vote` lemma that
says nothing. Exactly the two cases where finality moves to the `source` stay
open, asking for `source.slot ≤` the new justified slot.

The base case is missing: that the genesis state satisfies the invariant. The
crate does not build that state.

**`ST-6`, finality is irreversible.** The catalog itself says it is the
`latest_finalized` half of `ST-3`. `ST6.finalizacion_irreversible` gives it a
name.

**`ST-5`, purity, is not stated.** In the catalog it is
`transition s b = transition s b`, proved by `rfl`. That holds of any Lean
function, your translated one included, and adding it would say nothing about
the code.

### The justified-slots window

`justified_slots_ops` is the bitlist that records which slots are justified,
indexed relative to the finalized slot. The results above went around it: they
come from guards, assignments and the history. These go in.

They are not from the catalog. They are the four we set ourselves on 22
October, on first reading your code and before translating anything:

| | Statement |
|---|---|
| round trip | after `set_justified(s)`, `is_slot_justified(s)` returns `Ok(true)` |
| `extend_to_slot` | the new list is the old one plus zeros at the end: no bit changes value or place |
| `shift_window` | the new list is the old one without its first `delta` bits |
| the composite | when finality advances from `f` to `f'` and the window shifts by `f' − f`, every slot above `f'` is reported as before |

The last one is what justified the exercise:

```lean
theorem JS.finalizar_conserva_justificados
    (slots slots' : ssz.SszBitlist ...) (f f' s : U64) (delta : Usize) (b : Bool)
    (hff : f.val ≤ f'.val) (hfs : f'.val < s.val)
    (hdelta : delta.val = f'.val - f.val)
    (hfit : s.val - f.val - 1 < 2 ^ UScalarTy.Usize.numBits) :
    is_slot_justified slots f s = ok (Ok b) →
    shift_window slots delta = ok slots' →
    is_slot_justified slots' f' s = ok (Ok b)
```

It involves three functions and two index systems. Slot `s` sits at position
`s − f − 1` before and at `s − f' − 1` after, and `shift_window` must have moved
exactly that bit. It is not something you check by reading.

Three things differ from everything above.

**The statements are exact.** They do not say "does not go backwards" but which
list results: `slots ++ zeros` for `extend_to_slot`, `slots.drop delta` for
`shift_window`.

**Two of the conclusions are not conditional.** The round trip and the composite
conclude that `is_slot_justified` *returns* `Ok`. That required proving, as
equations, what `get`, `set`, `len` and `relative_index` return — for instance
`get s i = ok (s.bits[i]?)` — going down through the `core` models to the
bottom: slice indexing, `vec![false; n]`, overflowing subtraction. The first
call in each statement (`set_justified`, `shift_window`) is still conditional,
as everywhere else.

**The copy loops have their invariant in plain Lean.** `Copiado` and
`Desplazado` are predicates on lists, and their step lemmas mention nothing
about Rust. The translated loop leaves three goals — bit set, bit clear, end of
range — and each one is a step lemma.

**The composite asks that the distance fit in a `usize`.** `relative_index`
does `idx as usize`, and the toolchain's model does not fix the width of
`usize`. On 64 bits `hfit` always holds. On 32 bits that cast truncates, and two
slots 2³² apart would share a bit. Not a live bug, but a precondition the code
does not state.

The three `.expect()` and the `.unwrap()` in this module (`"index out of
bounds"`, `"capacity limit exceeded"`, `"index within capacity"`) are the
subject of the next section.

### The window does not panic

Everything above says "if the function returns, then…". This is the other
thing: that it **returns**. It is done for the four functions of
`justified_slots_ops`, which have three `.expect()`, one `.unwrap()` and two
additions that could overflow.

| Function | When it returns |
|---|---|
| `is_slot_justified` | always |
| `set_justified` | exactly when `is_slot_justified` answers `Ok` for that slot |
| `extend_to_slot` | if the requested slot is at most 262144 above the finalized one |
| `shift_window` | if the list is no longer than 262144 bits |

The `set_justified` one is two lemmas, and together they say when its
`expect("index out of bounds")` fires:

```lean
theorem NP.set_justified_total ... :
    is_slot_justified slots f t = ok (Ok b) →
    ∃ slots', set_justified slots f t = ok slots'

theorem NP.set_justified_panico ... :
    is_slot_justified slots f t = ok (Err e) →
    set_justified slots f t = fail Error.panic
```

The second is not a working hypothesis: it proves the panic happens. If the
slot is outside the window, `set_justified` aborts.

**At the call site that panic cannot fire.** The `process_attestations` loop
calls `set_justified` on a vote's target only after `is_valid_vote` accepted
it, with the same state between the two calls.
`NP.set_justified_tras_voto_valido` proves that is enough: `is_valid_vote`
returns `Ok(true)` only if `is_slot_justified` answered `Ok(false)` for the
target, that is, the target is inside the window.

**The composite becomes unconditional.** With `shift_window` returning,
`NP.finalizar_conserva_justificados_total` says that when finality advances the
window shifts *and* every slot above the new boundary is reported as before.

How the technique changes. The earlier triples use `PostCond.mayThrow`, which
tolerates panic and divergence. These use `⇓`, which tolerates neither, so every
point where the code could abort shows up as a goal to prove: that the index is
in range, that the addition does not overflow, that what is asked for fits the
capacity. The loop has to be given a real termination measure (`end − start`)
instead of the constant that was enough before. The rest is the same: the same
list invariants and the same step lemmas.

As a negative control we ran the `shift_window` proof without the capacity
hypothesis. It stops at one goal, the `expect` on `with_length`: it cannot show
that what remains fits in 262144.

**What is not there.** That the capacity hypotheses hold on every reachable
state: that the window never exceeds 262144 bits and that no slot ends up
further than that from the finalized one. Those are invariants of the whole
state, not of this module. And the other functions of the STF keep their
conditional.

### A comment of yours about the window, checked

The comment on `is_valid_vote` says:

```rust
/// After `process_block_header` the window covers up to
/// `block.slot - 1`, so this is exactly a vote whose source or target slot is
/// at or beyond the importing block's own slot.
```

It is a claim about what `process_block_header`, `extend_to_slot` and
`is_slot_justified` do together. It is now two theorems, one per half of the
sentence.

**"Covers up to `block.slot − 1`".** If `process_block_header` accepts, then for
every slot before the block's `is_slot_justified` answers `Ok`
(`VC.tras_header_cubre`). It holds for any input state.

**"Exactly".** From the block's slot onwards it answers `Err`, which is
`JustifiedSlotOutOfRange` (`VC.tras_header_rechaza`). This half **does not hold
for every state**: it asks that the input window did not already reach past the
slot before the block.

```lean
(hlen : state.justified_slots.bits.val.length +
          state.latest_finalized.slot.val + 1 ≤ block.slot.val)
```

With a window longer than it should be, a vote with a slot after the block
would not be rejected as out of range. So the comment's "exactly" is true under
an invariant the comment does not mention: that the window ends right at the
last materialized slot. We did not prove that invariant is preserved across the
transition; see below.

As a negative control we ran the second proof without `hlen`. It fails at the
two places where it is used, and nowhere else.

What it took was the exact length `extend_to_slot` leaves — the maximum of what
it had and what was asked for — which was not among the window results, and
which window `process_block_header` leaves: the input one passed through
`extend_to_slot` up to `block.slot − 1`, with the same finalized slot.

That `hlen` is preserved from one block to the next is the subject of the next
section.

### Where the window ends

The previous section left a loose hypothesis: that the input window did not
reach past the slot before the block. Here it is as an invariant of the whole
transition.

There are two predicates on the state:

- `VentanaNoPasa`: the window's length plus the finalized slot does not exceed
  the latest header's slot. It holds at genesis, where the window is empty and
  the finalized slot is zero.
- `VentanaJusta`: length + finalized + 1 is exactly the latest header's slot.
  That is, the window covers finalized + 1 up to the header's slot − 1, not one
  bit more and not one less.

```lean
theorem VI.state_transition_conserva_ventana ...
    (h64 : UScalarTy.Usize.numBits = 64) :
    VentanaNoPasa state →
    stf.state_transition state block = ok (res, state') →
    VentanaNoPasa state'

theorem VI.state_transition_ventana_justa ...
    (h64 : UScalarTy.Usize.numBits = 64) :
    VentanaNoPasa state →
    stf.state_transition state block = ok (Ok (), state') →
    VentanaJusta state'
```

The first holds whether the block is accepted or rejected. The second says
that after an accepted block the window is exact. Since `VentanaJusta` implies
`VentanaNoPasa`, the invariant carries from one block to the next, and with it
the "exactly" in the `is_valid_vote` comment no longer needs a loose hypothesis
(`VI.tras_header_rechaza_inv`).

Why it holds. `process_block_header` extends the window up to `block.slot − 1`,
which makes it exact. Then, in the attestation loop, `set_justified` does not
change the length, and `try_finalize` moves both things at once: finality
advances by `source.slot − finalized`, and `shift_window` shortens the window by
that same amount. The sum does not change. For the arithmetic to close the
source has to be inside the window, and `is_valid_vote` guarantees that: it only
accepts the vote if `is_slot_justified` answered `Ok(true)` for the source.

As a negative control we ran the loop without that fact about the source. The
cases where nothing is finalized still close; exactly the two where something
is stay open.

**This whole result assumes a 64-bit `usize`.** It is the same `as usize` as in
the previous sections, which here appears three times: the source's index, the
`delta` passed to `shift_window`, and the index of the last slot in the header.
On 32 bits those casts truncate and the arithmetic does not close. We did not
analyse what happens in that case beyond that.

That the window does not exceed 262144 bits is the subject of the next section.

### The window stays within capacity

The previous section leaves the window bounded by the latest header's slot.
That slot still has to be bounded, and the bound comes from a second invariant,
about the hash history:

- `HistorialAcotado`: `historical_block_hashes` has exactly one hash per slot —
  its length is the latest header's slot — and that slot does not exceed
  262144, which is `HISTORICAL_ROOTS_LIMIT`.

It holds at genesis and is preserved by `state_transition`, whether the block is
accepted or rejected. `process_block_header` appends to the history the parent
root and one zero per empty slot between the parent and the block:
`block.slot − parent.slot` elements in all, so if there was one per slot there
still is. And before appending them it checks that the total does not exceed
`HISTORICAL_ROOTS_LIMIT`. That total **is** the block's slot.

Two things follow.

**No block with a slot above 262144 is accepted.**

```lean
theorem HC.header_acepta_slot_acotado ...
    (h64 : UScalarTy.Usize.numBits = 64)
    (hlen : state.historical_block_hashes.items.val.length =
              state.latest_block_header.slot.val) :
    stf.process_block_header state block = ok (Ok (), state') →
    block.slot.val ≤ 262144
```

This is not a difference from the spec: the cap is the same in leanSpec
(`2**18`) and in your code. It is a consequence of that cap, and worth having
written down: with one hash per slot since genesis, the chain does not go past
slot 262144. The check you added to
avoid an unbounded allocation (`SlotGapTooLarge`) is what enforces it.

**The window does not exceed 262144 bits.** With both invariants, this
section's and the previous one's, `HC.ventana_en_capacidad` gives the bound,
and `HC.shift_window_no_falla` uses it: on the window of such a state,
`shift_window` returns. It is the capacity hypothesis of **The window does not
panic**, discharged. `HC.state_transition_conserva_acotado` says the two
invariants together carry from one block to the next.

As a negative control we ran the slot bound without the one-hash-per-slot
hypothesis. It fails at the final arithmetic.

What it took was the exact length left by the loop that fills in the empty
slots — before there was only that it appends — and that
`process_attestations` leaves the history alone, with no hypothesis.

**Where it is used.** In absence of panic for `try_finalize` and for
`process_block_header`, further down: they are the two functions that call
`shift_window` and `extend_to_slot`.

### Five functions of the transition do not panic

**The window does not panic** did it for the helper module. This starts on the
transition proper, with the five small functions of `stf.rs`:

| Function | Result |
|---|---|
| `current_proposer` | always returns: `None` with no validators, `Some(slot % n)` with validators |
| `is_proposer` | always returns |
| `slot_is_justifiable_after` | always returns |
| `attestation_data_matches_chain` | always returns |
| `is_valid_vote` | always returns, for any state and any vote |

None carries a hypothesis: they hold for every input.

Where a panic could have been and why there is none:

- `current_proposer` divides by the number of validators. Your
  `(n > 0).then(…)` is what prevents it, and the statement says it in full:
  with zero validators it returns `None`, it does not abort.
- `slot_is_justifiable_after` squares an integer square root, twice. It does
  not overflow because the square of the integer root does not exceed the
  original number. The rest of its arithmetic already uses `checked_mul` and
  `checked_add`.
- `attestation_data_matches_chain` reads three positions of the history. All
  three are checked against the length before reading.
- `is_valid_vote` combines the above with two `?`. When the `?` cuts, what it
  propagates is an `Err`, and that is enough for it not to abort.

As a negative control we ran `slot_is_justifiable_after` with an `isqrt` lemma
that says it returns but not what. Exactly the two squarings stay open.

**`bool::then` is no longer an axiom.** `current_proposer` is
`(n > 0).then(|| slot % n)`, and with `then` as a contentless signature not
even "it returns" could be proved. It is now a definition — it calls the
closure only if the boolean is true and wraps the result in `Some` — and it is
the third modeling claim we make.

**These five results depend only on Lean's three axioms.** No native axiom and
no contentless declaration: they are the first results about the translated
code in this package where `#print axioms` lists nothing else. That does not
mean they assume nothing. They still lean on two of our modeling claims,
`bool::then` and `isqrt`, which are definitions and so do not show up as
axioms.

### `process_slots` and `process_block_header` do not panic

Next come the two functions of `stf.rs` that hash.

| Function | Result | Hypotheses |
|---|---|---|
| `process_slots` | always returns | that the state hash returns |
| `process_block_header` | always returns | 64-bit `usize`; one hash per slot in the history; that the hash of the previous header and the hash of the block body return |

**The hash is a hypothesis, on purpose.** The `hash_tree_root` in this crate is
a stand-in for yours. Proving that the stand-in terminates would say nothing
about yours, so each statement carries "this call to the hash returns" in
writing, once per call. It is the only thing these two results ask of the
hash.

Where a panic could have been and why there is none:

- In `process_slots`, the subtraction `target_slot - state.slot`. The check
  above has already ruled out `state.slot >= target_slot`.
- In `process_block_header`, `block.slot - parent_header.slot - 1`. The
  `ParentSlotIsNewer` check guarantees the difference is at least one.
- `current_len + 1 + num_empty_slots`. With one hash per slot in the history
  that sum is exactly `block.slot`, which fits in a `u64`.
- The `push` calls and the loop that fills in the empty slots. The loop
  terminates — now with a termination measure — and leaves exactly `new_total`
  entries.
- The `expect("pre-validated: total does not exceed limit")`. The comment is
  right: at that point the vector has `new_total` entries, which already passed
  the check against `HISTORICAL_ROOTS_LIMIT`, and `try_from` gives `Ok`.
- `block.slot - 1`. The block's slot is greater than the previous header's.
- `extend_to_slot`. It receives a window that fits the capacity, because
  `block.slot` does not exceed 262144.

**A precondition the code takes for granted.** `new_total` is computed before
it is compared against the limit:

```rust
let num_empty_slots = (block.slot - parent_header.slot - 1) as usize;
let current_len = state.historical_block_hashes.len();
let new_total = current_len + 1 + num_empty_slots; // +1 for parent_root push
if new_total > HISTORICAL_ROOTS_LIMIT {
```

If the history had more entries than the previous header's slot, that sum
could exceed `usize::MAX` for a very large `block.slot`, before the check gets
to reject it. The "one hash per slot" hypothesis is what prevents it. It is
not a new hypothesis: it is the first half of the invariant in **The window
stays within capacity**, which the transition preserves. We know of no
reachable state that violates it, and we are not presenting it as a bug. It is
the condition under which the result holds, and it is written down.

As a negative control we removed that hypothesis. The proof stops closing, and
what stays open is exactly that: the two sums, in both branches, and the
window's capacity in the branch that is not the genesis one.

In the Lean model an overflow is a panic. What a binary compiled without
overflow checks does is not modeled by this package.

`NP3.process_slots_devuelve` depends only on Lean's three axioms.
`NP3.process_block_header_devuelve` depends on seven: those three, three
native ones, and the `fmt` signature of the error that the `expect` formats.

### `serialize_justifications` does not panic

This is the function that writes the vote map back into the two state fields.
It sorts the roots, asks for a bitlist of `roots * validator_count` bits, dumps
each root's votes into its own stretch, and stores the roots.

It has three `expect`s, and each one is tied to a hypothesis of the statement:

| `expect` | What makes it true |
|---|---|
| `"maximum validator justifications reached"` | at most 262144 roots and at most 4096 validators: the two limits of your types, whose product is exactly the bitlist's capacity |
| `"we just updated the capacity"` | that no vote list is longer than `validator_count`: then each vote's bit falls inside its root's stretch |
| `"justifications_roots limit exceeded"` | at most 262144 roots |

With the two limits `roots * validator_count` does not overflow either, nor
does the `base` that advances one stretch per root.

**`H256` comparison is a hypothesis.** The sort compares roots with `<`. That
array comparison is one of the twenty-six contentless declarations in this
package, so it cannot be proved to return: the statement asks for it, as with
the hash. It is the first time a result names one of those declarations in its
hypotheses.

**The hand-written sort terminates.** `claves_ordenadas` replaces your
`sort()` with an insertion sort written with explicit loops.
`NP4.claves_ordenadas_devuelve` says it terminates, does not abort, and returns
as many roots as the map has keys. That it also leaves them sorted is not
proved, and could not be with the comparison as a contentless declaration.

Negative controls, two. Without the hypothesis on the vote lists a goal shows
up that does not close: that the vote fits in its stretch. Without the bound
on validators, the bitlist's capacity and the product stay open.

`NP4.claves_ordenadas_devuelve` depends on four axioms: Lean's three and the
array comparison. `NP4.serialize_justifications_devuelve` depends on eight:
those four, three native ones, and the `fmt` signature of the error that the
`expect`s format.

**What is not there.** That the map `process_attestations` builds meets those
hypotheses: one is in the next section, the others are not.

### The vote map meets one of those hypotheses

Of the four hypotheses of `serialize_justifications`, one is about the vote
lists: that none is longer than `validator_count`. The map is built by
`process_attestations`, and here it is proved that it builds it that way.

| Result | What it says |
|---|---|
| `MV.construir_mapa_acotado` | the map that comes out of `construir_mapa_de_votos` meets the bound |
| `MV.loop_conserva_acotado` | the attestation loop preserves it |
| `MV.serialize_tras_attestations_devuelve` | with that map, `serialize_justifications` returns asking only for the other three hypotheses |

Why it holds:

- `construir_mapa_de_votos` builds each list from one root's stretch, which is
  exactly `validator_count` long.
- In the loop, the only thing that adds a list is a new vote, and it adds it
  with `validator_count` votes set to false.
- Marking a vote changes a bit, not the length.
- Dropping an already justified root, and filtering on finalization, only copy
  lists that were already there.

These are "if it returns" results: they do not say the loop terminates, they
say what map it leaves when it does. That is what discharging a hypothesis
needs.

As a negative control we took away from the loop the fact that the new list is
`validator_count` long. The proof stops closing.

**What is still asked for.** Three hypotheses:

- That `H256` comparison returns.
- At most 4096 validators. `validator_count` is `state.validators.len()` and
  4096 is that type's limit, but the `SszList` in this crate does not carry the
  limit as an invariant.
- At most 262144 roots in the map. This is the hard one. The loop can add one
  root per attestation, so the easy count gives "the state's roots plus the
  attestations", which is not enough. The real bound comes from elsewhere: the
  map's roots are all distinct and all in the history, which has at most 262144
  entries. That invariant is not proved.

`MV.construir_mapa_acotado` depends only on Lean's three axioms.
`MV.loop_conserva_acotado` depends on fourteen and
`MV.serialize_tras_attestations_devuelve` on eighteen; the breakdown is in the
table under **The trust base**.

### `try_finalize` does not panic

This is the function that, when a justification closes a stretch with no
justifiable slots in between, advances finality, shifts the window and drops
from the vote map the roots left behind.

| Hypothesis | What for |
|---|---|
| the `source` is before the `target` | so that `source.slot + 1` does not overflow |
| the window does not exceed 262144 bits | so that `shift_window` does not abort |
| the `HashMap` lookup returns | cannot be proved here: `HashMap::get` is a contentless signature |

**`source.slot + 1` stops being an unstated precondition.** It has been under
**Honest limits** from the start: with `source.slot = u64::MAX` the increment
overflows. It is now written as a hypothesis, and a natural one: that the
source is before the target. In the one place where `try_finalize` is called
that is already guaranteed, because `is_valid_vote` checks it, and that check
is proved further up.

**The window's capacity comes from the invariants.**
`NP5.try_finalize_devuelve_inv` is the same result, asking for the two
invariants the transition preserves instead of the capacity.

**The `HashMap` is a hypothesis.** As with the hash and `H256` comparison: the
lookup is a contentless declaration, so the statement asks that it return.

What had to be proved anew:

- `filtrado`, the replacement for your `retain`, terminates and does not
  abort, with no hypothesis. That is `NP5.filtrado_devuelve`.
- Copying a vote list terminates and does not abort. In the translation
  `Vec::clone` is a loop.
- Stepping a `u64` range. The hax library ships that lemma for `usize` and for
  `i32`, not for `u64`, and slots are iterated here.

Negative controls, two. Without "the source is before the target", exactly the
`source.slot + 1` overflow stays open. Without the capacity, the precondition
of `shift_window` stays open.

The two results on `try_finalize` depend on thirteen axioms: Lean's three,
three native ones and seven declarations. `NP5.filtrado_devuelve` depends only
on Lean's three.

### The pieces of `process_attestations` do not panic

`process_attestations` is the big function, and the one we rewrote the most:
its iterators and closures became helper functions with explicit loops. Before
going through all of it, each of those helpers has to be known to return. Ten
results:

| Function | Hypotheses |
|---|---|
| `contar_datos_distintos` | none |
| `hay_raiz_cero` | none |
| `primer_bit_fuera_de_rango` | none |
| `votos_vacios` | none |
| `marcar_votos` | none |
| `cuenta_votos` | none |
| `sin` (drop a root from the map) | none |
| `poner_si_falta` (add a root) | that there is room for one more entry |
| `construir_mapa_de_votos` | that `roots * validator_count` does not overflow |
| `construir_root_to_slot` | that `finalized + 1` does not overflow, and that the `HashMap` returns |

Seven ask for nothing. The ones that count carry a counter that never exceeds
what has been traversed, which is why their `+ 1` does not overflow. The ones
that read do so with `get`, which returns `None` out of range instead of
aborting.

**The `HashMap`, now all of it.** `try_finalize` only looked it up.
`construir_root_to_slot` creates it and fills it, so the hypothesis covers all
three operations, `new`, `get` and `insert`, and has to hold for every map
rather than for one, because the map changes on each iteration. All three
remain contentless declarations.

**Several results also say how big what they return is**: how many entries
are left in the map, how many votes a list has. That is what chaining them in
the loop needs, where each `push` has to know there is room.

Negative controls, three. Without the bounded product, the overflow of
`(i + 1) * validator_count` stays open. Without `finalized + 1` bounded, that
overflow stays open. Without room in the keys, the `push` does not close.

Nine of the ten depend only on Lean's three axioms. The one on
`construir_root_to_slot` depends on eleven: those three and eight
declarations, the `HashMap` ones.

**Where they are used.** In the next section, which puts them together.

### `process_attestations` does not panic

This is the big function of the transition: it goes through the block's
attestations, counts votes, justifies and finalizes, and at the end writes the
vote map back into the state.

| Hypothesis | What for |
|---|---|
| the `HashMap` returns (`new`, `get`, `insert`) | they are contentless signatures |
| `H256` comparison returns | used by the sort when serializing; also a contentless signature |
| at most 4096 validators | so that `3 * votes` and `2 * validator_count` do not overflow, and the vote bitlist fits its capacity |
| the state's roots plus the block's attestations do not exceed 262144 | so that there is room in the vote map and in `justifications_roots` |
| the window does not exceed 262144 bits | so that `shift_window` does not abort |
| `finalized + 1` does not overflow | used by `construir_root_to_slot` |

`NP7.process_attestations_devuelve_inv` is the same result, with the last two
taken from the invariants the transition preserves.

**What is carried along the loop.** Four things: the window does not grow; no
vote list is longer than `validator_count`; the map grows by at most one entry
per iteration; and the processed-attestations counter does not exceed the
number traversed.

**The delicate point is `set_justified`.** It aborts if the target falls
outside the window. That does not happen, because it is only called after an
`is_valid_vote` that returned `true` on the same state, and that check has
already read that slot. This is a result from **The window does not panic**,
put to use. The same vote gives that the source is before
the target, which is what `try_finalize` asks for.

**The bound on roots is stronger than needed, and we say so.** "The state's
roots plus the block's attestations" is a sufficient condition on what goes
into the function: the loop adds at most one root per attestation. It is not
an invariant of reachable states. A state with many pending roots and a full
block falls outside this result, which does not mean it aborts: it means it is
not proved here. The fine bound, that the map's roots are distinct and in the
history, is not there.

The loop body leaves 170 conditions to check, one for each point where
something could fail on each possible path. They fall into eight classes and
are closed by class.

Negative controls, three. Without the bound on validators, the two products
stay open. Without the bound on roots, the product `roots * validator_count`,
the room in the map and the roots limit stay open. Without what
`is_valid_vote` says, `set_justified` and the order between source and target
stay open.

Both results depend on twenty axioms: Lean's three, seven native ones and ten
declarations.

**What is not there.** `process_block` and `state_transition`. Both only chain
functions that are already done, but it remains to show that the state
`process_block_header` leaves meets the hypotheses of `process_attestations`.

### What this is against the catalog, stated exactly

`ST-3` in
[`NyxFoundation/formal-leanSpec`](https://github.com/NyxFoundation/formal-leanSpec)
is stated over `State.transition` — the whole one-block transition — and bounds
both checkpoint slots at once (`State.checkpoint_monotone`).
`ST3.state_transition_no_retrocede` is that statement, about your
`state_transition` as the toolchain translates it. Two differences, so nobody
reads more into it than is there:

**It is about a different program.** The catalog proves the proposition of its
own Lean model of the spec. This proves it of the Rust in this crate, with the
stand-ins listed under **Honest limits**. Same proposition, different object: it
is not a proof of the catalog's theorem, and the catalog's is not a proof about
your code.

**It needs no `AnchorWF`.** The catalog's theorem carries an extra hypothesis,
`AnchorWF s` — if the latest block header is at slot 0, both checkpoints are at
slot 0 — because in its model the genesis anchoring force-assigns slot-0
checkpoints, which makes the bare statement false for adversarial states. Yours
assigns only the roots, so the hypothesis is not needed. On states reachable
from genesis the two agree, since there the slots are 0 already; on arbitrary
states your code and that model behave differently, which is worth knowing
whichever of the two is intended. Checked against `formal-leanSpec` at
`ba72845`.

**`ST-7` needs a hypothesis the catalog does not have.**
`State.checkpoint_forward` asks only that the latest header is not the genesis
one. `ST7.state_transition_adelante` asks for `hhist` as well, and without it
is false. Here the difference is not one of modeling but of behaviour: on a slot
tie, your code and the spec choose differently. Checked against `leanSpec`
`main` as of 15 Nov 2026 (`Checkpoint.advance_to` and `state_transition.py`) and
against your `main`, which that day was still identical to `35c074b`.

**`ST-4` is the inductive step, not the invariant.** The catalog proves
`justified_ge_finalized` by induction over its reachable states. Here is the
step — if it holds before a block, it holds after — and the base case is
missing.

The properties were not chosen because they looked provable. That catalog has
thirty-five propositions — seven about the state transition, the rest about
fork choice, SSZ, the validator, networking, storage and sync — and these are
the seven. The statements predate our work on them, which matters: picking your
own properties makes the exercise circular.

### The trust base

`#print axioms` on each result, with the output in `axiomas.txt`:

| Result | Total | Lean's | Native | Declarations |
|---|---|---|---|---|
| the two arithmetic ones | 3 | 3 | — | — |
| `bind_da_ok` | 1 | 1 | — | — |
| the two `try_finalize` ones | 13 | 3 | 3 | 7 |
| the loop theorem | 14 | 3 | 4 | 7 |
| `process_attestations`, justification and finality | 20 | 3 | 7 | 10 |
| `process_slots`, all three results | 3 | 3 | — | — |
| `process_block_header`, all three results | 7 | 3 | 3 | 1 |
| `process_block`, `state_transition` (`ST-3`) | 22 | 3 | 9 | 10 |
| equality on `H256` | 3 | 3 | — | — |
| `process_attestations` (`ST-7`) | 20 | 3 | 7 | 10 |
| `state_transition` (`ST-4`, `ST-6`, `ST-7`, header preservation) | 22 | 3 | 9 | 10 |
| the window: round trip, `shift_window`, the composite | 5 | 3 | 1 | 1 |
| the window: `extend_to_slot`, both results | 6 | 3 | 2 | 1 |
| no panic: `is_slot_justified` | 3 | 3 | — | — |
| no panic: `set_justified` (all three), `shift_window`, the composite | 5 | 3 | 1 | 1 |
| no panic: `extend_to_slot` | 6 | 3 | 2 | 1 |
| the window after the header, all three results | 7 | 3 | 3 | 1 |
| the window invariant over `state_transition`, both | 22 | 3 | 9 | 10 |
| the slot bound in the header | 7 | 3 | 3 | 1 |
| both invariants together over `state_transition` | 22 | 3 | 9 | 10 |
| `shift_window` on the window of a state with the invariants | 5 | 3 | 1 | 1 |
| no panic: the five small functions of `stf.rs` | 3 | 3 | — | — |
| no panic: `process_slots` | 3 | 3 | — | — |
| no panic: `process_block_header` | 7 | 3 | 3 | 1 |
| no panic: `claves_ordenadas` | 4 | 3 | — | 1 |
| no panic: `serialize_justifications` | 8 | 3 | 3 | 2 |
| the vote map built from the state | 3 | 3 | — | — |
| the vote map along the attestation loop | 14 | 3 | 4 | 7 |
| `serialize_justifications` with the map from `process_attestations` | 18 | 3 | 7 | 8 |
| no panic: `filtrado` | 3 | 3 | — | — |
| no panic: `try_finalize`, both results | 13 | 3 | 3 | 7 |
| no panic: nine helpers of `process_attestations` | 3 | 3 | — | — |
| no panic: `construir_root_to_slot` | 11 | 3 | — | 8 |
| no panic: `process_attestations`, both results | 20 | 3 | 7 | 10 |

Three categories, with three different weights.

**Lean's three** — `propext`, `Classical.choice`, `Quot.sound` — underpin any
classical proof and say nothing about this code.

**The native ones** are `_native.decide.ax_*`: facts the Lean kernel did not
check, computed by the compiler instead. Nine distinct ones appear across
the twelve functions. The whole-transition results depend on all nine; the
results about components depend on fewer, as the table shows.
They are not ours and not yours. Defining a function in Lean can require
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
entry. What we did not do is open each of the nine to name the fact it stands
for.

**The declarations** are ours, in `supuestos/FunsExternal.lean`: twenty-six
axioms that are signatures and no more — `HashMap`'s `get`, `insert` and `new`,
the `Borrow` and `BuildHasher` trait types, the `cmp` and `hash` of `[T; N]`,
and seventeen `fmt` stubs — fourteen `Debug`, three `Display`. They exist so the
generated Lean compiles: `try_finalize` calls `root_to_slot.get(…)`, Aeneas
names `HashMap::get` in the output, `CoreModels` has no model for it, and
without the declaration the module dies with `Unknown identifier` and nothing
builds.

That is a milder gap than the native axioms. An axiom that states nothing yields
nothing — you cannot derive a falsehood from it because you cannot derive
anything. What it costs is reach: any property depending on how the map behaves
is out of bounds. Models *with* content would buy those properties at the price
of asserting things that could be wrong, and we declined that trade.

We make three real assertions. One is `U64::isqrt`, modeled as `Nat.sqrt`: both
are the floor of the square root. Another is `mem::take`, modeled as "returns
what was there and leaves `Default::default()`". The third is `bool::then`,
modeled as "calls the closure only if the boolean is true and wraps the result
in `Some`". The last two are what their documentation says. We believe all
three, but they are our claims and not something the toolchain checked.
`mem::take` and `bool::then` were contentless declarations until 15 and 17 Nov;
that is why the results that go through `process_block_header` now have two
axioms fewer than at first. `HashMap` also gets a representation in
`TypesExternal.lean` — a list of pairs — but `get` and `insert` stay opaque over
it, so no behaviour is asserted there.

None of the twenty-six carries weight in the theorems above: the properties
come from the guards, the assignments and the hash history, not from anything
the map, the hash or the formatter does. There are exceptions, and they are
written down: the result on `serialize_justifications` asks the array
comparison to return, and the ones on `try_finalize`,
`construir_root_to_slot` and `process_attestations` ask the same of the
`HashMap`, always as hypotheses.
Of the three modeling claims, `ST-3`
leans on none; `ST-7` over the whole transition and the history invariants lean
on the `mem::take` one, because they need the history to survive
`process_block_header`; absence of panic for `current_proposer` and
`slot_is_justifiable_after` leans on the `bool::then` and `isqrt` ones; and
that of `process_block_header` on the `mem::take` and `bool::then` ones. That
is a claim about the proofs, read off them. `#print
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
| `triple_total_of`, `of_triple_total` | ours | the same bridges for total-correctness triples, the ones that tolerate neither panic nor divergence. |
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
conditional shape of the statements comes from — conditional on not panicking,
not on the block being accepted.

**Two bridges, and they are the reusable part.**

```lean
triple_mayThrow_of : (∀ v, x = ok v → P v) → ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄
of_triple_mayThrow : ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄ → x = ok v → P v
```

`triple_mayThrow_of` is the dual of `bind_da_ok`: it turns a theorem you already
have **as an equation** into the `@[spec]` lemma the tactic consumes, so a result
proved the hard way stays usable without being redone. The other direction
brings a triple back to an equation, which is how the statements above are
phrased. Twenty-three `@[spec]` lemmas feed the first two loop-related proofs,
those of `ST-3`; all but four have a trivially true postcondition, present only so the tactic can step
over a call that cannot move `latest_justified`. The four with content are
`is_none_spec`, `try_finalize_spec`, `serialize_spec`, and the loop theorem
itself, reused as a lemma for the whole function.

The lift to `state_transition` reused all of it and cost little. The finality
half is the justification proof again with a different invariant and a different
lemma for `try_finalize` — the two cannot be active at once, because the tactic
picks one lemma per call. `process_block_header` took fourteen more trivial
lemmas, one per call that neither takes nor returns the state, and with them
`hax_mvcgen` closed every verification condition by itself. `process_block` and
`state_transition` close the same way from the lemmas of what they call.

`ST-7` asked for two things `ST-3` did not. Lemmas with content for the `core`
and `alloc` operations the history goes through — `Vec::push`, `mem::take`, the
`try_from` and `expect` that store it back, `==` on `H256` — because there it
is no longer enough to get past the call: you need to know what it returns. And
a way to compose lemmas that carry hypotheses: the hypothesis goes as an
antecedent **inside** the postcondition (`⌜ hyp → conclusion ⌝`), not as an
argument of the lemma. That way `hax_mvcgen` consumes it like any other, and
the hypothesis is discharged where it is used, from what the previous step left
proved.

With that in place, the other state-transition propositions asked for nothing
new. `ST-4` is the loop script once more, with a different invariant,
an `is_valid_vote` lemma saying the vote goes forward and a `try_finalize` lemma
saying where it moves finality. The new proofs are long to write and short to
think: the work is in choosing the invariant and in saying what each call
returns.

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
On the Lean side it is now stated: `NP5.try_finalize_devuelve` carries it as a
hypothesis, in the form "the source is before the target".

**`current_len + 1 + num_empty_slots` is added before the limit is checked.**
The same kind of finding, in `process_block_header`, and it surfaced the same
way: by asking the function to return. With one hash per slot in the history
the sum is `block.slot` and does not overflow; the transition preserves that
invariant. It is not a live bug either. It is told under **`process_slots`
and `process_block_header` do not panic**.

**The trust base is not empty**, and what is in it is set out under **The trust
base** above: nine native axioms that come with the translation, twenty-six
declarations of ours that assert nothing, and three modeling claims we do make.

**`ST-7` holds under a hypothesis that is not established from genesis.** The
theorem asks that the justified checkpoint be in the history and proves that
this is preserved, but not that the first block establishes it. And without
that hypothesis the statement is false of your code, as the test shows.

**`ST-4` is an inductive step with no base case.** Missing is that the genesis
state has its finalized slot not above its justified one; the crate does not
build it.

**The translated functions cannot be executed in Lean.** Lean marks them
`noncomputable`; among other things they depend on the `fmt` axioms that
`.expect()` uses. You can prove things about them, but you cannot run them with
`#eval` to try a concrete case: the evidence that they return what is expected
on a given input is the Rust tests.

**Absence of panic does not cover the whole transition.** The four functions of
`justified_slots_ops` return, under capacity hypotheses; five of the twelve in
`stf.rs` return with no hypothesis; and `process_slots`,
`process_block_header`, `serialize_justifications`, `try_finalize` and
`process_attestations` return under the hypotheses of their section, among
them that the hash, `H256` comparison and the `HashMap` return. The other two,
`process_block` and `state_transition`, keep the "if the function returns"
conditional.

**The bound on roots in `process_attestations` is a sufficient condition, not
an invariant.** It asks that the state's roots plus the block's attestations
do not exceed 262144. The fine bound, that the vote map's roots are distinct
and in the history, is not proved.

**The window invariant assumes a 64-bit `usize`.** The results about where the
window ends carry that hypothesis explicitly. On 32 bits the `as usize` casts
truncate and they do not hold as stated.
