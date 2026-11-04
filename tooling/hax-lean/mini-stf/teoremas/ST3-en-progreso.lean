/- SONDA 5: hacer que la tactica siga.

   Estado: `hax_mvcgen` corre, cierra TODO salvo un objetivo (`vc1.h_lt`), y
   ese objetivo quedo con el cuerpo entero envuelto en un `wp`. La tactica se
   planta porque decide "ya esta" por la forma del objetivo: un `.down` con
   `WP.wp` pero sin `PredTrans.apply` no entra en ninguno de los tres casos
   que reconoce `goalNeedsMvcgen`.

   Si el diagnostico es correcto, largarle `mvcgen` a mano tiene que seguir.

   lake env lean Sondeo.lean
-/
import MiniStf.Extraction
import MiniStf.Verification.ProofObligations
import Hax

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option maxHeartbeats 4000000

namespace Sonda
open mini_stf

abbrev Acc :=
  tipos.State × Std.U64 × mapa.MapaVotos × (core.option.Option stf.Error)

abbrev invJ (s0 : tipos.State) : Std.Usize → Acc → RustM Prop :=
  fun _ acc => ok (s0.latest_justified.slot ≤ acc.1.latest_justified.slot)

/-- `try_finalize` no toca `latest_justified`. Demostrado en la sonda 3. -/
theorem try_finalize_no_toca_justified
    (state state' : tipos.State) (source target : tipos.Checkpoint)
    (j j' : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global)
    (h : stf.try_finalize state source target j rts = ok (state', j')) :
    state'.latest_justified = state.latest_justified := by
  unfold stf.try_finalize at h
  split at h
  · simp_all
  · obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    split at h
    · simp [stubs.metrics.inc_finalizations] at h
      simp_all
    · simp [stubs.metrics.inc_finalizations] at h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      simp only [RustM.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hst, -⟩ := h
      subst hst
      simp_all

/- --------------------------------------------------------------------
   A: hax_mvcgen y despues mvcgen a mano, una vez
   -------------------------------------------------------------------- -/

example
    (s0 : tipos.State)
    (attestations : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (validator_count n : Std.Usize)
    (j0 : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations_loop { start := 0#usize, «end» := n } s0
      attestations validator_count 0#u64 j0 rts core.option.Option.None
    ⦃ ⇓ r => ⌜ (invJ s0 n r).holds ⌝ ⦄ := by
  unfold stf.process_attestations_loop
  apply Hax.loop_range_spec_unsigned (inv := invJ s0)
  · scalar_tac
  · simp [RustM.holds, Triple, WP.wp, PredTrans.apply]
  · intro acc i hi0 hin hinv
    obtain ⟨st, ap, jj, fl⟩ := acc
    have hj : s0.latest_justified.slot ≤ st.latest_justified.slot := by
      simpa [RustM.holds, Triple, WP.wp, PredTrans.apply] using hinv
    clear hinv
    unfold stf.process_attestations_loop.body
    hax_mvcgen
    all_goals try mvcgen
    all_goals try first
      | rfl
      | assumption
      | (simp_all; done)
      | scalar_tac
      | omega
      | (simp_all; omega)
      | (simp_all; scalar_tac)

/- --------------------------------------------------------------------
   B: insistir hasta que no avance mas
   -------------------------------------------------------------------- -/

example
    (s0 : tipos.State)
    (attestations : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (validator_count n : Std.Usize)
    (j0 : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations_loop { start := 0#usize, «end» := n } s0
      attestations validator_count 0#u64 j0 rts core.option.Option.None
    ⦃ ⇓ r => ⌜ (invJ s0 n r).holds ⌝ ⦄ := by
  unfold stf.process_attestations_loop
  apply Hax.loop_range_spec_unsigned (inv := invJ s0)
  · scalar_tac
  · simp [RustM.holds, Triple, WP.wp, PredTrans.apply]
  · intro acc i hi0 hin hinv
    obtain ⟨st, ap, jj, fl⟩ := acc
    have hj : s0.latest_justified.slot ≤ st.latest_justified.slot := by
      simpa [RustM.holds, Triple, WP.wp, PredTrans.apply] using hinv
    clear hinv
    unfold stf.process_attestations_loop.body
    repeat' first
      | rfl
      | assumption
      | scalar_tac
      | omega
      | hax_mvcgen
      | mvcgen
      | (simp_all; done)

end Sonda
