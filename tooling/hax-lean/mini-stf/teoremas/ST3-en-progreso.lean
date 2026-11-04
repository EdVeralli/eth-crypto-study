/- SONDA 8: ST-3 mitad 2, con el puente y los lemas de las funciones.

   Cambio clave respecto de la sonda 6: se usa `Aeneas.Std.loop_spec` en vez
   del de hax. El de hax exige `⇓`, o sea que el cuerpo no falle nunca, lo que
   obliga a demostrar la ausencia de panico en las doce funciones que llama
   (seis con loops propios). El de Aeneas toma una postcondicion completa:
   eligiendo una que tolere falla y divergencia, esas obligaciones se
   descargan solas y el desborde del contador deja de importar.

   Y el enunciado que queda es el correcto: "si termina bien, el slot no
   retrocedio" -- la misma forma condicional que el teorema 2.

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

/- ====================================================================
   El puente: de ecuacion a terna tolerante.

   Es el dual de `bind_da_ok`. Ese abre un bind; este convierte cualquier
   teorema de la forma "si devolvio ok, entonces P" en la terna que `mvcgen`
   sabe usar. Con el, cada teorema que ya tenemos demostrado como ecuacion se
   vuelve un lema `@[spec]` en una linea.
   ==================================================================== -/

theorem triple_mayThrow_of {α : Type} {x : RustM α} {P : α → Prop}
    (h : ∀ v, x = ok v → P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.mayThrow (fun r => ⌜ P r ⌝) ⦄ := by
  cases x with
  | ok v => simp [Triple, WP.wp, PredTrans.apply, h v rfl]
  | fail e => simp [Triple, WP.wp, PredTrans.apply]
  | div => simp [Triple, WP.wp, PredTrans.apply]

/- ====================================================================
   Lemas de las funciones del cuerpo.

   Once de los doce no tienen que decir NADA: el invariante habla solo de
   `latest_justified`, y estas funciones no reciben ni devuelven el estado.
   Alcanza con que `mvcgen` pueda atravesar la llamada.
   ==================================================================== -/

@[local spec]
theorem is_none_spec {T : Type} (o : core.option.Option T) :
    ⦃ ⌜ True ⌝ ⦄
    core.option.Option.is_none o
    ⦃ ⇓ r => ⌜ r = true ↔ o = core.option.Option.None ⌝ ⦄ := by
  unfold core.option.Option.is_none core.option.Option.is_some
  cases o <;> simp [Triple, WP.wp, PredTrans.apply]

@[local spec]
theorem dato_en_spec (a : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (i : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.dato_en a i ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem bits_en_uno_en_spec
    (a : ssz.SszList tipos.AggregatedAttestation 4096#usize) (i : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.bits_en_uno_en a i
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem is_valid_vote_spec (st : tipos.State) (d : tipos.AttestationData) :
    ⦃ ⌜ True ⌝ ⦄ stf.is_valid_vote st d
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem primer_bit_spec
    (a : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (idx desde : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.primer_bit_fuera_de_rango a idx desde
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem votos_vacios_spec (k : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.votos_vacios k
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem poner_si_falta_spec (m : mapa.MapaVotos) (k : tipos.H256)
    (v : alloc.vec.Vec Bool) :
    ⦃ ⌜ True ⌝ ⦄ m.poner_si_falta k v
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem marcar_votos_spec (m : mapa.MapaVotos) (p : Std.Usize)
    (a : ssz.SszList tipos.AggregatedAttestation 4096#usize) (idx : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.marcar_votos m p a idx
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem cuenta_votos_spec (m : mapa.MapaVotos) (p : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ m.cuenta_votos p
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem sin_spec (m : mapa.MapaVotos) (k : tipos.H256) :
    ⦃ ⌜ True ⌝ ⦄ m.sin k ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem div_ceil_spec (a b : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ core.num.Usize.div_ceil a b
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem set_justified_spec (slots : ssz.SszBitlist 262144#usize)
    (fin tgt : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.set_justified slots fin tgt
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

/-- El unico que SI tiene que decir algo. Sale del teorema 3, que ya esta
    demostrado como ecuacion, pasado por el puente. -/
@[local spec]
theorem try_finalize_spec (state : tipos.State) (source target : tipos.Checkpoint)
    (j : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    stf.try_finalize state source target j rts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.1.latest_justified = state.latest_justified ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨st', j'⟩ := v
    exact try_finalize_no_toca_justified state st' source target j j' rts hv)

/- ====================================================================
   ST-3 mitad 2
   ==================================================================== -/

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
    ⦃ PostCond.mayThrow
        (fun r => ⌜ s0.latest_justified.slot ≤ r.1.latest_justified.slot ⌝) ⦄ := by
  unfold stf.process_attestations_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × Acc =>
              s0.latest_justified.slot ≤ x.2.1.latest_justified.slot)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · first
      | exact Nat.lt_wfRel.wf
      | exact wellFounded_lt
      | exact (inferInstance : WellFoundedLT Nat).wf
  · simp
  · intro x hinv
    obtain ⟨iter, st, ap, jj, fl⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    unfold stf.process_attestations_loop.body
    hax_mvcgen
    -- Dos pasadas, no una. Las obligaciones de la rama `cont` tienen la forma
    --     inv r ∧ (rel ... ∨ PostCond.div P)
    -- y hacerlo en una sola tactica con `<;>` exige exito en los dos miembros
    -- a la vez: si falla en uno se cae todo. Separado, el lado de la
    -- divergencia se descarga solo y queda a la vista lo que importa.
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | assumption
      | trivial
      | simp [PostCond.div, PostCond.mayThrow]
      | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
      | (simp_all; done)
      | (simp_all; omega)
      | (simp_all; scalar_tac)
      | omega
      | scalar_tac

end Sonda
