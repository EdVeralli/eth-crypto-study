/- Teoremas escritos a mano sobre las definiciones extraidas.

   hax crea este archivo una vez y despues no lo toca. Es donde van los
   enunciados: la traduccion da las definiciones, los teoremas los pone
   una persona.

   Copia de trabajo: este archivo vive en `teoremas/` del crate (que si se
   commitea) y se copia a `proofs/lean/MiniStf/Verification/` (que no).
-/
-- Importa la extraccion, NO el modulo raiz `MiniStf`: ese importa a
-- `Verification`, asi que `import MiniStf` aca es un ciclo
-- ("bad import 'MiniStf'").
import MiniStf.Extraction
-- `Hax` trae `loop_spec` via Aeneas, `mvcgen` y `PostCond.mayThrow`.
import Hax

-- Los mismos `open` que traen los archivos generados. Sin ellos no resuelven
-- `ok`, `Std.U64` ni `alloc.alloc.Global`.
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

/- ===========================================================================
   Teorema 1: la regla de los numeros pronic

   `slot_is_justifiable_after` decide si un slot se puede justificar con tres
   reglas. La tercera, segun el comentario del codigo de ethlambda:

       // Pronic numbers have the form n(n+1): 2, 6, 12, 20, 30, 42, 56, ...
       // Mathematical insight: For pronic delta = n(n+1), we have:
       //   4*delta + 1 = 4n(n+1) + 1 = (2n+1)^2
       // Check: 4*delta+1 is an odd perfect square

   O sea que el codigo detecta pronics preguntando si `4·delta + 1` es un
   cuadrado perfecto impar, en vez de factorizar. Eso es una afirmacion
   matematica que el comentario enuncia y nadie demostro. Aca se demuestra.
   =========================================================================== -/

theorem pronic_iff_cuadrado (n : ℕ) :
    (∃ m, m * m = 4 * n + 1) ↔ (∃ k, n = k * (k + 1)) := by
  constructor
  · rintro ⟨m, hm⟩
    -- `m` tiene que ser impar, porque `m * m = 4n + 1` es impar
    have hodd : Odd m := by
      have h : Odd (m * m) := by rw [hm]; exact ⟨2 * n, by ring⟩
      exact (Nat.odd_mul.mp h).1
    obtain ⟨k, hk⟩ := hodd
    subst hk
    exact ⟨k, by nlinarith [hm]⟩
  · rintro ⟨k, hk⟩
    exact ⟨2 * k + 1, by subst hk; ring⟩

/- ===========================================================================
   Corolario: el chequeo de paridad del codigo es redundante

   El codigo pregunta DOS cosas sobre `m = 4·delta + 1`: que sea cuadrado
   perfecto Y que sea impar (`m % 2 == 1`). La segunda nunca puede fallar si
   la primera pasa: `4·delta + 1` es impar siempre, asi que su raiz tambien.

   No es un bug -- el resultado es correcto -- pero es una condicion que
   siempre se cumple, y aparecio al escribir el enunciado.
   =========================================================================== -/

theorem chequeo_de_paridad_redundante (n m : ℕ) (h : m * m = 4 * n + 1) :
    m % 2 = 1 := by
  have hodd : Odd m := by
    have h2 : Odd (m * m) := by rw [h]; exact ⟨2 * n, by ring⟩
    exact (Nat.odd_mul.mp h2).1
  exact Nat.odd_iff.mp hodd

/- Control: los primeros pronics son los que dice el comentario. -/
example : (∃ k, 2 = k * (k + 1)) := ⟨1, by norm_num⟩
example : (∃ k, 6 = k * (k + 1)) := ⟨2, by norm_num⟩
example : (∃ k, 12 = k * (k + 1)) := ⟨3, by norm_num⟩
example : (∃ k, 56 = k * (k + 1)) := ⟨7, by norm_num⟩

/- Y la identidad del comentario, instanciada: 4·56 + 1 = 225 = 15². -/
example : 4 * 56 + 1 = 15 * 15 := by norm_num

/- ===========================================================================
   De que dependen los teoremas. Si sale solo los tres estandar de Lean,
   estan limpios: nada de native axioms, nada de agujeros nuestros.
   =========================================================================== -/

#print axioms pronic_iff_cuadrado
#print axioms chequeo_de_paridad_redundante

/- ===========================================================================
   Herramienta: abrir un bind

   El codigo que genera Aeneas es una cadena de binds de `RustM`, que es un
   inductivo con `ok`, `fail` y `div`. Para razonar sobre el hay que ir
   abriendolos: si la secuencia entera termino en `ok`, el primer paso tambien.
   Los casos `fail` y `div` se descartan solos, porque no son `ok`.

   Esto se usa en todos los teoremas sobre funciones generadas, asi que vale
   tenerlo una vez.
   =========================================================================== -/

theorem bind_da_ok {α β : Type} {x : RustM α} {k : α → RustM β} {y : β}
    (h : (x >>= k) = ok y) : ∃ a, x = ok a ∧ k a = ok y := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp at h
  | div => simp at h

/- ===========================================================================
   Teorema 2: la mitad de ST-3 que vive en `try_finalize`

   `ST-3` es una de las 35 proposiciones de NyxFoundation/formal-leanSpec:

       latest_justified.slot y latest_finalized.slot nunca retroceden

   Lo que la hace la vara correcta es que NO la inventamos nosotros, y que la
   suite de ethlambda ya la afirma por ejemplo, en el test
   `latest_justified_does_not_regress_within_block`.

   Tiene dos mitades. Esta es la de la finalidad, que vive en `try_finalize` y
   que el codigo casi regala:

       if source.slot <= state.latest_finalized.slot { return; }
       ...
       state.latest_finalized = source;

   La guarda de arriba ES la propiedad: si el source no avanza, no se toca
   nada; y si se llega a la asignacion, es porque avanza.
   =========================================================================== -/

open mini_stf in
theorem try_finalize_no_retrocede
    (state state' : tipos.State) (source target : tipos.Checkpoint)
    (j j' : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global)
    (h : stf.try_finalize state source target j rts = ok (state', j')) :
    state.latest_finalized.slot ≤ state'.latest_finalized.slot := by
  unfold stf.try_finalize at h
  split at h
  · -- Rama 1: el source no avanza, se devuelve el estado sin tocar.
    simp_all
  · -- Ramas 2 y 3. Antes del `if` hay dos binds que hay que abrir.
    obtain ⟨i, hadd, h⟩ := bind_da_ok h
    obtain ⟨b, hb, h⟩ := bind_da_ok h
    split at h
    · -- Rama 2: hay un slot justificable en el medio, tampoco se toca.
      simp [stubs.metrics.inc_finalizations] at h
      simp_all
    · -- Rama 3: se asigna `latest_finalized := source`. Quedan ocho binds
      -- entre el `if` y el `ok` final; ninguno toca `latest_finalized`, pero
      -- hay que atravesarlos para llegar a la igualdad.
      simp [stubs.metrics.inc_finalizations] at h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      obtain ⟨_, _, h⟩ := bind_da_ok h
      -- Ahora `h` es `ok (<estado nuevo>, _) = ok (state', _)`. Se abre el
      -- constructor y el par para quedarse con la igualdad de estados.
      simp only [RustM.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hst, -⟩ := h
      subst hst
      -- El estado devuelto tiene `latest_finalized := source`, y la guarda de
      -- la rama 1 dice que `source.slot` es mayor. Listo.
      simp_all
      omega

/- ===========================================================================
   Teorema 3: `try_finalize` no toca `latest_justified`

   Companero del anterior, y la pieza que necesita la segunda mitad de ST-3.
   `try_finalize` se llama adentro del loop de `process_attestations`, que es
   donde se mueve `latest_justified`. Para demostrar que ese campo no retrocede
   en el loop hay que saber que `try_finalize` no lo toca.

   El cuerpo generado arma el estado nuevo con
   `latest_justified := state.latest_justified`, asi que sale con la misma
   estructura que el teorema 2.
   =========================================================================== -/

open mini_stf in
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

/- ===========================================================================
   ST-3 mitad 2: nota historica del 4 nov

   Esto es como estaba el 4 nov, ANTES de cerrar la otra mitad. Se deja porque
   explica por que el teorema 4, mas abajo, no usa
   `Hax.loop_range_spec_unsigned`. Lo que aca figura como faltante -- que
   `latest_justified.slot` tampoco retroceda en el loop de
   `process_attestations` -- esta demostrado en los teoremas 4 y 5. El archivo
   de trabajo de ese dia, `teoremas/ST3-en-progreso.lean`, ya no existe.

   Lo que ya esta medido:

   - `Hax.loop_range_spec_unsigned` UNIFICA con el loop generado tal como sale
     de Aeneas. Eso recien quedo posible hoy: hasta el arreglo del `match
     fallo`, el loop descartaba la bandera, el acumulador era una tupla de
     cuatro y el resultado de tres, y el lema exige el mismo tipo en los dos
     lados.
   - Sus tres obligaciones: `h_le` sale con `scalar_tac`, `h_init` con `simp`,
     y `h_step` es la que queda.
   - `hax_mvcgen` sobre `h_step` cierra todo menos un objetivo, `vc1.h_lt`, que
     es la rama donde el loop sigue. Y se planta ahi: deja el cuerpo entero
     envuelto en un `wp`. El motivo es la forma del objetivo, no la dificultad
     -- `goalNeedsMvcgen` reconoce una terna, un `entails` con `wp`, o un
     `.down` con `PredTrans.apply`; lo que queda es un `.down` con `WP.wp` y
     sin `PredTrans.apply`, asi que la tactica cree que ya termino.
   - Insistir con `mvcgen` a mano avanza un paso y vuelve a plantarse en
     `core.option.Option.is_none`, que no se puede decidir mientras la bandera
     sea una variable. Son cuatro `is_none` encadenados.

   Y lo que hay que cambiar, que aparecio al mirarlo con la lente de ternas:

   **El invariante es demasiado debil.** Habla solo del slot justificado, y no
   alcanza, porque el cuerpo hace

       let attestations_processed1 <- acc.2.1 + 1#u64

   y `loop_range_spec_unsigned` exige que el cuerpo NO FALLE NUNCA. Ese `+1`
   puede desbordar. La cota existe -- el contador arranca en 0 y sube como
   maximo uno por vuelta, asi que `attestations_processed <= i`, y con `i < n`
   de la rama `h_lt` queda estrictamente menor que el maximo -- pero hay que
   meterla EN el invariante:

       inv i acc = (s0.latest_justified.slot <= acc.1.latest_justified.slot
                    /\ acc.2.1.val <= i.val)

   Es el segundo desborde que aparece en el dia, y los dos por la misma razon:
   la terna de Hoare exige que el programa no falle y la forma ecuacional no.
   El otro es `source.slot + 1` en `try_finalize`.
   =========================================================================== -/


/- ===========================================================================
   Teorema 4: ST-3 mitad 2 -- `latest_justified` no retrocede en el loop

   Con esto quedan demostradas las dos mitades de `ST-3`, cada una sobre el
   componente donde se mueve su campo. La proposicion del catalogo esta
   enunciada sobre `State.transition` entera: eso es el teorema 6, al final
   de este archivo.

   El enunciado es condicional a que la llamada devuelva `ok`, igual que el
   teorema 2:

       si `process_attestations_loop` devuelve `ok`, el slot justificado del
       resultado no es menor que el que habia al entrar.

   Ojo con que `ok` es ese. Es el de `RustM`: la corrida no entro en panico
   (`fail`) ni dejo de terminar (`div`). NO es el `Ok` de Rust. Un bloque
   rechazado es `ok (Err e, estado)` y esta cubierto por el teorema. Lo que
   queda afuera son los panicos -- un desborde, un indice fuera de rango -- y
   eso es un limite real: un panico no rechaza el bloque, tira el nodo.
   Demostrar que no los hay es otro teorema, mucho mas grande (ver el punto 1
   de abajo).

   Dos decisiones que costaron el dia y vale dejar escritas.

   1. Se usa `Aeneas.Std.loop_spec`, NO `Hax.loop_range_spec_unsigned`.

      El de hax enuncia la obligacion del paso con `⇓`, que exige que el
      cuerpo no falle NUNCA. Eso convierte este teorema en uno mucho mas
      grande: hay que demostrar ausencia de panico en las doce funciones que
      el cuerpo llama, y seis tienen loops propios. El de Aeneas toma una
      postcondicion completa, con ramas de falla y divergencia; eligiendo
      `PostCond.mayThrow`, esas obligaciones se descargan solas, el desborde
      de `attestations_processed + 1` deja de importar, y tolerando la
      divergencia no hace falta medida de terminacion.

   2. El puente `triple_mayThrow_of` es el dual de `bind_da_ok`.

      `bind_da_ok` abre un bind; este convierte cualquier teorema que ya
      tengamos COMO ECUACION en el lema `@[spec]` que `mvcgen` sabe usar. De
      ahi que `try_finalize_spec` salga en una linea del teorema 3, sin
      rehacer la demostracion.

   Once de los trece lemas `@[spec]` de este bloque no dicen nada: el
   invariante habla solo de `latest_justified` y esas funciones no reciben ni
   devuelven el estado, asi que alcanza con que la tactica pueda atravesar la
   llamada. Los dos con contenido son `is_none_spec` y `try_finalize_spec`.

   Y donde esta la propiedad, al final: `mvcgen` genera mas de 250
   condiciones de verificacion y deja dieciocho. Se cierran de dos formas --
   por transitividad (`hinv` da `s0 <= st`, la guarda del `if` da
   `st <= target`, y `try_finalize_spec` da que no movio el campo) o por
   absurdo, porque varias ramas son inalcanzables.
   =========================================================================== -/

namespace ST3
open mini_stf
open Std.Tactic

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

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

   Once de los trece no tienen que decir NADA: el invariante habla solo de
   `latest_justified`, y estas funciones no reciben ni devuelven el estado.
   Alcanza con que `mvcgen` pueda atravesar la llamada. Los otros dos son
   `is_none_spec` y `try_finalize_spec`.
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

theorem process_attestations_loop_no_retrocede
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

    -- Tercera pasada: lo que queda es `inv r` con todo a la vista. Dos formas:
    --
    --   * transitividad -- `hinv` da `s0 <= st`, la guarda del `if` da
    --     `st <= target`, y `try_finalize_spec` da que try_finalize no movio
    --     el campo. El objetivo esta sobre los valores con la coercion y las
    --     hipotesis sobre los u64, asi que `omega` no cruza solo: `scalar_tac`
    --     si.
    --   * absurdo -- varias ramas son inalcanzables, con un
    --     `r = true` junto a un `r = true <-> Some _ = None`.
    --
    -- `grind` sirve para las dos, y aca ya no explota: los objetivos son
    -- chicos y de primer orden, no un `wp` entero.
    all_goals try first
      | scalar_tac
      | grind
      | (simp_all; scalar_tac)
      | (simp_all; grind)
      | (simp_all; omega)

end ST3


/- ===========================================================================
   Teorema 5: ST-3 mitad 2 sobre `process_attestations` ENTERA

   El teorema 4 habla del loop. Este habla de la funcion que ethlambda llama:

       si `process_attestations` termina bien, el slot justificado del estado
       resultante no es menor que el que habia al entrar.

   Con esto la mitad de la justificacion queda demostrada sobre la funcion
   entera, no solo sobre el loop.

   Dos notas de metodo.

   El primer intento fue demostrarla como ecuacion, peleando con los binds
   como en los teoremas 2 y 3. No se puede asi: el `let` que desarma la tupla
   que devuelve el loop es un `match` sobre el par, `split` no lo atraviesa, y
   ni `simp only []` ni `dsimp only` lo reducen. Con `mvcgen` sale, porque
   maneja sola los cuatro `if` del preambulo y el `match` de la bandera.

   Y quedan los DOS puentes, que juntos valen mas que cada uno:

       triple_mayThrow_of  : ecuacion -> terna
       of_triple_mayThrow  : terna   -> ecuacion

   Con los dos se demuestra del lado que conviene y se enuncia del lado que se
   lee. `serialize_spec` sale del lema ecuacional por el primero; el enunciado
   final de este teorema sale de la terna por el segundo.
   =========================================================================== -/

namespace ST3
open mini_stf
open Std.Tactic

/- ====================================================================
   1. serialize_justifications no toca latest_justified

   Sale por construccion: devuelve `{state with ...}` tocando otros dos campos.
   ==================================================================== -/

theorem serialize_no_toca_justified
    (state state' : tipos.State) (j : mapa.MapaVotos) (vc : Std.Usize)
    (h : stf.serialize_justifications state j vc = ok state') :
    state'.latest_justified = state.latest_justified := by
  unfold stf.serialize_justifications at h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  simp only [RustM.ok.injEq] at h
  subst h
  rfl

/- ====================================================================
   2. El puente al reves: de terna tolerante a ecuacion.

   `triple_mayThrow_of` va de ecuacion a terna; este vuelve. Con los dos
   se puede demostrar donde convenga y enunciar donde se lea mejor.
   ==================================================================== -/

theorem of_triple_mayThrow {α : Type} {x : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.mayThrow (fun r => ⌜ P r ⌝) ⦄)
    {v : α} (hv : x = ok v) : P v := by
  subst hv
  simpa [Triple, WP.wp, PredTrans.apply] using h

/- ====================================================================
   3. Lemas del preambulo. Ninguno dice nada: el invariante habla solo de
      `latest_justified` y estas funciones no lo tocan.
   ==================================================================== -/

@[local spec]
theorem timer_spec :
    ⦃ ⌜ True ⌝ ⦄ stubs.metrics.time_attestations_processing
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem inc_procesadas_spec (c : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ stubs.metrics.inc_attestations_processed c
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem contar_datos_spec
    (a : ssz.SszList tipos.AggregatedAttestation 4096#usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.contar_datos_distintos a
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem hay_raiz_cero_spec (r : ssz.SszList tipos.H256 262144#usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.hay_raiz_cero r
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem construir_mapa_spec (st : tipos.State) (vc : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.construir_mapa_de_votos st vc
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem construir_rts_spec (st : tipos.State) :
    ⦃ ⌜ True ⌝ ⦄ stf.construir_root_to_slot st
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem ssz_len_spec {T : Type} {N : Std.Usize} (l : ssz.SszList T N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszList.len l
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec]
theorem bitlist_len_spec {N : Std.Usize} (b : ssz.SszBitlist N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.len b
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

/-- El unico del preambulo con contenido: no mueve `latest_justified`. -/
@[local spec]
theorem serialize_spec (st : tipos.State) (j : mapa.MapaVotos)
    (vc : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.serialize_justifications st j vc
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.latest_justified = st.latest_justified ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => serialize_no_toca_justified st v j vc hv)

/- Y el teorema 4, el del loop, como lema. -/
attribute [local spec] process_attestations_loop_no_retrocede

/- ====================================================================
   4. ST-3 sobre `process_attestations`
   ==================================================================== -/

theorem process_attestations_spec (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations state atts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_justified.slot ≤ r.2.latest_justified.slot ⌝) ⦄ := by
  unfold stf.process_attestations
  hax_mvcgen
  all_goals try (refine ⟨?_, Or.inr ?_⟩)
  all_goals try first
    | rfl
    | assumption
    | trivial
    | simp [PostCond.div, PostCond.mayThrow]
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | (simp_all; done)
    | scalar_tac
    | omega
  all_goals try first
    | scalar_tac
    | grind
    | (simp_all; scalar_tac)
    | (simp_all; grind)
    | (simp_all; omega)

/-- La misma cosa como ecuacion, que es como se lee. -/
theorem process_attestations_no_retrocede
    (state state' : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (res : core.result.Result Unit stf.Error)
    (h : stf.process_attestations state atts = ok (res, state')) :
    state.latest_justified.slot ≤ state'.latest_justified.slot :=
  of_triple_mayThrow (process_attestations_spec state atts) h

end ST3


/- ===========================================================================
   Teorema 6: ST-3 sobre `state_transition` ENTERA (15 nov 2026)

   Hasta aca habia dos mitades, cada una sobre el componente donde se mueve
   su campo: la justificacion sobre `process_attestations` y la finalidad
   sobre `try_finalize`. Faltaban tres lemas para subirlas a la transicion de
   un bloque:

     1. `process_slots` no toca los checkpoints;
     2. `process_block_header` no los baja;
     3. la finalidad llevada a traves del loop de attestations.

   Estan los tres, y la composicion. El resultado final es
   `ST3.state_transition_no_retrocede`, al fondo de este bloque.
   =========================================================================== -/

namespace ST3
open mini_stf
open Std.Tactic

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

/- ====================================================================
   Lema 1: `process_slots` no toca los checkpoints.

   Avanza `slot` y completa el `state_root` del header; el resto del estado
   sale igual. Se demuestra como ecuacion, abriendo los binds.
   ==================================================================== -/

theorem process_slots_no_toca_checkpoints
    (state state' : tipos.State) (t : Std.U64)
    (res : core.result.Result Unit stf.Error)
    (h : stf.process_slots state t = ok (res, state')) :
    state'.latest_justified = state.latest_justified ∧
    state'.latest_finalized = state.latest_finalized := by
  unfold stf.process_slots at h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  split at h
  · simp only [RustM.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hst⟩ := h
    subst hst
    exact ⟨rfl, rfl⟩
  · obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    simp only [RustM.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hst⟩ := h
    subst hst
    exact ⟨rfl, rfl⟩

/- ====================================================================
   `serialize_justifications` tampoco toca `latest_finalized`.
   Gemelo de `serialize_no_toca_justified`.
   ==================================================================== -/

theorem serialize_no_toca_finalized
    (state state' : tipos.State) (j : mapa.MapaVotos) (vc : Std.Usize)
    (h : stf.serialize_justifications state j vc = ok state') :
    state'.latest_finalized = state.latest_finalized := by
  unfold stf.serialize_justifications at h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  simp only [RustM.ok.injEq] at h
  subst h
  rfl

end ST3

/- ====================================================================
   Lema 3: la finalidad a traves del loop de attestations.

   El teorema 2 dice que `try_finalize` suelta no baja `latest_finalized`.
   Aca se lleva a `process_attestations`, que es quien la llama. Es la misma
   maquinaria del teorema 4 con otro invariante: el unico lugar del cuerpo
   donde el estado cambia es la llamada a `try_finalize`, y el
   `{ state with latest_justified := .., justified_slots := .. }` que se le
   pasa no toca `latest_finalized`.

   Los lemas `@[local spec]` del teorema 4 dejaron de valer al cerrar su
   `namespace`, asi que se vuelven a activar. El de `try_finalize` es otro:
   `try_finalize_spec` hablaba de `latest_justified`; este habla de
   `latest_finalized`. Si los dos estuvieran activos a la vez, `mvcgen`
   elegiria uno solo.
   ==================================================================== -/

namespace ST3F
open mini_stf
open Std.Tactic
open ST3

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

attribute [local spec] is_none_spec dato_en_spec bits_en_uno_en_spec
  is_valid_vote_spec primer_bit_spec votos_vacios_spec poner_si_falta_spec
  marcar_votos_spec cuenta_votos_spec sin_spec div_ceil_spec set_justified_spec

@[local spec]
theorem try_finalize_fin_spec (state : tipos.State)
    (source target : tipos.Checkpoint) (j : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    stf.try_finalize state source target j rts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_finalized.slot ≤ r.1.latest_finalized.slot ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨st', j'⟩ := v
    exact try_finalize_no_retrocede state st' source target j j' rts hv)

theorem process_attestations_loop_fin_no_retrocede
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
        (fun r => ⌜ s0.latest_finalized.slot ≤ r.1.latest_finalized.slot ⌝) ⦄ := by
  unfold stf.process_attestations_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × Acc =>
              s0.latest_finalized.slot ≤ x.2.1.latest_finalized.slot)
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
    all_goals try first
      | scalar_tac
      | grind
      | (simp_all; scalar_tac)
      | (simp_all; grind)
      | (simp_all; omega)


/- ====================================================================
   La finalidad sobre `process_attestations` entera.
   ==================================================================== -/

attribute [local spec] timer_spec inc_procesadas_spec contar_datos_spec
  hay_raiz_cero_spec construir_mapa_spec construir_rts_spec ssz_len_spec
  bitlist_len_spec

@[local spec]
theorem serialize_fin_spec (st : tipos.State) (j : mapa.MapaVotos)
    (vc : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.serialize_justifications st j vc
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.latest_finalized = st.latest_finalized ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => serialize_no_toca_finalized st v j vc hv)

attribute [local spec] process_attestations_loop_fin_no_retrocede

theorem process_attestations_fin_spec (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations state atts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_finalized.slot ≤ r.2.latest_finalized.slot ⌝) ⦄ := by
  unfold stf.process_attestations
  hax_mvcgen
  all_goals try (refine ⟨?_, Or.inr ?_⟩)
  all_goals try first
    | rfl
    | assumption
    | trivial
    | simp [PostCond.div, PostCond.mayThrow]
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | (simp_all; done)
    | scalar_tac
    | omega
  all_goals try first
    | scalar_tac
    | grind
    | (simp_all; scalar_tac)
    | (simp_all; grind)
    | (simp_all; omega)

theorem process_attestations_fin_no_retrocede
    (state state' : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (res : core.result.Result Unit stf.Error)
    (h : stf.process_attestations state atts = ok (res, state')) :
    state.latest_finalized.slot ≤ state'.latest_finalized.slot :=
  of_triple_mayThrow (process_attestations_fin_spec state atts) h

end ST3F

/- ====================================================================
   Lema 2: `process_block_header` no mueve el slot de ningun checkpoint.

   Aca estaba la trampa anunciada: el anclaje del genesis. En el primer
   bloque despues del genesis el codigo de ethlambda hace

       state.latest_justified.root = parent_root;
       state.latest_finalized.root = parent_root;

   Escribe la RAIZ, no el slot. Por eso el enunciado sobre los slots vale
   para cualquier estado, sin hipotesis extra de estado bien formado. Lo que
   NO vale es la igualdad del checkpoint entero: la raiz si cambia.

   Catorce lemas triviales para que `mvcgen` atraviese las llamadas. Ninguna
   recibe el estado ni lo devuelve, asi que no tienen nada que decir. Con
   ellos `hax_mvcgen` cierra solo todas las condiciones.
   ==================================================================== -/

namespace ST3H
open mini_stf
open Std.Tactic
open ST3

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

attribute [local spec] ssz_len_spec

@[local spec] theorem current_proposer_spec (a b : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ stf.current_proposer a b ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem ok_or_spec {T E : Type} (o : core.option.Option T) (e : E) :
    ⦃ ⌜ True ⌝ ⦄ core.option.Option.ok_or o e ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem branch_spec {T E : Type} (r : core.result.Result T E) :
    ⦃ ⌜ True ⌝ ⦄ core.result.Result.Insts.CoreOpsTry_traitTry.branch r
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem header_hash_spec (h : tipos.BlockHeader) :
    ⦃ ⌜ True ⌝ ⦄ tipos.BlockHeader.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root h
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem ne_default_spec {S R : Type} (inst : core.cmp.PartialEq S R)
    (a : S) (b : R) :
    ⦃ ⌜ True ⌝ ⦄ core.cmp.PartialEq.ne.default inst a b
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem take_spec {T : Type} (inst : core.default.Default T) (x : T) :
    ⦃ ⌜ True ⌝ ⦄ core.mem.take inst x ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem into_inner_spec {T : Type} {N : Std.Usize} (l : ssz.SszList T N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszList.into_inner l ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem push_spec {T : Type} (v : alloc.vec.Vec T) (x : T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.push v x ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem header_loop_spec (it : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec tipos.H256) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_block_header_loop it v
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem try_from_spec {T : Type} (N : Std.Usize) (v : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄
    ssz.SszList.Insts.CoreConvertTryFromVecFueraDeCapacidad.try_from N v
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem expect_spec {T E : Type} (inst : core.fmt.Debug E)
    (r : core.result.Result T E) (s : Str) :
    ⦃ ⌜ True ⌝ ⦄ core.result.Result.expect inst r s
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem extend_spec (b : ssz.SszBitlist 262144#usize) (x y : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.extend_to_slot b x y
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem body_hash_spec (b : tipos.BlockBody) :
    ⦃ ⌜ True ⌝ ⦄ tipos.BlockBody.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root b
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem from_residual_spec (T : Type) {E F : Type}
    (inst : core.convert.From F E)
    (r : core.result.Result core.convert.Infallible E) :
    ⦃ ⌜ True ⌝ ⦄
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T inst r
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

theorem process_block_header_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block_header state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.2.latest_justified.slot = state.latest_justified.slot ∧
                    r.2.latest_finalized.slot = state.latest_finalized.slot ⌝) ⦄ := by
  unfold stf.process_block_header
  hax_mvcgen
  all_goals try first
    | rfl
    | assumption
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | (simp_all; done)
    | scalar_tac
    | grind

theorem process_block_header_no_mueve_slots
    (state state' : tipos.State) (block : tipos.Block)
    (res : core.result.Result Unit stf.Error)
    (h : stf.process_block_header state block = ok (res, state')) :
    state'.latest_justified.slot = state.latest_justified.slot ∧
    state'.latest_finalized.slot = state.latest_finalized.slot :=
  of_triple_mayThrow (process_block_header_spec state block) h

end ST3H

/- ====================================================================
   Composicion: `process_block` y `state_transition`.

   `process_block` = header (los slots quedan igual) y despues attestations
   (ninguno de los dos retrocede). `state_transition` = `process_slots` (no
   toca los checkpoints), `process_block`, y la comparacion de la raiz del
   estado, que no modifica nada.
   ==================================================================== -/

namespace ST3T
open mini_stf
open Std.Tactic
open ST3

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

attribute [local spec] ST3H.branch_spec ST3H.from_residual_spec
  ST3H.ne_default_spec

@[local spec] theorem time_block_spec :
    ⦃ ⌜ True ⌝ ⦄ stubs.metrics.time_block_processing
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem time_transition_spec :
    ⦃ ⌜ True ⌝ ⦄ stubs.metrics.time_state_transition
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

@[local spec] theorem state_hash_spec (s : tipos.State) :
    ⦃ ⌜ True ⌝ ⦄ tipos.State.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root s
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

attribute [local spec] ST3H.process_block_header_spec

/-- Las dos mitades de ST-3 sobre `process_attestations`, juntas. -/
@[local spec] theorem process_attestations_ambas_spec (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations state atts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_justified.slot ≤ r.2.latest_justified.slot ∧
                    state.latest_finalized.slot ≤ r.2.latest_finalized.slot ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨res, st'⟩ := v
    exact ⟨process_attestations_no_retrocede state st' atts res hv,
           ST3F.process_attestations_fin_no_retrocede state st' atts res hv⟩)

theorem process_block_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_justified.slot ≤ r.2.latest_justified.slot ∧
                    state.latest_finalized.slot ≤ r.2.latest_finalized.slot ⌝) ⦄ := by
  unfold stf.process_block
  hax_mvcgen
  all_goals try first
    | rfl
    | assumption
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | (simp_all; done)
    | scalar_tac
    | grind
    | (simp_all; scalar_tac)
    | (simp_all; grind)

theorem process_block_no_retrocede
    (state state' : tipos.State) (block : tipos.Block)
    (res : core.result.Result Unit stf.Error)
    (h : stf.process_block state block = ok (res, state')) :
    state.latest_justified.slot ≤ state'.latest_justified.slot ∧
    state.latest_finalized.slot ≤ state'.latest_finalized.slot :=
  of_triple_mayThrow (process_block_spec state block) h

@[local spec] theorem process_slots_spec (state : tipos.State) (t : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_slots state t
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.2.latest_justified = state.latest_justified ∧
                    r.2.latest_finalized = state.latest_finalized ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨res, st'⟩ := v
    exact process_slots_no_toca_checkpoints state st' t res hv)

attribute [local spec] process_block_spec

theorem state_transition_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.state_transition state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_justified.slot ≤ r.2.latest_justified.slot ∧
                    state.latest_finalized.slot ≤ r.2.latest_finalized.slot ⌝) ⦄ := by
  unfold stf.state_transition
  hax_mvcgen
  all_goals try first
    | rfl
    | assumption
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | (simp_all; done)
    | scalar_tac
    | grind
    | (simp_all; scalar_tac)
    | (simp_all; grind)

end ST3T

/-- Teorema 6: `ST-3` sobre la transicion entera de un bloque.

    Si `state_transition` devuelve `ok` -- acepte el bloque o lo rechace --,
    ni el slot justificado ni el finalizado del estado resultante son menores
    que los de entrada. Es el `ok` de `RustM`: quedan afuera los panicos y la
    no terminacion, igual que en los teoremas 2 a 5. -/
theorem ST3.state_transition_no_retrocede
    (state state' : mini_stf.tipos.State) (block : mini_stf.tipos.Block)
    (res : core.result.Result Unit mini_stf.stf.Error)
    (h : mini_stf.stf.state_transition state block = ok (res, state')) :
    state.latest_justified.slot ≤ state'.latest_justified.slot ∧
    state.latest_finalized.slot ≤ state'.latest_finalized.slot :=
  ST3.of_triple_mayThrow (ST3T.state_transition_spec state block) h

/- ===========================================================================
   Teorema 7: ST-7 sobre `state_transition` ENTERA (15 nov 2026)

   ST-3 acota solo los SLOTS de los checkpoints. Deja pasar una transicion que
   le cambie la raiz a un checkpoint sin moverlo de slot. ST-7 cierra eso:
   cada checkpoint queda igual ENTERO, raiz incluida, o pasa a un slot
   estrictamente mayor.

   En el modelo del catalogo vale para cualquier estado posterior al genesis,
   porque la especificacion compara con `>` estricto
   (`Checkpoint.advance_to`). En ethlambda NO vale asi: usa

       std::cmp::max_by_key(state.latest_justified, target, |c| c.slot)

   que ante un empate de slots devuelve el SEGUNDO argumento, el target. Con
   un estado en que la raiz justificada no es la que el historial guarda en
   ese slot, la raiz cambia sin que el slot se mueva. Lo muestra el test
   `same_slot_root_swap_needs_a_justified_root_off_the_chain` de src/stf.rs.

   Lo que si vale, y es lo que se demuestra aca: si el checkpoint justificado
   esta en el historial (`EnElHistorial`), no hay cambio de raiz en el mismo
   slot, y `EnElHistorial` se conserva. La razon NO es la de la
   especificacion: un voto solo cuenta si su target coincide con el historial
   (`attestation_data_matches_chain`), asi que un target que empata en slot
   con el justificado tiene la misma raiz, y entonces es el mismo checkpoint.

   La mitad de la finalidad no necesita esa hipotesis: `try_finalize` asigna
   solo cuando `source.slot` es estrictamente mayor.

   Piezas:
     1. la igualdad traducida de `H256` es la igualdad (un loop de 32 bytes);
     2. voto valido => target en el historial;
     3. el loop de attestations, con un invariante de cuatro partes;
     4. `process_block_header` fuera del anclaje del genesis: los checkpoints
        quedan enteros y el historial viejo es prefijo del nuevo. Para esto
        hizo falta que `core.mem.take` dejara de ser un axioma (ver
        supuestos/FunsExternal.lean);
     5. la composicion por `process_block` hasta `state_transition`.

   Lo que NO se demuestra: que el primer bloque despues del genesis deje el
   estado cumpliendo `EnElHistorial`. Es el lema que falta para decir "vale
   en todo estado alcanzable desde el genesis". La otra hipotesis, que
   `latest_block_header.slot` sea distinto de cero, si se conserva: esta en
   el teorema 8 (`ST2.state_transition_conserva_no_genesis`).
   =========================================================================== -/

namespace ST7
open mini_stf
open Std.Tactic
open ST3

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

theorem array_eq_loop_spec (a b : Array Std.U8 32#usize) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreCmpPartialEqArray.eq_loop
      core.U8.Insts.CoreCmpPartialEqU8 a b 0#usize
    ⦃ PostCond.mayThrow (fun r => ⌜ r = true → a = b ⌝) ⦄ := by
  unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop
  apply Aeneas.Std.loop_spec
    (inv := fun i : Std.Usize => ∀ k : Nat, k < i.val → a.val[k]? = b.val[k]?)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · simp
  · intro i hinv
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body
    simp only [core.U8.Insts.CoreCmpPartialEqU8]
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | trivial
      | simp [PostCond.div, PostCond.mayThrow]
    -- Rama `cont`: el invariante para i+1.
    · rename_i hlt ra hra rb hrb heq r hr
      obtain ⟨hia, rfl⟩ := hra
      obtain ⟨hib, rfl⟩ := hrb
      intro k hk
      by_cases hki : k < i.val
      · exact hinv k hki
      · have hk' : k = i.val := by scalar_tac
        subst hk'
        have e1 : (a.to_slice).val = a.val := rfl
        have e2 : (b.to_slice).val = b.val := rfl
        have la : i.val < a.val.length := by scalar_tac
        have lb : i.val < b.val.length := by scalar_tac
        rw [List.getElem?_eq_getElem la, List.getElem?_eq_getElem lb]
        simp only [beq_iff_eq] at heq
        simpa [e1, e2] using heq
    -- Rama `done false`: nada que probar.
    · simp [PostCond.okAssertion]
    -- Rama `done true`: i >= 32 y todo el prefijo coincide.
    · simp only [PostCond.okAssertion]
      intro _
      have ha : a.val.length = 32 := by scalar_tac
      have hb : b.val.length = 32 := by scalar_tac
      apply Subtype.ext
      apply List.ext_getElem?
      intro k
      by_cases hk : k < 32
      · exact hinv k (by scalar_tac)
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- La igualdad traducida de `H256` es la igualdad. -/
theorem h256_eq_true (a b : tipos.H256)
    (h : tipos.H256.Insts.CoreCmpPartialEqH256.eq a b = ok true) : a = b := by
  unfold tipos.H256.Insts.CoreCmpPartialEqH256.eq at h
  exact of_triple_mayThrow (array_eq_loop_spec a b) h rfl

/-- `try_finalize`: la finalidad queda igual ENTERA o avanza estrictamente;
    el historial de hashes no se toca. -/
theorem try_finalize_adelante
    (state state' : tipos.State) (source target : tipos.Checkpoint)
    (j j' : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global)
    (h : stf.try_finalize state source target j rts = ok (state', j')) :
    (state'.latest_finalized = state.latest_finalized ∨
      state.latest_finalized.slot < state'.latest_finalized.slot) ∧
    state'.historical_block_hashes = state.historical_block_hashes := by
  unfold stf.try_finalize at h
  split at h
  · simp_all
  · obtain ⟨i, hadd, h⟩ := bind_da_ok h
    obtain ⟨b, hb, h⟩ := bind_da_ok h
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
      refine ⟨Or.inr ?_, rfl⟩
      simp_all

/-- `process_slots`: no toca checkpoints, ni el historial, ni el slot del
    ultimo header. -/
theorem process_slots_no_toca
    (state state' : tipos.State) (t : Std.U64)
    (res : core.result.Result Unit stf.Error)
    (h : stf.process_slots state t = ok (res, state')) :
    state'.latest_justified = state.latest_justified ∧
    state'.latest_finalized = state.latest_finalized ∧
    state'.historical_block_hashes = state.historical_block_hashes ∧
    state'.latest_block_header.slot = state.latest_block_header.slot := by
  unfold stf.process_slots at h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  split at h
  · simp only [RustM.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hst⟩ := h
    subst hst
    exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    simp only [RustM.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hst⟩ := h
    subst hst
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem serialize_no_toca_historial
    (state state' : tipos.State) (j : mapa.MapaVotos) (vc : Std.Usize)
    (h : stf.serialize_justifications state j vc = ok state') :
    state'.historical_block_hashes = state.historical_block_hashes := by
  unfold stf.serialize_justifications at h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  simp only [RustM.ok.injEq] at h
  subst h
  rfl


/- ====================================================================
   Voto valido => la raiz del target es la del historial en ese slot.
   ==================================================================== -/

/-- El checkpoint `c` esta en el historial: en la posicion de su slot,
    `historical_block_hashes` guarda su raiz. Se enuncia con el mismo `cast` que
    usa el codigo traducido, para no razonar sobre el ancho de `usize`. -/
def EnElHistorial (hist : ssz.SszList tipos.H256 262144#usize)
    (c : tipos.Checkpoint) : Prop :=
  hist.items.val[(UScalar.cast .Usize c.slot).val]? = some c.root

theorem h256_eq_spec (a b : tipos.H256) :
    ⦃ ⌜ True ⌝ ⦄ tipos.H256.Insts.CoreCmpPartialEqH256.eq a b
    ⦃ PostCond.mayThrow (fun r => ⌜ r = true → a = b ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    intro hvt; subst hvt; exact h256_eq_true a b hv)

theorem slice_len_spec {T : Type} (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄ core.slice.Slice.len s ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

section
attribute [local spec] h256_eq_spec slice_len_spec

theorem matches_chain_spec (s : Slice tipos.H256) (d : tipos.AttestationData) :
    ⦃ ⌜ True ⌝ ⦄ stf.attestation_data_matches_chain s d
    ⦃ PostCond.mayThrow (fun r => ⌜ r = true →
        s.val[(UScalar.cast .Usize d.target.slot).val]? = some d.target.root ⌝) ⦄ := by
  unfold stf.attestation_data_matches_chain
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | (simp_all; done)
    | grind
end

theorem ssz_deref_spec {T : Type} {N : Std.Usize} (l : ssz.SszList T N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszList.Insts.CoreOpsDerefDerefSlice.deref l
    ⦃ PostCond.mayThrow (fun r => ⌜ r.val = l.items.val ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    simp [ssz.SszList.Insts.CoreOpsDerefDerefSlice.deref,
      alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
      rust_primitives.sequence.seq_to_slice] at hv
    subst hv; rfl)

theorem is_slot_justified_spec (b : ssz.SszBitlist 262144#usize) (x y : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.is_slot_justified b x y
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

theorem justifiable_spec (x y : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ stf.slot_is_justifiable_after x y
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

/-- `from_residual` nunca devuelve `Ok`: o entra en panico o devuelve `Err`. -/
theorem from_residual_err_spec (T : Type) {E F : Type}
    (inst : core.convert.From F E)
    (r : core.result.Result core.convert.Infallible E) :
    ⦃ ⌜ True ⌝ ⦄
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T inst r
    ⦃ PostCond.mayThrow (fun res => ⌜ ∀ v, res ≠ core.result.Result.Ok v ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual at hv
    cases r with
    | Ok x => simp [core.panicking.internal.panic] at hv
    | Err e =>
      obtain ⟨t, _, hv⟩ := bind_da_ok hv
      simp only [RustM.ok.injEq] at hv
      subst hv
      intro v h
      cases h)

section
attribute [local spec] ssz_deref_spec is_slot_justified_spec justifiable_spec
  from_residual_err_spec matches_chain_spec ST3H.branch_spec

/-- Un voto que `is_valid_vote` acepta tiene su target en el historial. -/
theorem is_valid_vote_historial_spec (st : tipos.State) (d : tipos.AttestationData) :
    ⦃ ⌜ True ⌝ ⦄ stf.is_valid_vote st d
    ⦃ PostCond.mayThrow (fun r => ⌜ r = core.result.Result.Ok true →
        EnElHistorial st.historical_block_hashes d.target ⌝) ⦄ := by
  unfold stf.is_valid_vote
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | (simp_all [EnElHistorial]; done)
end

/- ====================================================================
   El loop de attestations.
   ==================================================================== -/

/-- "Igual entero, o estrictamente hacia adelante": la forma de ST-7. -/
def Adelante (viejo nuevo : tipos.Checkpoint) : Prop :=
  nuevo = viejo ∨ viejo.slot < nuevo.slot

/-- El paso de justificacion. Si el target empata en slot con el justificado
    actual, los dos estan en el historial en el MISMO slot, asi que tienen la
    misma raiz y son el mismo checkpoint: no hay cambio. Si no empata, el
    slot sube. -/
theorem adelante_al_target (hist : ssz.SszList tipos.H256 262144#usize)
    (lj0 lj tgt : tipos.Checkpoint)
    (h0 : Adelante lj0 lj) (hlj : EnElHistorial hist lj) (htg : EnElHistorial hist tgt)
    (hge : tgt.slot ≥ lj.slot) : Adelante lj0 tgt := by
  by_cases heq : tgt.slot = lj.slot
  · have hig : tgt = lj := by
      unfold EnElHistorial at hlj htg
      rw [heq] at htg
      rw [hlj] at htg
      have hr : lj.root = tgt.root := Option.some.inj htg
      cases tgt; cases lj; simp_all
    rw [hig]; exact h0
  · right
    rcases h0 with h0 | h0
    · subst h0; scalar_tac
    · scalar_tac

theorem adelante_trans {a b c : tipos.Checkpoint}
    (h1 : Adelante a b) (h2 : Adelante b c) : Adelante a c := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left; rw [h2, h1]
  · right; rw [← h1]; exact h2
  · right; rw [h2]; exact h1
  · right; scalar_tac

/-- Cierre de la rama en que el target empata o supera al justificado. -/
theorem cierre_si (s0 st r : tipos.State) (tgt : tipos.Checkpoint) (v : Bool)
    (res : core.result.Result Bool stf.Error)
    (hj : Adelante s0.latest_justified st.latest_justified)
    (hf : Adelante s0.latest_finalized st.latest_finalized)
    (hh : st.historical_block_hashes = s0.historical_block_hashes)
    (hc : EnElHistorial st.historical_block_hashes st.latest_justified)
    (hvoto : res = core.result.Result.Ok true →
               EnElHistorial st.historical_block_hashes tgt)
    (hres : res = core.result.Result.Ok v) (hv : v = true)
    (hge : tgt.slot ≥ st.latest_justified.slot)
    (hfin : r.latest_justified = { root := tgt.root, slot := tgt.slot } ∧
            Adelante st.latest_finalized r.latest_finalized ∧
            r.historical_block_hashes = st.historical_block_hashes) :
    Adelante s0.latest_justified r.latest_justified ∧
    Adelante s0.latest_finalized r.latest_finalized ∧
    r.historical_block_hashes = s0.historical_block_hashes ∧
    EnElHistorial r.historical_block_hashes r.latest_justified := by
  obtain ⟨e1, e2, e3⟩ := hfin
  have htg := hvoto (by rw [hres, hv])
  have etgt : ({ root := tgt.root, slot := tgt.slot } : tipos.Checkpoint) = tgt := by
    cases tgt; rfl
  rw [etgt] at e1
  refine ⟨?_, adelante_trans hf e2, e3.trans hh, ?_⟩
  · rw [e1]; exact adelante_al_target _ _ _ _ hj hc htg hge
  · rw [e1, e3]; exact htg

/-- Cierre de la rama en que el target queda atras: no cambia nada. -/
theorem cierre_no (s0 st r : tipos.State)
    (hj : Adelante s0.latest_justified st.latest_justified)
    (hf : Adelante s0.latest_finalized st.latest_finalized)
    (hh : st.historical_block_hashes = s0.historical_block_hashes)
    (hc : EnElHistorial st.historical_block_hashes st.latest_justified)
    (hfin : r.latest_justified =
              { root := st.latest_justified.root, slot := st.latest_justified.slot } ∧
            Adelante st.latest_finalized r.latest_finalized ∧
            r.historical_block_hashes = st.historical_block_hashes) :
    Adelante s0.latest_justified r.latest_justified ∧
    Adelante s0.latest_finalized r.latest_finalized ∧
    r.historical_block_hashes = s0.historical_block_hashes ∧
    EnElHistorial r.historical_block_hashes r.latest_justified := by
  obtain ⟨e1, e2, e3⟩ := hfin
  have elj : ({ root := st.latest_justified.root, slot := st.latest_justified.slot }
                : tipos.Checkpoint) = st.latest_justified := by
    cases st.latest_justified; rfl
  rw [elj] at e1
  refine ⟨?_, adelante_trans hf e2, e3.trans hh, ?_⟩
  · rw [e1]; exact hj
  · rw [e1, e3]; exact hc

theorem try_finalize_st7_spec (state : tipos.State)
    (source target : tipos.Checkpoint) (j : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    stf.try_finalize state source target j rts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.1.latest_justified = state.latest_justified ∧
                    Adelante state.latest_finalized r.1.latest_finalized ∧
                    r.1.historical_block_hashes = state.historical_block_hashes ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨st', j'⟩ := v
    have h1 := try_finalize_no_toca_justified state st' source target j j' rts hv
    have h2 := try_finalize_adelante state st' source target j j' rts hv
    exact ⟨h1, h2.1, h2.2⟩)

section
attribute [local spec] is_none_spec dato_en_spec bits_en_uno_en_spec
  primer_bit_spec votos_vacios_spec poner_si_falta_spec
  marcar_votos_spec cuenta_votos_spec sin_spec div_ceil_spec set_justified_spec
  is_valid_vote_historial_spec try_finalize_st7_spec

theorem process_attestations_loop_st7
    (s0 : tipos.State)
    (attestations : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (validator_count n : Std.Usize)
    (j0 : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global)
    (h0 : EnElHistorial s0.historical_block_hashes s0.latest_justified) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations_loop { start := 0#usize, «end» := n } s0
      attestations validator_count 0#u64 j0 rts core.option.Option.None
    ⦃ PostCond.mayThrow
        (fun r => ⌜ Adelante s0.latest_justified r.1.latest_justified ∧
                    Adelante s0.latest_finalized r.1.latest_finalized ∧
                    r.1.historical_block_hashes = s0.historical_block_hashes ∧
                    EnElHistorial r.1.historical_block_hashes r.1.latest_justified ⌝) ⦄ := by
  unfold stf.process_attestations_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × Acc =>
              Adelante s0.latest_justified x.2.1.latest_justified ∧
              Adelante s0.latest_finalized x.2.1.latest_finalized ∧
              x.2.1.historical_block_hashes = s0.historical_block_hashes ∧
              EnElHistorial x.2.1.historical_block_hashes x.2.1.latest_justified)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · exact ⟨Or.inl rfl, Or.inl rfl, rfl, h0⟩
  · intro x hinv
    obtain ⟨iter, st, ap, jj, fl⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    obtain ⟨hj, hf, hh, hc⟩ := hinv
    simp only at hj hf hh hc
    unfold stf.process_attestations_loop.body
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | assumption
      | trivial
      | exact ⟨hj, hf, hh, hc⟩
      | simp [PostCond.div, PostCond.mayThrow]
      | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    all_goals first
      | exact cierre_si _ _ _ _ _ _ hj hf hh hc (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption)
      | exact cierre_no _ _ _ hj hf hh hc (by assumption)
end

/-- El mismo resultado sin hipotesis afuera: la precondicion pasa a ser el
    antecedente de la postcondicion, que es la forma que `mvcgen` compone. -/
theorem process_attestations_loop_st7_spec
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
        (fun r => ⌜ EnElHistorial s0.historical_block_hashes s0.latest_justified →
                    (Adelante s0.latest_justified r.1.latest_justified ∧
                     Adelante s0.latest_finalized r.1.latest_finalized ∧
                     r.1.historical_block_hashes = s0.historical_block_hashes ∧
                     EnElHistorial r.1.historical_block_hashes r.1.latest_justified) ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv h0 =>
    of_triple_mayThrow
      (process_attestations_loop_st7 s0 attestations validator_count n j0 rts h0) hv)

theorem serialize_st7_spec (st : tipos.State) (j : mapa.MapaVotos)
    (vc : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.serialize_justifications st j vc
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.latest_justified = st.latest_justified ∧
                    r.latest_finalized = st.latest_finalized ∧
                    r.historical_block_hashes = st.historical_block_hashes ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv =>
    ⟨serialize_no_toca_justified st v j vc hv,
     serialize_no_toca_finalized st v j vc hv,
     serialize_no_toca_historial st v j vc hv⟩)

section
attribute [local spec] timer_spec inc_procesadas_spec contar_datos_spec
  hay_raiz_cero_spec construir_mapa_spec construir_rts_spec ssz_len_spec
  bitlist_len_spec serialize_st7_spec process_attestations_loop_st7_spec

theorem process_attestations_st7 (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (h0 : EnElHistorial state.historical_block_hashes state.latest_justified) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations state atts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ Adelante state.latest_justified r.2.latest_justified ∧
                    Adelante state.latest_finalized r.2.latest_finalized ∧
                    r.2.historical_block_hashes = state.historical_block_hashes ∧
                    EnElHistorial r.2.historical_block_hashes r.2.latest_justified ⌝) ⦄ := by
  unfold stf.process_attestations
  hax_mvcgen
  all_goals try first
    | rfl
    | assumption
    | trivial
    | exact ⟨Or.inl rfl, Or.inl rfl, rfl, h0⟩
    | simp [PostCond.div, PostCond.mayThrow]
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
  all_goals first
    | exact ⟨Or.inl rfl, Or.inl rfl, h0⟩
    | exact (by assumption : EnElHistorial _ _ → _) h0
    | (obtain ⟨a1, a2, a3, a4⟩ := (by assumption : EnElHistorial _ _ → _) h0
       obtain ⟨b1, b2, b3⟩ := (by assumption : _ = _ ∧ _ = _ ∧ _ = _)
       exact ⟨by rw [b1]; exact a1, by rw [b2]; exact a2, b3.trans a3,
              by rw [b1, b3]; exact a4⟩)
end

theorem process_attestations_st7_spec (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations state atts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ EnElHistorial state.historical_block_hashes state.latest_justified →
                    (Adelante state.latest_justified r.2.latest_justified ∧
                     Adelante state.latest_finalized r.2.latest_finalized ∧
                     r.2.historical_block_hashes = state.historical_block_hashes ∧
                     EnElHistorial r.2.historical_block_hashes r.2.latest_justified) ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv h0 =>
    of_triple_mayThrow (process_attestations_st7 state atts h0) hv)

/- ====================================================================
   `process_block_header` fuera del anclaje del genesis.
   ==================================================================== -/

theorem take_modelo_spec {T : Type} (inst : core.default.Default T) (x : T) :
    ⦃ ⌜ True ⌝ ⦄ core.mem.take inst x
    ⦃ PostCond.mayThrow (fun r => ⌜ r.1 = x ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    unfold core.mem.take at hv
    obtain ⟨d, _, hv⟩ := bind_da_ok hv
    simp only [RustM.ok.injEq] at hv
    subst hv; rfl)

theorem into_inner_modelo_spec {T : Type} {N : Std.Usize} (l : ssz.SszList T N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszList.into_inner l
    ⦃ PostCond.mayThrow (fun r => ⌜ r = l.items ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    unfold ssz.SszList.into_inner at hv
    simp only [RustM.ok.injEq] at hv
    exact hv.symm)

theorem push_modelo_spec {T : Type} (v : alloc.vec.Vec T) (x : T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.push v x
    ⦃ PostCond.mayThrow (fun r => ⌜ v.val <+: r.val ⌝) ⦄ :=
  triple_mayThrow_of (fun r hr => by
    unfold alloc.vec.Vec.push at hr
    obtain ⟨s, hs, hr⟩ := bind_da_ok hr
    simp only [RustM.ok.injEq] at hr
    subst hr
    unfold rust_primitives.sequence.seq_push at hs
    dsimp only at hs
    split at hs
    · simp only [RustM.ok.injEq] at hs
      subst hs
      exact ⟨[x], rfl⟩
    · simp at hs)

theorem try_from_modelo_spec {T : Type} (N : Std.Usize) (v : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄
    ssz.SszList.Insts.CoreConvertTryFromVecFueraDeCapacidad.try_from N v
    ⦃ PostCond.mayThrow
        (fun r => ⌜ ∀ l, r = core.result.Result.Ok l → l.items = v ⌝) ⦄ :=
  triple_mayThrow_of (fun r hr l hl => by
    unfold ssz.SszList.Insts.CoreConvertTryFromVecFueraDeCapacidad.try_from at hr
    obtain ⟨i, _, hr⟩ := bind_da_ok hr
    split at hr
    · simp only [RustM.ok.injEq] at hr
      subst hr
      cases hl
    · simp only [RustM.ok.injEq] at hr
      subst hr
      injection hl with hl
      subst hl
      rfl)

theorem expect_modelo_spec {T E : Type} (inst : core.fmt.Debug E)
    (r : core.result.Result T E) (s : Str) :
    ⦃ ⌜ True ⌝ ⦄ core.result.Result.expect inst r s
    ⦃ PostCond.mayThrow (fun t => ⌜ r = core.result.Result.Ok t ⌝) ⦄ :=
  triple_mayThrow_of (fun t ht => by
    unfold core.result.Result.expect at ht
    cases r with
    | Ok x =>
      simp only [RustM.ok.injEq] at ht
      subst ht; rfl
    | Err e => simp [core.panicking.internal.panic] at ht)

section
attribute [local spec] push_modelo_spec

/-- El loop que rellena los slots vacios solo AGREGA al final. -/
theorem header_loop_prefijo_spec (it : core.ops.range.Range Std.Usize)
    (v0 : alloc.vec.Vec tipos.H256) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_block_header_loop it v0
    ⦃ PostCond.mayThrow (fun r => ⌜ v0.val <+: r.val ⌝) ⦄ := by
  unfold stf.process_block_header_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × (alloc.vec.Vec tipos.H256) =>
              v0.val <+: x.2.val)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · exact List.prefix_rfl
  · intro x hinv
    obtain ⟨iter, v⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    simp only at hinv
    unfold stf.process_block_header_loop.body
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | assumption
      | trivial
      | simp [PostCond.div, PostCond.mayThrow]
      | exact List.IsPrefix.trans hinv (by assumption)
end

section
attribute [local spec] ssz_len_spec ST3H.current_proposer_spec ST3H.ok_or_spec
  ST3H.branch_spec ST3H.header_hash_spec ST3H.ne_default_spec ST3H.extend_spec
  ST3H.body_hash_spec ST3H.from_residual_spec
  take_modelo_spec into_inner_modelo_spec push_modelo_spec
  header_loop_prefijo_spec try_from_modelo_spec expect_modelo_spec

/-- Si el ultimo header no es el del genesis, `process_block_header` deja los
    dos checkpoints ENTEROS como estaban, y el historial viejo queda como
    prefijo del nuevo. -/
theorem process_block_header_st7_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block_header state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_block_header.slot ≠ 0#u64 →
            (r.2.latest_justified = state.latest_justified ∧
             r.2.latest_finalized = state.latest_finalized ∧
             state.historical_block_hashes.items.val <+:
               r.2.historical_block_hashes.items.val) ⌝) ⦄ := by
  unfold stf.process_block_header
  hax_mvcgen
  all_goals try first
    | rfl
    | assumption
    | trivial
    | exact fun _ => ⟨rfl, rfl, List.prefix_rfl⟩
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
  -- Queda la rama que llega al final. El historial nuevo se arma sacando el
  -- viejo con `mem::take`, agregandole la raiz del padre y los slots vacios,
  -- y volviendolo a guardar: cada paso solo agrega al final, y `grind`
  -- encadena los prefijos. Las ramas del anclaje del genesis ya se cerraron
  -- arriba, porque chocan con la hipotesis.
  all_goals grind [List.IsPrefix.trans]
end

/- ====================================================================
   Composicion.
   ==================================================================== -/

theorem enElHistorial_prefijo {h h' : ssz.SszList tipos.H256 262144#usize}
    {c : tipos.Checkpoint}
    (hc : EnElHistorial h c) (hp : h.items.val <+: h'.items.val) :
    EnElHistorial h' c := by
  unfold EnElHistorial at *
  obtain ⟨t, ht⟩ := hp
  rw [← ht]
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hc
  rw [List.getElem?_append_left hlt]
  exact hc

theorem process_slots_st7_spec (state : tipos.State) (t : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_slots state t
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.2.latest_justified = state.latest_justified ∧
                    r.2.latest_finalized = state.latest_finalized ∧
                    r.2.historical_block_hashes = state.historical_block_hashes ∧
                    r.2.latest_block_header.slot = state.latest_block_header.slot ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨res, st'⟩ := v
    exact process_slots_no_toca state st' t res hv)

/-- Lo que ST-7 pide de un paso, mas la hipotesis de coherencia conservada. -/
def Paso7 (s s' : tipos.State) : Prop :=
  Adelante s.latest_justified s'.latest_justified ∧
  Adelante s.latest_finalized s'.latest_finalized ∧
  EnElHistorial s'.historical_block_hashes s'.latest_justified

/-- Encadenar header y attestations. -/
theorem paso7_header_atts (s s1 s2 : tipos.State)
    (hc : EnElHistorial s.historical_block_hashes s.latest_justified)
    (hh : s1.latest_justified = s.latest_justified ∧
          s1.latest_finalized = s.latest_finalized ∧
          s.historical_block_hashes.items.val <+: s1.historical_block_hashes.items.val)
    (ha : EnElHistorial s1.historical_block_hashes s1.latest_justified →
          (Adelante s1.latest_justified s2.latest_justified ∧
           Adelante s1.latest_finalized s2.latest_finalized ∧
           s2.historical_block_hashes = s1.historical_block_hashes ∧
           EnElHistorial s2.historical_block_hashes s2.latest_justified)) :
    Paso7 s s2 := by
  obtain ⟨h1, h2, h3⟩ := hh
  have hc1 : EnElHistorial s1.historical_block_hashes s1.latest_justified := by
    rw [h1]; exact enElHistorial_prefijo hc h3
  obtain ⟨a1, a2, -, a4⟩ := ha hc1
  rw [h1] at a1
  rw [h2] at a2
  exact ⟨a1, a2, a4⟩

/-- Si el header rechaza el bloque, el estado que devuelve igual cumple. -/
theorem paso7_header (s s1 : tipos.State)
    (hc : EnElHistorial s.historical_block_hashes s.latest_justified)
    (hh : s1.latest_justified = s.latest_justified ∧
          s1.latest_finalized = s.latest_finalized ∧
          s.historical_block_hashes.items.val <+: s1.historical_block_hashes.items.val) :
    Paso7 s s1 := by
  obtain ⟨h1, h2, h3⟩ := hh
  refine ⟨Or.inl h1, Or.inl h2, ?_⟩
  rw [h1]; exact enElHistorial_prefijo hc h3

section
attribute [local spec] ST3H.branch_spec ST3H.from_residual_spec
  ST3H.ne_default_spec ST3T.time_block_spec ST3T.time_transition_spec
  ST3T.state_hash_spec process_block_header_st7_spec
  process_attestations_st7_spec

theorem process_block_st7_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_block_header.slot ≠ 0#u64 →
                    EnElHistorial state.historical_block_hashes state.latest_justified →
                    Paso7 state r.2 ⌝) ⦄ := by
  unfold stf.process_block
  hax_mvcgen
  all_goals first
    | exact paso7_header_atts _ _ _ (by assumption)
        ((by assumption : _ ≠ _ → _) (by assumption)) (by assumption)
    | exact paso7_header _ _ (by assumption)
        ((by assumption : _ ≠ _ → _) (by assumption))
end

theorem paso7_slots_block (s s1 s2 : tipos.State)
    (hnz : s.latest_block_header.slot ≠ 0#u64)
    (hc : EnElHistorial s.historical_block_hashes s.latest_justified)
    (hs : s1.latest_justified = s.latest_justified ∧
          s1.latest_finalized = s.latest_finalized ∧
          s1.historical_block_hashes = s.historical_block_hashes ∧
          s1.latest_block_header.slot = s.latest_block_header.slot)
    (hb : s1.latest_block_header.slot ≠ 0#u64 →
          EnElHistorial s1.historical_block_hashes s1.latest_justified →
          Paso7 s1 s2) :
    Paso7 s s2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have hp := hb (by rw [h4]; exact hnz) (by rw [h3, h1]; exact hc)
  unfold Paso7 at *
  rw [h1, h2] at hp
  exact hp

theorem paso7_slots (s s1 : tipos.State)
    (hc : EnElHistorial s.historical_block_hashes s.latest_justified)
    (hs : s1.latest_justified = s.latest_justified ∧
          s1.latest_finalized = s.latest_finalized ∧
          s1.historical_block_hashes = s.historical_block_hashes ∧
          s1.latest_block_header.slot = s.latest_block_header.slot) :
    Paso7 s s1 := by
  obtain ⟨h1, h2, h3, -⟩ := hs
  exact ⟨Or.inl h1, Or.inl h2, by rw [h3, h1]; exact hc⟩

section
attribute [local spec] ST3H.branch_spec ST3H.from_residual_spec
  ST3H.ne_default_spec ST3T.time_transition_spec ST3T.state_hash_spec
  process_slots_st7_spec process_block_st7_spec

theorem state_transition_st7_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.state_transition state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_block_header.slot ≠ 0#u64 →
                    EnElHistorial state.historical_block_hashes state.latest_justified →
                    Paso7 state r.2 ⌝) ⦄ := by
  unfold stf.state_transition
  hax_mvcgen
  all_goals first
    | exact paso7_slots_block _ _ _ (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact paso7_slots _ _ (by assumption) (by assumption)
end

/-- `ST-7` sobre `process_attestations`, como ecuacion. -/
theorem process_attestations_adelante
    (state state' : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (res : core.result.Result Unit stf.Error)
    (hhist : EnElHistorial state.historical_block_hashes state.latest_justified)
    (h : stf.process_attestations state atts = ok (res, state')) :
    Adelante state.latest_justified state'.latest_justified ∧
    Adelante state.latest_finalized state'.latest_finalized ∧
    EnElHistorial state'.historical_block_hashes state'.latest_justified := by
  obtain ⟨a1, a2, -, a4⟩ :=
    of_triple_mayThrow (process_attestations_st7 state atts hhist) h
  exact ⟨a1, a2, a4⟩

/-- Fuera del anclaje del genesis, `process_block_header` no toca ninguno de
    los dos checkpoints -- enteros, raiz incluida -- y solo agrega al final
    del historial. -/
theorem process_block_header_no_toca_checkpoints
    (state state' : tipos.State) (block : tipos.Block)
    (res : core.result.Result Unit stf.Error)
    (hnz : state.latest_block_header.slot ≠ 0#u64)
    (h : stf.process_block_header state block = ok (res, state')) :
    state'.latest_justified = state.latest_justified ∧
    state'.latest_finalized = state.latest_finalized ∧
    state.historical_block_hashes.items.val <+:
      state'.historical_block_hashes.items.val :=
  of_triple_mayThrow (process_block_header_st7_spec state block) h hnz

end ST7

/-- Teorema 7: `ST-7` sobre la transicion entera de un bloque.

    Sobre un estado que ya paso el anclaje del genesis (`hnz`) y cuyo
    checkpoint justificado esta en el historial (`hhist`), si `state_transition`
    devuelve `ok` -- acepte el bloque o lo rechace --, cada checkpoint queda
    igual ENTERO, raiz incluida, o pasa a un slot estrictamente mayor. No hay
    cambio de raiz en el mismo slot. Ademas `hhist` se conserva. -/
theorem ST7.state_transition_adelante
    (state state' : mini_stf.tipos.State) (block : mini_stf.tipos.Block)
    (res : core.result.Result Unit mini_stf.stf.Error)
    (hnz : state.latest_block_header.slot ≠ 0#u64)
    (hhist : ST7.EnElHistorial state.historical_block_hashes state.latest_justified)
    (h : mini_stf.stf.state_transition state block = ok (res, state')) :
    (state'.latest_justified = state.latest_justified ∨
      state.latest_justified.slot < state'.latest_justified.slot) ∧
    (state'.latest_finalized = state.latest_finalized ∨
      state.latest_finalized.slot < state'.latest_finalized.slot) ∧
    ST7.EnElHistorial state'.historical_block_hashes state'.latest_justified :=
  ST3.of_triple_mayThrow (ST7.state_transition_st7_spec state block) h hnz hhist

/- ===========================================================================
   Teorema 8: ST-1, ST-2, ST-4 y ST-6 (15 nov 2026)

   Las otras propiedades de transicion de estado del catalogo. Con ST-3 y
   ST-7 quedan cubiertas las siete, contando que ST-5 ("la transicion es
   pura") es `rfl` para cualquier funcion de Lean y no se enuncia.

   ST-1. `process_slots` deja el estado en el slot pedido. El catalogo la
         enuncia con `slot <= target` porque su modelo devuelve un estado y
         no rechaza. La especificacion en Python y ethlambda rechazan los dos
         cuando `slot >= target`, asi que aca son dos enunciados: si acepta,
         queda en el slot pedido; y si el slot pedido no esta en el futuro,
         rechaza sin tocar el estado.

   ST-2. Si `process_block_header` acepta, el ultimo header queda en el slot
         del bloque. De paso sale lo que le faltaba a ST-7: si el ultimo
         header no era el del genesis, sigue sin serlo, acepte o rechace. Y
         eso se sube a `state_transition` entera, para lo que hace falta que
         el resto de la transicion no toque `latest_block_header`.

   ST-4. El slot justificado es siempre >= el finalizado. En el catalogo es
         un invariante de los estados alcanzables; aca se demuestra el paso
         inductivo, para cualquier estado: si vale antes de la transicion,
         vale despues. La razon: `try_finalize` solo corre justo despues de
         justificar un target, lo que finaliza es el source de ese voto, y un
         voto valido tiene `source.slot < target.slot`. No hace falta razonar
         sobre la lista de bits `justified_slots`, y tampoco hace falta
         ninguna hipotesis sobre el anclaje del genesis, porque ethlambda ahi
         escribe solo las raices.

   ST-6. La finalizacion es irreversible: es la mitad `latest_finalized` de
         ST-3, con nombre propio como en el catalogo.

   Lo que NO esta: el caso base de ST-4 (que el estado del genesis cumple el
   invariante). El crate no construye el estado del genesis.
   =========================================================================== -/

namespace ST1
open mini_stf

/-- `ST-1`: si `process_slots` acepta, el estado queda en el slot pedido. -/
theorem process_slots_avanza
    (state state' : tipos.State) (t : Std.U64)
    (h : stf.process_slots state t = ok (core.result.Result.Ok (), state')) :
    state'.slot = t := by
  unfold stf.process_slots at h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  split at h
  · simp only [RustM.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hres, -⟩ := h
    cases hres
  · obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    simp only [RustM.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hst⟩ := h
    subst hst
    rfl

/-- El otro lado: si el slot pedido no esta en el futuro, rechaza y devuelve
    el estado sin tocar. -/
theorem process_slots_rechaza
    (state : tipos.State) (t : Std.U64) (h : state.slot ≥ t) :
    stf.process_slots state t =
      ok (core.result.Result.Err (stf.Error.StateSlotIsNewer t state.slot), state) := by
  unfold stf.process_slots
  simp [stubs.metrics.time_slots_processing, h]

end ST1

namespace ST2
open mini_stf
open Std.Tactic
open ST3

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

section
attribute [local spec] ssz_len_spec ST3H.current_proposer_spec ST3H.ok_or_spec
  ST3H.branch_spec ST3H.header_hash_spec ST3H.ne_default_spec ST3H.take_spec
  ST3H.into_inner_spec ST3H.push_spec ST3H.header_loop_spec ST3H.try_from_spec
  ST3H.expect_spec ST3H.extend_spec ST3H.body_hash_spec
  ST7.from_residual_err_spec

theorem process_block_header_slot_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block_header state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ (r.1 = core.result.Result.Ok () →
                       r.2.latest_block_header.slot = block.slot) ∧
                    (state.latest_block_header.slot ≠ 0#u64 →
                       r.2.latest_block_header.slot ≠ 0#u64) ⌝) ⦄ := by
  unfold stf.process_block_header
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | (refine ⟨?_, ?_⟩ <;> first | (simp_all; done) | (intros; scalar_tac) | grind)
end

/-- `ST-2`: si `process_block_header` acepta, el ultimo header queda en el
    slot del bloque. -/
theorem process_block_header_slot
    (state state' : tipos.State) (block : tipos.Block)
    (h : stf.process_block_header state block =
           ok (core.result.Result.Ok (), state')) :
    state'.latest_block_header.slot = block.slot :=
  (of_triple_mayThrow (process_block_header_slot_spec state block) h).1 rfl

/-- Acepte o rechace, si el ultimo header no era el del genesis sigue sin
    serlo. -/
theorem process_block_header_conserva_no_genesis
    (state state' : tipos.State) (block : tipos.Block)
    (res : core.result.Result Unit stf.Error)
    (hnz : state.latest_block_header.slot ≠ 0#u64)
    (h : stf.process_block_header state block = ok (res, state')) :
    state'.latest_block_header.slot ≠ 0#u64 :=
  (of_triple_mayThrow (process_block_header_slot_spec state block) h).2 hnz

/- El resto de la transicion no toca `latest_block_header`. -/

theorem try_finalize_no_toca_header
    (state state' : tipos.State) (source target : tipos.Checkpoint)
    (j j' : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global)
    (h : stf.try_finalize state source target j rts = ok (state', j')) :
    state'.latest_block_header = state.latest_block_header := by
  unfold stf.try_finalize at h
  split at h
  · simp_all
  · obtain ⟨i, hadd, h⟩ := bind_da_ok h
    obtain ⟨b, hb, h⟩ := bind_da_ok h
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
      rfl

theorem serialize_no_toca_header
    (state state' : tipos.State) (j : mapa.MapaVotos) (vc : Std.Usize)
    (h : stf.serialize_justifications state j vc = ok state') :
    state'.latest_block_header = state.latest_block_header := by
  unfold stf.serialize_justifications at h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  simp only [RustM.ok.injEq] at h
  subst h
  rfl

theorem try_finalize_header_spec (state : tipos.State)
    (source target : tipos.Checkpoint) (j : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    stf.try_finalize state source target j rts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.1.latest_block_header = state.latest_block_header ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨st', j'⟩ := v
    exact try_finalize_no_toca_header state st' source target j j' rts hv)

theorem serialize_header_spec (st : tipos.State) (j : mapa.MapaVotos)
    (vc : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.serialize_justifications st j vc
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.latest_block_header = st.latest_block_header ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => serialize_no_toca_header st v j vc hv)

section
attribute [local spec] is_none_spec dato_en_spec bits_en_uno_en_spec
  is_valid_vote_spec primer_bit_spec votos_vacios_spec poner_si_falta_spec
  marcar_votos_spec cuenta_votos_spec sin_spec div_ceil_spec set_justified_spec
  try_finalize_header_spec

theorem process_attestations_loop_header_spec
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
        (fun r => ⌜ r.1.latest_block_header = s0.latest_block_header ⌝) ⦄ := by
  unfold stf.process_attestations_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × Acc =>
              x.2.1.latest_block_header = s0.latest_block_header)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · rfl
  · intro x hinv
    obtain ⟨iter, st, ap, jj, fl⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    simp only at hinv
    unfold stf.process_attestations_loop.body
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | assumption
      | trivial
      | simp [PostCond.div, PostCond.mayThrow]
      | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
end

section
attribute [local spec] timer_spec inc_procesadas_spec contar_datos_spec
  hay_raiz_cero_spec construir_mapa_spec construir_rts_spec ssz_len_spec
  bitlist_len_spec serialize_header_spec process_attestations_loop_header_spec

theorem process_attestations_header_spec (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations state atts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.2.latest_block_header = state.latest_block_header ⌝) ⦄ := by
  unfold stf.process_attestations
  hax_mvcgen
  all_goals try first
    | rfl
    | assumption
    | trivial
    | simp [PostCond.div, PostCond.mayThrow]
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
end

theorem process_slots_header_spec (state : tipos.State) (t : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_slots state t
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.2.latest_block_header.slot = state.latest_block_header.slot ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨res, st'⟩ := v
    exact (ST7.process_slots_no_toca state st' t res hv).2.2.2)

theorem process_block_header_no_genesis_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block_header state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_block_header.slot ≠ 0#u64 →
                    r.2.latest_block_header.slot ≠ 0#u64 ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv hnz => by
    obtain ⟨res, st'⟩ := v
    exact process_block_header_conserva_no_genesis state st' block res hnz hv)

section
attribute [local spec] ST3H.branch_spec ST3H.from_residual_spec
  ST3H.ne_default_spec ST3T.time_block_spec ST3T.time_transition_spec
  ST3T.state_hash_spec process_block_header_no_genesis_spec
  process_attestations_header_spec

theorem process_block_no_genesis_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_block_header.slot ≠ 0#u64 →
                    r.2.latest_block_header.slot ≠ 0#u64 ⌝) ⦄ := by
  unfold stf.process_block
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | grind
end

section
attribute [local spec] ST3H.branch_spec ST3H.from_residual_spec
  ST3H.ne_default_spec ST3T.time_transition_spec ST3T.state_hash_spec
  process_slots_header_spec process_block_no_genesis_spec

theorem state_transition_no_genesis_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.state_transition state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_block_header.slot ≠ 0#u64 →
                    r.2.latest_block_header.slot ≠ 0#u64 ⌝) ⦄ := by
  unfold stf.state_transition
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | grind
end

end ST2

namespace ST4
open mini_stf
open Std.Tactic
open ST3

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

/-- Cuando `try_finalize` mueve la finalidad, la mueve al `source`. -/
theorem try_finalize_fin_es_source
    (state state' : tipos.State) (source target : tipos.Checkpoint)
    (j j' : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global)
    (h : stf.try_finalize state source target j rts = ok (state', j')) :
    state'.latest_finalized = state.latest_finalized ∨
    state'.latest_finalized = source := by
  unfold stf.try_finalize at h
  split at h
  · simp_all
  · obtain ⟨i, hadd, h⟩ := bind_da_ok h
    obtain ⟨b, hb, h⟩ := bind_da_ok h
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
      exact Or.inr rfl

theorem try_finalize_st4_spec (state : tipos.State)
    (source target : tipos.Checkpoint) (j : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    stf.try_finalize state source target j rts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.1.latest_justified = state.latest_justified ∧
                    (r.1.latest_finalized = state.latest_finalized ∨
                     r.1.latest_finalized = source) ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨st', j'⟩ := v
    exact ⟨try_finalize_no_toca_justified state st' source target j j' rts hv,
           try_finalize_fin_es_source state st' source target j j' rts hv⟩)

section
attribute [local spec] ST7.ssz_deref_spec ST7.is_slot_justified_spec
  ST7.justifiable_spec ST7.from_residual_err_spec ST7.matches_chain_spec
  ST3H.branch_spec

/-- Un voto que `is_valid_vote` acepta va hacia adelante: el source esta
    estrictamente antes que el target. -/
theorem is_valid_vote_orden_spec (st : tipos.State) (d : tipos.AttestationData) :
    ⦃ ⌜ True ⌝ ⦄ stf.is_valid_vote st d
    ⦃ PostCond.mayThrow (fun r => ⌜ r = core.result.Result.Ok true →
        d.source.slot < d.target.slot ⌝) ⦄ := by
  unfold stf.is_valid_vote
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | scalar_tac
    | (simp_all; scalar_tac)
    | grind
end

/-- Cierre de la rama en que el target empata o supera al justificado. -/
theorem cierre4_si (st r : tipos.State) (src tgt : tipos.Checkpoint) (v : Bool)
    (res : core.result.Result Bool stf.Error)
    (hinv : st.latest_finalized.slot ≤ st.latest_justified.slot)
    (hvoto : res = core.result.Result.Ok true → src.slot < tgt.slot)
    (hres : res = core.result.Result.Ok v) (hv : v = true)
    (hge : tgt.slot ≥ st.latest_justified.slot)
    (hfin : r.latest_justified = { root := tgt.root, slot := tgt.slot } ∧
            (r.latest_finalized = st.latest_finalized ∨
             r.latest_finalized = src)) :
    r.latest_finalized.slot ≤ r.latest_justified.slot := by
  obtain ⟨e1, e2⟩ := hfin
  have hlt := hvoto (by rw [hres, hv])
  rw [e1]
  show r.latest_finalized.slot ≤ tgt.slot
  rcases e2 with e2 | e2 <;> rw [e2] <;> scalar_tac

/-- Cierre de la rama en que el target queda atras del justificado. -/
theorem cierre4_no (st r : tipos.State) (src tgt : tipos.Checkpoint) (v : Bool)
    (res : core.result.Result Bool stf.Error)
    (hinv : st.latest_finalized.slot ≤ st.latest_justified.slot)
    (hvoto : res = core.result.Result.Ok true → src.slot < tgt.slot)
    (hres : res = core.result.Result.Ok v) (hv : v = true)
    (hlt : ¬ tgt.slot ≥ st.latest_justified.slot)
    (hfin : r.latest_justified =
              { root := st.latest_justified.root, slot := st.latest_justified.slot } ∧
            (r.latest_finalized = st.latest_finalized ∨
             r.latest_finalized = src)) :
    r.latest_finalized.slot ≤ r.latest_justified.slot := by
  obtain ⟨e1, e2⟩ := hfin
  have hst := hvoto (by rw [hres, hv])
  rw [e1]
  show r.latest_finalized.slot ≤ st.latest_justified.slot
  rcases e2 with e2 | e2 <;> rw [e2] <;> scalar_tac

section
attribute [local spec] is_none_spec dato_en_spec bits_en_uno_en_spec
  primer_bit_spec votos_vacios_spec poner_si_falta_spec
  marcar_votos_spec cuenta_votos_spec sin_spec div_ceil_spec set_justified_spec
  is_valid_vote_orden_spec try_finalize_st4_spec

theorem process_attestations_loop_st4
    (s0 : tipos.State)
    (attestations : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (validator_count n : Std.Usize)
    (j0 : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global)
    (h0 : s0.latest_finalized.slot ≤ s0.latest_justified.slot) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations_loop { start := 0#usize, «end» := n } s0
      attestations validator_count 0#u64 j0 rts core.option.Option.None
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.1.latest_finalized.slot ≤ r.1.latest_justified.slot ⌝) ⦄ := by
  unfold stf.process_attestations_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × Acc =>
              x.2.1.latest_finalized.slot ≤ x.2.1.latest_justified.slot)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · exact h0
  · intro x hinv
    obtain ⟨iter, st, ap, jj, fl⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    simp only at hinv
    unfold stf.process_attestations_loop.body
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | assumption
      | trivial
      | simp [PostCond.div, PostCond.mayThrow]
      | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    all_goals first
      | exact cierre4_si _ _ _ _ _ _ hinv (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption)
      | exact cierre4_no _ _ _ _ _ _ hinv (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption)
end

theorem process_attestations_loop_st4_spec
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
        (fun r => ⌜ s0.latest_finalized.slot ≤ s0.latest_justified.slot →
                    r.1.latest_finalized.slot ≤ r.1.latest_justified.slot ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv h0 =>
    of_triple_mayThrow
      (process_attestations_loop_st4 s0 attestations validator_count n j0 rts h0) hv)

section
attribute [local spec] timer_spec inc_procesadas_spec contar_datos_spec
  hay_raiz_cero_spec construir_mapa_spec construir_rts_spec ssz_len_spec
  bitlist_len_spec ST7.serialize_st7_spec process_attestations_loop_st4_spec

theorem process_attestations_st4 (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (h0 : state.latest_finalized.slot ≤ state.latest_justified.slot) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations state atts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.2.latest_finalized.slot ≤ r.2.latest_justified.slot ⌝) ⦄ := by
  unfold stf.process_attestations
  hax_mvcgen
  all_goals try first
    | rfl
    | assumption
    | trivial
    | exact h0
    | simp [PostCond.div, PostCond.mayThrow]
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
  all_goals first
    | exact (by assumption : _ ≤ _ → _) h0
    | (have a := (by assumption : _ ≤ _ → _) h0
       obtain ⟨b1, b2, -⟩ := (by assumption : _ = _ ∧ _ = _ ∧ _ = _)
       rw [b1, b2]; exact a)
end

theorem process_attestations_st4_spec (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations state atts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_finalized.slot ≤ state.latest_justified.slot →
                    r.2.latest_finalized.slot ≤ r.2.latest_justified.slot ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv h0 =>
    of_triple_mayThrow (process_attestations_st4 state atts h0) hv)

theorem paso4_header_atts (s s1 s2 : tipos.State)
    (h : s.latest_finalized.slot ≤ s.latest_justified.slot)
    (hh : s1.latest_justified.slot = s.latest_justified.slot ∧
          s1.latest_finalized.slot = s.latest_finalized.slot)
    (ha : s1.latest_finalized.slot ≤ s1.latest_justified.slot →
          s2.latest_finalized.slot ≤ s2.latest_justified.slot) :
    s2.latest_finalized.slot ≤ s2.latest_justified.slot :=
  ha (by rw [hh.1, hh.2]; exact h)

theorem paso4_header (s s1 : tipos.State)
    (h : s.latest_finalized.slot ≤ s.latest_justified.slot)
    (hh : s1.latest_justified.slot = s.latest_justified.slot ∧
          s1.latest_finalized.slot = s.latest_finalized.slot) :
    s1.latest_finalized.slot ≤ s1.latest_justified.slot := by
  rw [hh.1, hh.2]; exact h

section
attribute [local spec] ST3H.branch_spec ST3H.from_residual_spec
  ST3H.ne_default_spec ST3T.time_block_spec ST3H.process_block_header_spec
  process_attestations_st4_spec

theorem process_block_st4_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_finalized.slot ≤ state.latest_justified.slot →
                    r.2.latest_finalized.slot ≤ r.2.latest_justified.slot ⌝) ⦄ := by
  unfold stf.process_block
  hax_mvcgen
  all_goals first
    | exact paso4_header_atts state _ _ (by assumption) (by assumption) (by assumption)
    | exact paso4_header state _ (by assumption) (by assumption)
end

theorem paso4_slots_block (s s1 s2 : tipos.State)
    (h : s.latest_finalized.slot ≤ s.latest_justified.slot)
    (hs : s1.latest_justified = s.latest_justified ∧
          s1.latest_finalized = s.latest_finalized)
    (hb : s1.latest_finalized.slot ≤ s1.latest_justified.slot →
          s2.latest_finalized.slot ≤ s2.latest_justified.slot) :
    s2.latest_finalized.slot ≤ s2.latest_justified.slot :=
  hb (by rw [hs.1, hs.2]; exact h)

theorem paso4_slots (s s1 : tipos.State)
    (h : s.latest_finalized.slot ≤ s.latest_justified.slot)
    (hs : s1.latest_justified = s.latest_justified ∧
          s1.latest_finalized = s.latest_finalized) :
    s1.latest_finalized.slot ≤ s1.latest_justified.slot := by
  rw [hs.1, hs.2]; exact h

section
attribute [local spec] ST3H.branch_spec ST3H.from_residual_spec
  ST3H.ne_default_spec ST3T.time_transition_spec ST3T.state_hash_spec
  ST3T.process_slots_spec process_block_st4_spec

theorem state_transition_st4_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.state_transition state block
    ⦃ PostCond.mayThrow
        (fun r => ⌜ state.latest_finalized.slot ≤ state.latest_justified.slot →
                    r.2.latest_finalized.slot ≤ r.2.latest_justified.slot ⌝) ⦄ := by
  unfold stf.state_transition
  hax_mvcgen
  all_goals first
    | exact paso4_slots_block state _ _ (by assumption) (by assumption) (by assumption)
    | exact paso4_slots state _ (by assumption) (by assumption)
end

end ST4

/-- `ST-4`, el paso inductivo: si el slot finalizado no supera al justificado
    antes de la transicion, tampoco lo supera despues. Vale para cualquier
    estado, acepte o rechace el bloque. -/
theorem ST4.state_transition_justificado_ge_finalizado
    (state state' : mini_stf.tipos.State) (block : mini_stf.tipos.Block)
    (res : core.result.Result Unit mini_stf.stf.Error)
    (hinv : state.latest_finalized.slot ≤ state.latest_justified.slot)
    (h : mini_stf.stf.state_transition state block = ok (res, state')) :
    state'.latest_finalized.slot ≤ state'.latest_justified.slot :=
  ST3.of_triple_mayThrow (ST4.state_transition_st4_spec state block) h hinv

/-- La hipotesis `hnz` de `ST-7` se conserva: si el ultimo header no era el
    del genesis antes de la transicion, tampoco lo es despues. -/
theorem ST2.state_transition_conserva_no_genesis
    (state state' : mini_stf.tipos.State) (block : mini_stf.tipos.Block)
    (res : core.result.Result Unit mini_stf.stf.Error)
    (hnz : state.latest_block_header.slot ≠ 0#u64)
    (h : mini_stf.stf.state_transition state block = ok (res, state')) :
    state'.latest_block_header.slot ≠ 0#u64 :=
  ST3.of_triple_mayThrow (ST2.state_transition_no_genesis_spec state block) h hnz

/-- `ST-6`: la finalizacion es irreversible. Es la mitad `latest_finalized`
    de `ST-3`, con nombre propio como en el catalogo. -/
theorem ST6.finalizacion_irreversible
    (state state' : mini_stf.tipos.State) (block : mini_stf.tipos.Block)
    (res : core.result.Result Unit mini_stf.stf.Error)
    (h : mini_stf.stf.state_transition state block = ok (res, state')) :
    state.latest_finalized.slot ≤ state'.latest_finalized.slot :=
  (ST3.state_transition_no_retrocede state state' block res h).2

/- ===========================================================================
   Teorema 9: la ventana de slots justificados (17 nov 2026)

   Los cuatro teoremas con los que empezo el analisis, sobre
   `justified_slots_ops`: la lista de bits que guarda que slots estan
   justificados, con indices relativos al slot finalizado. Todo lo anterior
   de este archivo la esquivo a proposito; aca se entra.

     1. `extend_to_slot` no pierde bits. Forma exacta: solo agrega ceros al
        final.
     2. Ida y vuelta: despues de `set_justified(s)`, `is_slot_justified(s)`
        devuelve `Ok(true)`.
     3. `shift_window` corre sin deformar. Forma exacta: la lista nueva es la
        vieja sin sus primeros `delta` bits.
     4. El compuesto: cuando la finalidad avanza y la ventana se corre, todo
        slot que sigue por encima del limite nuevo se reporta igual que antes.

   Como esta armado:

     - Una capa base con lo que hacen `get`, `set`, `len`, `with_length` y
       `relative_index`, como ECUACIONES: `get s i = ok (s.bits[i]?)`. Para
       eso hubo que desarmar los modelos de `core` hasta el fondo (indices de
       slice, `vec![false; n]`, la resta con desborde). A diferencia de los
       teoremas anteriores, estas ecuaciones dicen que la operacion DEVUELVE,
       no "si devuelve".
     - Dos invariantes sobre listas, `Copiado` y `Desplazado`, con sus lemas
       de paso demostrados en Lean puro, sin nada de Rust.
     - Los dos loops de copia, con el mismo `loop_spec` de siempre: tres
       objetivos cada uno (bit en uno, bit en cero, fin del rango), cerrados
       con los lemas de paso.

   Dos cosas a tener presentes al leer los enunciados:

     - Los teoremas 2 y 4 concluyen que `is_slot_justified` DEVUELVE `Ok`: no
       son condicionales en esa segunda llamada. Si lo son en la primera
       (`set_justified`, `shift_window`), como todo lo demas.
     - El teorema 4 pide que la distancia entre el slot y el finalizado entre
       en un `usize` (`hfit`). El codigo hace `idx as usize`, y el modelo no
       fija el ancho de `usize`: en 32 bits ese cast trunca y dos slots a
       distancia 2^32 compartirian bit. En 64 bits la hipotesis vale siempre.
   =========================================================================== -/

namespace JS
open mini_stf
open Std.Tactic
open ST3

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

theorem get_eq {N : Std.Usize} (s : ssz.SszBitlist N) (i : Std.Usize) :
    ssz.SszBitlist.get s i = ok (s.bits.val[i.val]?) := by
  unfold ssz.SszBitlist.get
  simp [alloc.vec.Vec.len, rust_primitives.sequence.seq_len,
    alloc.vec.Vec.Insts.CoreOpsIndexIndex.index,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
    rust_primitives.sequence.seq_to_slice]
  by_cases h : i.val < s.bits.val.length
  · simp [h, core.Slice.Insts.CoreOpsIndexIndex.index,
      core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get,
      rust_primitives.slice.slice_length, rust_primitives.slice.slice_index,
      Slice.index_usize]
  · simp [h]

theorem len_eq {N : Std.Usize} (s : ssz.SszBitlist N) :
    ∃ n : Std.Usize, ssz.SszBitlist.len s = ok n ∧ n.val = s.bits.val.length := by
  unfold ssz.SszBitlist.len
  simp [alloc.vec.Vec.len, rust_primitives.sequence.seq_len]

theorem set_eq {N : Std.Usize} (s : ssz.SszBitlist N) (i : Std.Usize) (v : Bool) :
    ∃ r, ssz.SszBitlist.set s i v = ok r ∧
      r.2.bits.val = s.bits.val.set i.val v ∧
      (r.1 = core.result.Result.Ok () ↔ i.val < s.bits.val.length) := by
  unfold ssz.SszBitlist.set
  simp [alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut,
    core.slice.Slice.get_mut, alloc.vec.Vec.as_mut_slice,
    rust_primitives.sequence.seq_to_slice_mut,
    core.Usize.Insts.CoreSliceIndexSliceIndexSliceT.get_mut,
    rust_primitives.slice.slice_length]
  by_cases h : i.val < s.bits.val.length
  · simp [h, rust_primitives.slice.slice_index_mut, Slice.index_mut_usize,
      Slice.index_usize]
  · simp [h]
    first
      | exact (List.set_eq_of_length_le (by omega)).symm
      | (apply List.ext_getElem?; intro k; simp [List.getElem?_set]; intro hk; omega)

theorem mapM_ok {α : Type} (l : List α) :
    List.mapM (fun x : α => (ok x : RustM α)) l = ok l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.mapM_cons, ih]; rfl

theorem with_length_eq (N l : Std.Usize) (b : ssz.SszBitlist N)
    (h : ssz.SszBitlist.with_length N l = ok (core.result.Result.Ok b)) :
    b.bits.val = List.replicate l.val false := by
  have hclone : (core.Bool.Insts.CoreCloneClone.clone) = fun x : Bool => (ok x : RustM Bool) := by
    funext x; rfl
  unfold ssz.SszBitlist.with_length at h
  simp [alloc.vec.from_elem, rust_primitives.sequence.seq_create, hclone, mapM_ok] at h
  by_cases hN : N.val < l.val
  · simp [hN] at h
  · by_cases h0 : l.val = 0
    · simp [hN, h0] at h
      rw [← h]
      simp [Slice.new, h0]
    · have hlt : l.val - 1 < Usize.max := by scalar_tac
      simp [hN, h0, hlt] at h
      rw [← h]
      show List.replicate (l.val - 1) false ++ [false] = List.replicate l.val false
      have e : l.val = (l.val - 1) + 1 := by omega
      rw [e, List.replicate_succ']
      simp

theorem sub_val (x y : Std.U64) (h : y.val ≤ x.val) :
    ((⟨x.bv - y.bv⟩ : Std.U64)).val = x.val - y.val := by
  show (x.bv - y.bv).toNat = x.bv.toNat - y.bv.toNat
  exact BitVec.toNat_sub_of_le (by simpa [BitVec.le_def] using h)

theorem checked_sub_eq (x y : Std.U64) :
    core.num.U64.checked_sub x y =
      ok (if x.val < y.val then none else some (⟨x.bv - y.bv⟩ : Std.U64)) := by
  simp [core.num.U64.checked_sub, core.num.U64.overflowing_sub,
    rust_primitives.arithmetic.overflowing_sub_u64, uoverflowing_sub]
  split <;> simp_all

/-- `relative_index`: nunca entra en panico; da `none` exactamente cuando el
    slot no esta por encima del finalizado, y si no el indice es la distancia
    menos uno, pasada por el `as usize`. -/
theorem relative_index_eq (t f : Std.U64) :
    ∃ o, justified_slots_ops.relative_index t f = ok o ∧
      (o = none ↔ t.val ≤ f.val) ∧
      (∀ i : Std.Usize, o = some i →
         i.val = (t.val - f.val - 1) % 2 ^ UScalarTy.Usize.numBits) := by
  unfold justified_slots_ops.relative_index
  rw [checked_sub_eq]
  by_cases h1 : t.val < f.val
  · refine ⟨none, ?_, ?_, ?_⟩
    · simp [h1, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
    · simp; omega
    · intro i hi; cases hi
  · have hv := sub_val t f (by omega)
    by_cases h2 : t.val = f.val
    · refine ⟨none, ?_, ?_, ?_⟩
      · simp [h1, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          checked_sub_eq, hv, h2, core.option.Option.map]
      · simp; omega
      · intro i hi; cases hi
    · have h3 : ¬ ((⟨t.bv - f.bv⟩ : Std.U64)).val < (1#u64).val := by
        rw [hv]; simp; omega
      have hv2 := sub_val (⟨t.bv - f.bv⟩ : Std.U64) 1#u64 (by rw [hv]; simp; omega)
      have h4 : ¬ ((⟨t.bv - f.bv⟩ : Std.U64)).val = 0 := by rw [hv]; omega
      refine ⟨some (UScalar.cast .Usize
                (⟨(⟨t.bv - f.bv⟩ : Std.U64).bv - (1#u64).bv⟩ : Std.U64)), ?_, ?_, ?_⟩
      · simp [h1, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          checked_sub_eq, h3, h4, core.option.Option.map,
          justified_slots_ops.relative_index.closure.Insts.CoreOpsFunctionFnOnceTupleU64Usize.call_once]
      · simp; omega
      · intro i hi
        injection hi with hi
        rw [← hi, UScalar.cast_val_eq, hv2, hv]
        simp

/- ====================================================================
   Teorema 2: ida y vuelta. Despues de `set_justified(s)`,
   `is_slot_justified(s)` devuelve `Ok(true)`.
   ==================================================================== -/

/-- Lo que hace `set_justified` con la lista: o no la toca (el slot ya esta
    finalizado), o prende el bit del indice relativo, que estaba en rango. -/
theorem set_justified_eq (slots slots' : ssz.SszBitlist 262144#usize)
    (f t : Std.U64)
    (h : justified_slots_ops.set_justified slots f t = ok slots') :
    (justified_slots_ops.relative_index t f = ok none ∧ slots' = slots) ∨
    (∃ idx : Std.Usize, justified_slots_ops.relative_index t f = ok (some idx) ∧
       idx.val < slots.bits.val.length ∧
       slots'.bits.val = slots.bits.val.set idx.val true) := by
  unfold justified_slots_ops.set_justified at h
  obtain ⟨o, ho, h⟩ := bind_da_ok h
  cases o with
  | none =>
    left
    simp only [RustM.ok.injEq] at h
    exact ⟨ho, h.symm⟩
  | some idx =>
    right
    obtain ⟨⟨r, s1⟩, hset, h⟩ := bind_da_ok h
    obtain ⟨u, hexp, h⟩ := bind_da_ok h
    simp only [RustM.ok.injEq] at h
    subst h
    obtain ⟨r', hr', hbits, hok⟩ := set_eq slots idx true
    rw [hset] at hr'
    simp only [RustM.ok.injEq] at hr'
    subst hr'
    have hr : r = core.result.Result.Ok () := by
      unfold core.result.Result.expect at hexp
      cases r with
      | Ok x => rfl
      | Err e => simp [core.panicking.internal.panic] at hexp
    exact ⟨idx, ho, hok.mp hr, hbits⟩

theorem set_luego_is_justified (slots slots' : ssz.SszBitlist 262144#usize)
    (f t : Std.U64)
    (h : justified_slots_ops.set_justified slots f t = ok slots') :
    justified_slots_ops.is_slot_justified slots' f t =
      ok (core.result.Result.Ok true) := by
  rcases set_justified_eq slots slots' f t h with ⟨ho, -⟩ | ⟨idx, ho, hlt, hbits⟩
  · unfold justified_slots_ops.is_slot_justified
    rw [ho]
    rfl
  · unfold justified_slots_ops.is_slot_justified
    rw [ho]
    obtain ⟨n, hn, -⟩ := len_eq slots'
    simp [get_eq, hn, hbits, hlt, core.option.Option.ok_or]

/-- Invariante del loop de `extend_to_slot`: los primeros `k` bits de la lista
    nueva ya son los de la original, y de `k` en adelante siguen en `false`. -/
def Copiado (orig ext : List Bool) (k : Nat) : Prop :=
  orig.length ≤ ext.length ∧
  (∀ j, j < k → ext[j]? = orig[j]?) ∧
  (∀ j, k ≤ j → j < ext.length → ext[j]? = some false)

theorem copiado_ini (orig : List Bool) (c : Nat) (h : orig.length ≤ c) :
    Copiado orig (List.replicate c false) 0 := by
  refine ⟨by simpa using h, ?_, ?_⟩
  · intro j hj; omega
  · intro j _ hj
    simp at hj
    simp [List.getElem?_replicate, hj]

theorem copiado_true {orig ext : List Bool} {k : Nat}
    (h : Copiado orig ext k) (hk : k < orig.length) (ht : orig[k]? = some true) :
    Copiado orig (ext.set k true) (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simpa using h1, ?_, ?_⟩
  · intro j hj
    by_cases hjk : j = k
    · subst hjk
      rw [ht]
      simp [List.getElem?_set]
      omega
    · rw [List.getElem?_set]
      simp [Ne.symm hjk]
      exact h2 j (by omega)
  · intro j hj hlen
    simp at hlen
    rw [List.getElem?_set]
    have : ¬ k = j := by omega
    simp [this]
    exact h3 j (by omega) hlen

theorem copiado_false {orig ext : List Bool} {k : Nat}
    (h : Copiado orig ext k) (hk : k < orig.length) (hf : ¬ orig[k]? = some true) :
    Copiado orig ext (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · intro j hj
    by_cases hjk : j = k
    · subst hjk
      rw [h3 j (Nat.le_refl _) (by omega)]
      have hget : orig[j]? = some orig[j] := List.getElem?_eq_getElem hk
      rw [hget] at hf ⊢
      cases hb : orig[j] <;> simp_all
    · exact h2 j (by omega)
  · intro j hj hlen
    exact h3 j (by omega) hlen

theorem copiado_fin {orig ext : List Bool}
    (h : Copiado orig ext orig.length) :
    ext = orig ++ List.replicate (ext.length - orig.length) false := by
  obtain ⟨h1, h2, h3⟩ := h
  apply List.ext_getElem?
  intro j
  by_cases hj : j < orig.length
  · rw [h2 j hj, List.getElem?_append_left hj]
  · by_cases hj2 : j < ext.length
    · rw [h3 j (by omega) hj2, List.getElem?_append_right (by omega),
        List.getElem?_replicate]
      simp
      omega
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- Invariante del loop de `shift_window`: los primeros `k` bits de la lista
    nueva son los de la original corridos `d` lugares. -/
def Desplazado (orig nuevo : List Bool) (d k : Nat) : Prop :=
  (∀ j, j < k → nuevo[j]? = orig[j + d]?) ∧
  (∀ j, k ≤ j → j < nuevo.length → nuevo[j]? = some false)

theorem desplazado_ini (orig : List Bool) (d c : Nat) :
    Desplazado orig (List.replicate c false) d 0 := by
  refine ⟨?_, ?_⟩
  · intro j hj; omega
  · intro j _ hj
    simp at hj
    simp [List.getElem?_replicate, hj]

theorem desplazado_true {orig nuevo : List Bool} {d k : Nat}
    (h : Desplazado orig nuevo d k) (hk : k < nuevo.length)
    (ht : orig[k + d]? = some true) :
    Desplazado orig (nuevo.set k true) d (k + 1) := by
  obtain ⟨h2, h3⟩ := h
  refine ⟨?_, ?_⟩
  · intro j hj
    by_cases hjk : j = k
    · subst hjk
      rw [ht]
      simp [List.getElem?_set]
      omega
    · rw [List.getElem?_set]
      simp [Ne.symm hjk]
      exact h2 j (by omega)
  · intro j hj hlen
    simp at hlen
    rw [List.getElem?_set]
    have : ¬ k = j := by omega
    simp [this]
    exact h3 j (by omega) hlen

theorem desplazado_false {orig nuevo : List Bool} {d k : Nat}
    (h : Desplazado orig nuevo d k) (hk : k < nuevo.length)
    (hkd : k + d < orig.length) (hf : orig[k + d]?.getD false = false) :
    Desplazado orig nuevo d (k + 1) := by
  obtain ⟨h2, h3⟩ := h
  refine ⟨?_, ?_⟩
  · intro j hj
    by_cases hjk : j = k
    · subst hjk
      rw [h3 j (Nat.le_refl _) hk]
      have hget : orig[j + d]? = some orig[j + d] := List.getElem?_eq_getElem hkd
      rw [hget] at hf ⊢
      simp at hf
      simp [hf]
    · exact h2 j (by omega)
  · intro j hj hlen
    exact h3 j (by omega) hlen

theorem desplazado_fin {orig nuevo : List Bool} {d : Nat}
    (hlen : nuevo.length = orig.length - d)
    (h : Desplazado orig nuevo d nuevo.length) :
    nuevo = orig.drop d := by
  obtain ⟨h2, -⟩ := h
  apply List.ext_getElem?
  intro j
  by_cases hj : j < nuevo.length
  · rw [h2 j hj, List.getElem?_drop, Nat.add_comm]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/- ====================================================================
   Lemas `@[spec]` con contenido para la lista de bits.
   ==================================================================== -/

theorem bl_get_spec {N : Std.Usize} (s : ssz.SszBitlist N) (i : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.get s i
    ⦃ PostCond.mayThrow (fun r => ⌜ r = s.bits.val[i.val]? ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    rw [get_eq] at hv
    simp only [RustM.ok.injEq] at hv
    exact hv.symm)

theorem bl_set_spec {N : Std.Usize} (s : ssz.SszBitlist N) (i : Std.Usize) (v : Bool) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.set s i v
    ⦃ PostCond.mayThrow (fun r => ⌜ r.2.bits.val = s.bits.val.set i.val v ∧
        (r.1 = core.result.Result.Ok () ↔ i.val < s.bits.val.length) ⌝) ⦄ :=
  triple_mayThrow_of (fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := set_eq s i v
    rw [hr] at hr'
    simp only [RustM.ok.injEq] at hr'
    subst hr'
    exact ⟨h1, h2⟩)

theorem opt_eq_true_spec (o : core.option.Option Bool) :
    ⦃ ⌜ True ⌝ ⦄
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
      core.Bool.Insts.CoreCmpPartialEqBool o (core.option.Option.Some true)
    ⦃ PostCond.mayThrow (fun r => ⌜ r = true ↔ o = some true ⌝) ⦄ :=
  triple_mayThrow_of (fun r hr => by
    unfold core.option.Option.Insts.CoreCmpPartialEqOption.eq at hr
    cases o with
    | none =>
      simp at hr
      subst hr
      simp
    | some a =>
      simp [core.Bool.Insts.CoreCmpPartialEqBool] at hr
      subst hr
      cases a <;> simp)

section
attribute [local spec] bl_get_spec bl_set_spec opt_eq_true_spec
  ST7.expect_modelo_spec

theorem extend_loop_spec (slots ext0 : ssz.SszBitlist 262144#usize)
    (n : Std.Usize) (hn : n.val = slots.bits.val.length)
    (h0 : Copiado slots.bits.val ext0.bits.val 0) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.extend_to_slot_loop { start := 0#usize, «end» := n } slots ext0
    ⦃ PostCond.mayThrow
        (fun r => ⌜ Copiado slots.bits.val r.bits.val slots.bits.val.length ⌝) ⦄ := by
  unfold justified_slots_ops.extend_to_slot_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × (ssz.SszBitlist 262144#usize) =>
       x.1.«end» = n ∧ x.1.start.val ≤ n.val ∧
       Copiado slots.bits.val x.2.bits.val x.1.start.val)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · exact ⟨rfl, by simp, h0⟩
  · intro x hinv
    obtain ⟨iter, ext⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    obtain ⟨hend, hle, hcop⟩ := hinv
    simp only at hend hle hcop
    subst hend
    unfold justified_slots_ops.extend_to_slot_loop.body
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | trivial
      | simp [PostCond.div, PostCond.mayThrow]
    -- Rama 1: el bit original esta en uno y se copia.
    · rename_i hlt s hs o ho b hb hbo r hr u hu
      refine ⟨by omega, ?_⟩
      rw [hs, hr.1]
      exact copiado_true hcop (by omega) (by rw [← ho]; exact hbo.mp hb)
    -- Rama 2: el bit original esta en cero y no se toca nada.
    · rename_i hlt s hs o ho b hb hbo
      refine ⟨by omega, ?_⟩
      rw [hs]
      exact copiado_false hcop (by omega) (by rw [← ho]; exact fun h => hb (hbo.mpr h))
    -- Rama 3: se termino el rango.
    · rename_i hge
      simp only [PostCond.okAssertion]
      have hfin : desde.val = slots.bits.val.length := by omega
      rw [← hfin]
      exact hcop
end

theorem extend_loop_spec' (slots ext0 : ssz.SszBitlist 262144#usize)
    (n : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.extend_to_slot_loop { start := 0#usize, «end» := n } slots ext0
    ⦃ PostCond.mayThrow
        (fun r => ⌜ n.val = slots.bits.val.length →
                    Copiado slots.bits.val ext0.bits.val 0 →
                    Copiado slots.bits.val r.bits.val slots.bits.val.length ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv hn h0 =>
    of_triple_mayThrow (extend_loop_spec slots ext0 n hn h0) hv)

theorem bl_len_spec {N : Std.Usize} (s : ssz.SszBitlist N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.len s
    ⦃ PostCond.mayThrow (fun r => ⌜ r.val = s.bits.val.length ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨n, hn, hval⟩ := len_eq s
    rw [hv] at hn
    simp only [RustM.ok.injEq] at hn
    subst hn
    exact hval)

theorem bl_with_length_spec (N l : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.with_length N l
    ⦃ PostCond.mayThrow (fun r => ⌜ ∀ b, r = core.result.Result.Ok b →
        b.bits.val = List.replicate l.val false ⌝) ⦄ :=
  triple_mayThrow_of (fun r hr b hb => by
    subst hb
    exact with_length_eq N l b hr)

theorem relative_index_trivial_spec (t f : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.relative_index t f
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

section
attribute [local spec] relative_index_trivial_spec bl_len_spec
  bl_with_length_spec ST7.expect_modelo_spec extend_loop_spec'

theorem extend_to_slot_spec (slots : ssz.SszBitlist 262144#usize) (f t : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.extend_to_slot slots f t
    ⦃ PostCond.mayThrow (fun r => ⌜ r.bits.val = slots.bits.val ++
        List.replicate (r.bits.val.length - slots.bits.val.length) false ⌝) ⦄ := by
  unfold justified_slots_ops.extend_to_slot
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp; done)
  -- Queda la rama que arma la lista nueva y corre el loop de copia.
  · rename_i o idx ho rc hrc n hnge hn r hwl ext hext res hloop
    have hbits := hwl ext hext
    have h0 : Copiado slots.bits.val ext.bits.val 0 := by
      rw [hbits]
      exact copiado_ini _ _ (by scalar_tac)
    exact copiado_fin (hloop hn h0)
end

/- ====================================================================
   El loop de `shift_window`.
   ==================================================================== -/

theorem unwrap_or_spec {T : Type} (o : core.option.Option T) (d : T) :
    ⦃ ⌜ True ⌝ ⦄ core.option.Option.unwrap_or o d
    ⦃ PostCond.mayThrow (fun r => ⌜ r = o.getD d ⌝) ⦄ :=
  triple_mayThrow_of (fun r hr => by
    unfold core.option.Option.unwrap_or at hr
    cases o with
    | none => simp only [RustM.ok.injEq] at hr; subst hr; rfl
    | some a => simp only [RustM.ok.injEq] at hr; subst hr; rfl)

theorem unwrap_modelo_spec {T E : Type} (inst : core.fmt.Debug E)
    (r : core.result.Result T E) :
    ⦃ ⌜ True ⌝ ⦄ core.result.Result.unwrap inst r
    ⦃ PostCond.mayThrow (fun t => ⌜ r = core.result.Result.Ok t ⌝) ⦄ :=
  triple_mayThrow_of (fun t ht => by
    unfold core.result.Result.unwrap at ht
    cases r with
    | Ok x =>
      simp only [RustM.ok.injEq] at ht
      subst ht; rfl
    | Err e => simp [core.panicking.internal.panic] at ht)

section
attribute [local spec] bl_get_spec bl_set_spec unwrap_or_spec unwrap_modelo_spec

theorem shift_loop_spec (slots nb0 : ssz.SszBitlist 262144#usize)
    (delta rem : Std.Usize)
    (hlen0 : nb0.bits.val.length = rem.val)
    (hsum : rem.val + delta.val = slots.bits.val.length)
    (h0 : Desplazado slots.bits.val nb0.bits.val delta.val 0) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.shift_window_loop { start := 0#usize, «end» := rem } slots delta nb0
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.bits.val.length = rem.val ∧
                    Desplazado slots.bits.val r.bits.val delta.val rem.val ⌝) ⦄ := by
  unfold justified_slots_ops.shift_window_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × (ssz.SszBitlist 262144#usize) =>
       x.1.«end» = rem ∧ x.1.start.val ≤ rem.val ∧
       x.2.bits.val.length = rem.val ∧
       Desplazado slots.bits.val x.2.bits.val delta.val x.1.start.val)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · exact ⟨rfl, by simp, hlen0, h0⟩
  · intro x hinv
    obtain ⟨iter, nb⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    obtain ⟨hend, hle, hlen, hdes⟩ := hinv
    simp only at hend hle hlen hdes
    subst hend
    unfold justified_slots_ops.shift_window_loop.body
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | trivial
      | simp [PostCond.div, PostCond.mayThrow]
    -- Rama 1: el bit corrido esta en uno y se copia.
    · rename_i hlt s hs i1 hi1 o ho b hb hbo r hr u hu
      refine ⟨by omega, ?_, ?_⟩
      · rw [hr.1]; simpa using hlen
      · rw [hs, hr.1]
        refine desplazado_true hdes (by omega) ?_
        have ho' : slots.bits.val[desde.val + delta.val]? = o := by rw [ho, hi1]
        rw [ho']
        subst hbo
        cases o with
        | none => simp at hb
        | some a => simp at hb; rw [hb]
    -- Rama 2: el bit corrido esta en cero.
    · rename_i hlt s hs i1 hi1 o ho b hb hbo
      refine ⟨by omega, hlen, ?_⟩
      rw [hs]
      refine desplazado_false hdes (by omega) (by omega) ?_
      have ho' : slots.bits.val[desde.val + delta.val]? = o := by rw [ho, hi1]
      rw [ho', ← hbo]
      simpa using hb
    -- Rama 3: se termino el rango.
    · rename_i hge
      simp only [PostCond.okAssertion]
      have hfin : desde.val = hasta.val := by omega
      rw [← hfin]
      exact ⟨by omega, hdes⟩
end

theorem shift_loop_spec' (slots nb0 : ssz.SszBitlist 262144#usize)
    (delta rem : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.shift_window_loop { start := 0#usize, «end» := rem } slots delta nb0
    ⦃ PostCond.mayThrow
        (fun r => ⌜ nb0.bits.val.length = rem.val →
                    rem.val + delta.val = slots.bits.val.length →
                    Desplazado slots.bits.val nb0.bits.val delta.val 0 →
                    (r.bits.val.length = rem.val ∧
                     Desplazado slots.bits.val r.bits.val delta.val rem.val) ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv h1 h2 h3 =>
    of_triple_mayThrow (shift_loop_spec slots nb0 delta rem h1 h2 h3) hv)

theorem bl_new_spec (N : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.new N
    ⦃ PostCond.mayThrow (fun r => ⌜ r.bits.val = [] ⌝) ⦄ :=
  triple_mayThrow_of (fun r hr => by
    simp [ssz.SszBitlist.new, alloc.vec.Vec.new,
      rust_primitives.sequence.seq_empty] at hr
    rw [← hr]
    rfl)

section
attribute [local spec] bl_len_spec bl_with_length_spec bl_new_spec
  ST7.expect_modelo_spec shift_loop_spec'

theorem shift_window_spec (slots : ssz.SszBitlist 262144#usize) (delta : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.shift_window slots delta
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.bits.val = slots.bits.val.drop delta.val ⌝) ⦄ := by
  unfold justified_slots_ops.shift_window
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all; done)
  -- Queda la rama que arma la lista nueva y corre el loop de copia.
  · rename_i hne n hnge hn rem hrem hle r hwl nb hnb res hloop
    have hbits := hwl nb hnb
    have h1 : nb.bits.val.length = rem.val := by rw [hbits]; simp
    have h2 : rem.val + delta.val = slots.bits.val.length := by omega
    have h3 : Desplazado slots.bits.val nb.bits.val delta.val 0 := by
      rw [hbits]; exact desplazado_ini _ _ _
    obtain ⟨hl, hd⟩ := hloop h1 h2 h3
    refine desplazado_fin (by omega) ?_
    rw [hl]; exact hd
end

/- ====================================================================
   Los enunciados, como ecuaciones.
   ==================================================================== -/

/-- Teorema 1, forma exacta: `extend_to_slot` solo agrega bits en cero al
    final. -/
theorem extend_to_slot_eq (slots slots' : ssz.SszBitlist 262144#usize)
    (f t : Std.U64)
    (h : justified_slots_ops.extend_to_slot slots f t = ok slots') :
    slots'.bits.val = slots.bits.val ++
      List.replicate (slots'.bits.val.length - slots.bits.val.length) false :=
  of_triple_mayThrow (extend_to_slot_spec slots f t) h

/-- Teorema 1: `extend_to_slot` no pierde bits. Todo bit que estaba en uno
    sigue en uno, en la misma posicion. -/
theorem extend_to_slot_no_pierde_bits (slots slots' : ssz.SszBitlist 262144#usize)
    (f t : Std.U64)
    (h : justified_slots_ops.extend_to_slot slots f t = ok slots')
    (j : Nat) (b : Bool) (hj : slots.bits.val[j]? = some b) :
    slots'.bits.val[j]? = some b := by
  rw [extend_to_slot_eq slots slots' f t h]
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj
  rw [List.getElem?_append_left hlt]
  exact hj

/-- Teorema 3: `shift_window` corre sin deformar. La lista nueva es la vieja
    sin sus primeros `delta` bits. -/
theorem shift_window_eq (slots slots' : ssz.SszBitlist 262144#usize)
    (delta : Std.Usize)
    (h : justified_slots_ops.shift_window slots delta = ok slots') :
    slots'.bits.val = slots.bits.val.drop delta.val :=
  of_triple_mayThrow (shift_window_spec slots delta) h

/-- Teorema 3, bit a bit: el bit en `i + delta` antes es el bit en `i`
    despues. -/
theorem shift_window_corre (slots slots' : ssz.SszBitlist 262144#usize)
    (delta : Std.Usize)
    (h : justified_slots_ops.shift_window slots delta = ok slots') (i : Nat) :
    slots'.bits.val[i]? = slots.bits.val[i + delta.val]? := by
  rw [shift_window_eq slots slots' delta h, List.getElem?_drop, Nat.add_comm]

/-- Lo que `is_slot_justified` lee: si el slot esta por encima del finalizado
    y responde `Ok b`, es porque el bit de su indice relativo vale `b`. -/
theorem is_slot_justified_lee (slots : ssz.SszBitlist 262144#usize)
    (f s : Std.U64) (idx : Std.Usize) (b : Bool)
    (ho : justified_slots_ops.relative_index s f = ok (some idx))
    (hj : justified_slots_ops.is_slot_justified slots f s =
            ok (core.result.Result.Ok b)) :
    slots.bits.val[idx.val]? = some b := by
  unfold justified_slots_ops.is_slot_justified at hj
  rw [ho] at hj
  obtain ⟨n, hn, -⟩ := len_eq slots
  cases hg : slots.bits.val[idx.val]? with
  | none => simp [get_eq, hn, hg, core.option.Option.ok_or] at hj
  | some v =>
    simp [get_eq, hn, hg, core.option.Option.ok_or] at hj
    rw [hj]

/-- Y al reves: si el bit del indice relativo vale `b`, responde `Ok b`. -/
theorem is_slot_justified_de_bit (slots : ssz.SszBitlist 262144#usize)
    (f s : Std.U64) (idx : Std.Usize) (b : Bool)
    (ho : justified_slots_ops.relative_index s f = ok (some idx))
    (hbit : slots.bits.val[idx.val]? = some b) :
    justified_slots_ops.is_slot_justified slots f s =
      ok (core.result.Result.Ok b) := by
  unfold justified_slots_ops.is_slot_justified
  rw [ho]
  obtain ⟨n, hn, -⟩ := len_eq slots
  simp [get_eq, hn, hbit, core.option.Option.ok_or]

/-- Por encima del finalizado, `relative_index` da el indice, y si la
    distancia entra en un `usize` el indice es la distancia menos uno. -/
theorem relative_index_arriba (s f : Std.U64) (hfs : f.val < s.val)
    (hfit : s.val - f.val - 1 < 2 ^ UScalarTy.Usize.numBits) :
    ∃ idx : Std.Usize, justified_slots_ops.relative_index s f = ok (some idx) ∧
      idx.val = s.val - f.val - 1 := by
  obtain ⟨o, ho, hnone, hval⟩ := relative_index_eq s f
  cases o with
  | none => have := hnone.mp rfl; omega
  | some idx =>
    exact ⟨idx, ho, by rw [hval idx rfl]; exact Nat.mod_eq_of_lt hfit⟩

/-- `extend_to_slot` no cambia ninguna respuesta que ya se podia leer. -/
theorem extend_to_slot_conserva_respuestas
    (slots slots' : ssz.SszBitlist 262144#usize) (f t s : Std.U64) (b : Bool)
    (hext : justified_slots_ops.extend_to_slot slots f t = ok slots')
    (hj : justified_slots_ops.is_slot_justified slots f s =
            ok (core.result.Result.Ok b)) :
    justified_slots_ops.is_slot_justified slots' f s =
      ok (core.result.Result.Ok b) := by
  obtain ⟨o, ho, -, -⟩ := relative_index_eq s f
  cases o with
  | none =>
    unfold justified_slots_ops.is_slot_justified at hj ⊢
    rw [ho] at hj ⊢
    exact hj
  | some idx =>
    have hbit := is_slot_justified_lee slots f s idx b ho hj
    exact is_slot_justified_de_bit slots' f s idx b ho
      (extend_to_slot_no_pierde_bits slots slots' f t hext idx.val b hbit)

/-- Teorema 4, el compuesto. Cuando la finalidad avanza de `f` a `f'` y la
    ventana se corre esa distancia, todo slot que sigue por encima del limite
    nuevo se reporta igual que antes: justificado si lo estaba, no justificado
    si no. Involucra `relative_index`, `is_slot_justified` y `shift_window`, y
    los dos sistemas de indices (relativo a `f` y relativo a `f'`). -/
theorem finalizar_conserva_justificados
    (slots slots' : ssz.SszBitlist 262144#usize) (f f' s : Std.U64)
    (delta : Std.Usize) (b : Bool)
    (hff : f.val ≤ f'.val) (hfs : f'.val < s.val)
    (hdelta : delta.val = f'.val - f.val)
    (hfit : s.val - f.val - 1 < 2 ^ UScalarTy.Usize.numBits)
    (hj : justified_slots_ops.is_slot_justified slots f s =
            ok (core.result.Result.Ok b))
    (hsh : justified_slots_ops.shift_window slots delta = ok slots') :
    justified_slots_ops.is_slot_justified slots' f' s =
      ok (core.result.Result.Ok b) := by
  obtain ⟨idx, ho, hidx⟩ := relative_index_arriba s f (by omega) hfit
  obtain ⟨idx', ho', hidx'⟩ := relative_index_arriba s f' hfs (by omega)
  have hbit := is_slot_justified_lee slots f s idx b ho hj
  refine is_slot_justified_de_bit slots' f' s idx' b ho' ?_
  rw [shift_window_corre slots slots' delta hsh]
  have e : idx'.val + delta.val = idx.val := by omega
  rw [e]
  exact hbit

end JS

/- ===========================================================================
   Teorema 10: la ventana de slots no entra en panico (17 nov 2026)

   Todo lo anterior dice "si la funcion devuelve, entonces...". Esto es lo
   otro: que DEVUELVE. Para las cuatro funciones de `justified_slots_ops`:

     - `is_slot_justified` nunca entra en panico, sin condiciones.
     - `set_justified` entra en panico EXACTAMENTE cuando `is_slot_justified`
       rechaza el slot (`Err`: esta fuera de la ventana). Son dos lemas: si
       responde `Ok`, `set_justified` devuelve; si responde `Err`,
       `set_justified = fail panic`. Es el `expect("index out of bounds")`.
     - `extend_to_slot` devuelve si el slot pedido esta a lo sumo 262144 por
       encima del finalizado. Cubre el `expect("capacity limit exceeded")`,
       el `expect("index within capacity")` del loop y el desborde de
       `required_idx + 1`.
     - `shift_window` devuelve si la lista no pasa de 262144. Cubre el
       `expect`, el `unwrap` del loop y el desborde de `i + delta`.

   Y en el punto de uso: despues de un voto que `is_valid_vote` acepta,
   `set_justified` sobre su target no entra en panico. Es la llamada que hace
   el loop de `process_attestations`, con el mismo estado entre las dos, asi
   que ese `expect` no se puede disparar ahi.

   Como esta armado. Las ternas de antes usaban `PostCond.mayThrow`, que
   tolera el panico y la divergencia. Estas usan `⇓`, que no tolera ninguna
   de las dos, asi que cada punto donde el codigo podria abortar aparece como
   un objetivo a demostrar: que el indice esta en rango, que la suma no
   desborda, que lo pedido entra en la capacidad. Y `loop_spec` recibe una
   medida de terminacion de verdad (`end - start`) en vez de la constante de
   antes. Dos puentes nuevos, `triple_total_of` y `of_triple_total`, van y
   vienen entre "devuelve `v` y vale `P v`" y la terna total.

   Con esto el teorema 4 queda sin condicional de panico
   (`finalizar_conserva_justificados_total`), y se despeja la duda de si los
   enunciados del teorema 9 eran vacios: `shift_window` y `extend_to_slot`
   devuelven.

   Lo que NO esta: que las hipotesis de capacidad valgan en todo estado
   alcanzable (que la ventana nunca pase de 262144, que el slot nunca este
   mas lejos que eso del finalizado). Son invariantes del estado, no de este
   modulo.
   =========================================================================== -/

namespace NP
open mini_stf
open Std.Tactic
open ST3 JS

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

/-- De "devuelve `v` y vale `P v`" a terna de correccion TOTAL. -/
theorem triple_total_of {α : Type} {x : RustM α} {P : α → Prop}
    (h : ∃ v, x = ok v ∧ P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  obtain ⟨v, rfl, hv⟩ := h
  simp [Triple, WP.wp, PredTrans.apply, hv]

/-- Y de vuelta: una terna total dice que la funcion DEVUELVE. -/
theorem of_triple_total {α : Type} {x : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) : ∃ v, x = ok v ∧ P v := by
  cases x with
  | ok v => exact ⟨v, rfl, by simpa [Triple, WP.wp, PredTrans.apply] using h⟩
  | fail e => simp [Triple, WP.wp, PredTrans.apply] at h
  | div => simp [Triple, WP.wp, PredTrans.apply] at h

theorem bl_get_total {N : Std.Usize} (s : ssz.SszBitlist N) (i : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.get s i ⦃ ⇓ r => ⌜ r = s.bits.val[i.val]? ⌝ ⦄ :=
  triple_total_of ⟨_, get_eq s i, rfl⟩

theorem bl_set_total {N : Std.Usize} (s : ssz.SszBitlist N) (i : Std.Usize) (v : Bool) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.set s i v
    ⦃ ⇓ r => ⌜ r.2.bits.val = s.bits.val.set i.val v ∧
        (r.1 = core.result.Result.Ok () ↔ i.val < s.bits.val.length) ⌝ ⦄ :=
  triple_total_of (set_eq s i v)

theorem unwrap_or_total {T : Type} (o : core.option.Option T) (d : T) :
    ⦃ ⌜ True ⌝ ⦄ core.option.Option.unwrap_or o d ⦃ ⇓ r => ⌜ r = o.getD d ⌝ ⦄ :=
  triple_total_of ⟨o.getD d, by cases o <;> rfl, rfl⟩

theorem unwrap_total {T E : Type} (inst : core.fmt.Debug E)
    (r : core.result.Result T E) :
    ⦃ ⌜ ∃ t, r = core.result.Result.Ok t ⌝ ⦄ core.result.Result.unwrap inst r
    ⦃ ⇓ v => ⌜ r = core.result.Result.Ok v ⌝ ⦄ := by
  cases r with
  | Ok x => simp [core.result.Result.unwrap, Triple, WP.wp, PredTrans.apply]
  | Err e => simp [Triple, WP.wp, PredTrans.apply]

theorem expect_total {T E : Type} (inst : core.fmt.Debug E)
    (r : core.result.Result T E) (msg : Str) :
    ⦃ ⌜ ∃ t, r = core.result.Result.Ok t ⌝ ⦄ core.result.Result.expect inst r msg
    ⦃ ⇓ v => ⌜ r = core.result.Result.Ok v ⌝ ⦄ := by
  cases r with
  | Ok x => simp [core.result.Result.expect, Triple, WP.wp, PredTrans.apply]
  | Err e => simp [Triple, WP.wp, PredTrans.apply]

theorem opt_eq_true_total (o : core.option.Option Bool) :
    ⦃ ⌜ True ⌝ ⦄
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
      core.Bool.Insts.CoreCmpPartialEqBool o (core.option.Option.Some true)
    ⦃ ⇓ r => ⌜ r = true ↔ o = some true ⌝ ⦄ :=
  triple_total_of (by
    unfold core.option.Option.Insts.CoreCmpPartialEqOption.eq
    cases o with
    | none => exact ⟨false, rfl, by simp⟩
    | some a => exact ⟨a == true, rfl, by cases a <;> simp⟩)

theorem bl_len_total {N : Std.Usize} (s : ssz.SszBitlist N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.len s ⦃ ⇓ r => ⌜ r.val = s.bits.val.length ⌝ ⦄ :=
  triple_total_of (len_eq s)

/-- `with_length` nunca entra en panico: devuelve `Err` si no entra en la
    capacidad, y si entra devuelve la lista de ceros. -/
theorem with_length_total_eq (N l : Std.Usize) :
    ∃ r, ssz.SszBitlist.with_length N l = ok r ∧
      (l.val ≤ N.val → ∃ b, r = core.result.Result.Ok b ∧
         b.bits.val = List.replicate l.val false) := by
  have hclone : (core.Bool.Insts.CoreCloneClone.clone) =
      fun x : Bool => (ok x : RustM Bool) := by
    funext x; rfl
  by_cases hN : N.val < l.val
  · refine ⟨core.result.Result.Err (), ?_, fun h => by omega⟩
    unfold ssz.SszBitlist.with_length
    simp [hN]
  · have hex : ∃ b : ssz.SszBitlist N,
        ssz.SszBitlist.with_length N l = ok (core.result.Result.Ok b) := by
      unfold ssz.SszBitlist.with_length
      simp [alloc.vec.from_elem, rust_primitives.sequence.seq_create, hclone, mapM_ok]
      by_cases h0 : l.val = 0
      · simp [hN, h0]
      · have hlt : l.val - 1 < Usize.max := by scalar_tac
        simp [hN, h0, hlt]
    obtain ⟨b, hb⟩ := hex
    exact ⟨_, hb, fun _ => ⟨b, rfl, with_length_eq N l b hb⟩⟩

theorem bl_with_length_total (N l : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.with_length N l
    ⦃ ⇓ r => ⌜ l.val ≤ N.val → ∃ b, r = core.result.Result.Ok b ∧
        b.bits.val = List.replicate l.val false ⌝ ⦄ :=
  triple_total_of (with_length_total_eq N l)

section
attribute [local spec] bl_get_total bl_set_total unwrap_or_total unwrap_total

/-- El loop de `shift_window` TERMINA y no entra en panico, y deja lo que
    dice el teorema 3. -/
theorem shift_loop_total (slots nb0 : ssz.SszBitlist 262144#usize)
    (delta rem : Std.Usize)
    (hlen0 : nb0.bits.val.length = rem.val)
    (hsum : rem.val + delta.val = slots.bits.val.length)
    (h0 : Desplazado slots.bits.val nb0.bits.val delta.val 0) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.shift_window_loop { start := 0#usize, «end» := rem } slots delta nb0
    ⦃ ⇓ r => ⌜ r.bits.val.length = rem.val ∧
               Desplazado slots.bits.val r.bits.val delta.val rem.val ⌝ ⦄ := by
  unfold justified_slots_ops.shift_window_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × (ssz.SszBitlist 262144#usize) =>
       x.1.«end» = rem ∧ x.1.start.val ≤ rem.val ∧
       x.2.bits.val.length = rem.val ∧
       Desplazado slots.bits.val x.2.bits.val delta.val x.1.start.val)
    (γ := Nat) (rel := (· < ·))
    (termination := fun x => x.1.«end».val - x.1.start.val)
  · exact Nat.lt_wfRel.wf
  · exact ⟨rfl, by simp, hlen0, h0⟩
  · intro x hinv
    obtain ⟨iter, nb⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    obtain ⟨hend, hle, hlen, hdes⟩ := hinv
    simp only at hend hle hlen hdes
    subst hend
    unfold justified_slots_ops.shift_window_loop.body
    hax_mvcgen
    -- 1. El `unwrap` del `set` no entra en panico: el indice esta en rango.
    · rename_i hlt s hs i1 hi1 o ho b hb hbo r hr
      exact ⟨(), hr.2.mpr (by omega)⟩
    -- 2. Bit en uno: se copia, y el contador baja.
    · rename_i hlt s hs i1 hi1 o ho b hb hbo r hr u hu
      refine ⟨⟨trivial, by omega, ?_, ?_⟩, Or.inl (by omega)⟩
      · rw [hr.1]; simpa using hlen
      · rw [hs, hr.1]
        refine desplazado_true hdes (by omega) ?_
        have ho' : slots.bits.val[desde.val + delta.val]? = o := by rw [ho, hi1]
        rw [ho']
        subst hbo
        cases o with
        | none => simp at hb
        | some a => simp at hb; rw [hb]
    -- 3. Bit en cero: no se toca nada, y el contador baja.
    · rename_i hlt s hs i1 hi1 o ho b hb hbo
      refine ⟨⟨trivial, by omega, hlen, ?_⟩, Or.inl (by omega)⟩
      rw [hs]
      refine desplazado_false hdes (by omega) (by omega) ?_
      have ho' : slots.bits.val[desde.val + delta.val]? = o := by rw [ho, hi1]
      rw [ho', ← hbo]
      simpa using hb
    -- 4. `i + delta` no desborda: queda adentro de la lista original.
    · rename_i hlt s hs hov
      exfalso
      have := slots.bits.property
      scalar_tac
    -- 5. Se termino el rango.
    · rename_i hge
      have hfin : desde.val = hasta.val := by omega
      show nb.bits.val.length = hasta.val ∧
        Desplazado slots.bits.val nb.bits.val delta.val hasta.val
      rw [← hfin]
      exact ⟨by omega, hdes⟩
end

section
attribute [local spec] bl_get_total bl_set_total opt_eq_true_total expect_total

/-- El loop de `extend_to_slot` TERMINA y no entra en panico, y deja lo que
    dice el teorema 1. -/
theorem extend_loop_total (slots ext0 : ssz.SszBitlist 262144#usize)
    (n : Std.Usize) (hn : n.val = slots.bits.val.length)
    (h0 : Copiado slots.bits.val ext0.bits.val 0) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.extend_to_slot_loop { start := 0#usize, «end» := n } slots ext0
    ⦃ ⇓ r => ⌜ Copiado slots.bits.val r.bits.val slots.bits.val.length ⌝ ⦄ := by
  unfold justified_slots_ops.extend_to_slot_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × (ssz.SszBitlist 262144#usize) =>
       x.1.«end» = n ∧ x.1.start.val ≤ n.val ∧
       Copiado slots.bits.val x.2.bits.val x.1.start.val)
    (γ := Nat) (rel := (· < ·))
    (termination := fun x => x.1.«end».val - x.1.start.val)
  · exact Nat.lt_wfRel.wf
  · exact ⟨rfl, by simp, h0⟩
  · intro x hinv
    obtain ⟨iter, ext⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    obtain ⟨hend, hle, hcop⟩ := hinv
    simp only at hend hle hcop
    subst hend
    unfold justified_slots_ops.extend_to_slot_loop.body
    hax_mvcgen
    -- 1. El `expect` del `set` no entra en panico: el indice esta en rango.
    · rename_i hlt s hs o ho b hb hbo r hr
      have := hcop.1
      exact ⟨(), hr.2.mpr (by omega)⟩
    -- 2. Bit en uno: se copia, y el contador baja.
    · rename_i hlt s hs o ho b hb hbo r hr u hu
      refine ⟨⟨trivial, by omega, ?_⟩, Or.inl (by omega)⟩
      rw [hs, hr.1]
      exact copiado_true hcop (by omega) (by rw [← ho]; exact hbo.mp hb)
    -- 3. Bit en cero: no se toca nada, y el contador baja.
    · rename_i hlt s hs o ho b hb hbo
      refine ⟨⟨trivial, by omega, ?_⟩, Or.inl (by omega)⟩
      rw [hs]
      exact copiado_false hcop (by omega) (by rw [← ho]; exact fun h => hb (hbo.mpr h))
    -- 4. Se termino el rango.
    · rename_i hge
      have hfin : desde.val = slots.bits.val.length := by omega
      show Copiado slots.bits.val ext.bits.val slots.bits.val.length
      rw [← hfin]
      exact hcop
end

theorem bl_new_total (N : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszBitlist.new N ⦃ ⇓ r => ⌜ r.bits.val = [] ⌝ ⦄ :=
  triple_total_of (by
    refine ⟨{ bits := Slice.new Bool }, ?_, rfl⟩
    simp [ssz.SszBitlist.new, alloc.vec.Vec.new, rust_primitives.sequence.seq_empty])

theorem relative_index_total (t f : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.relative_index t f
    ⦃ ⇓ o => ⌜ justified_slots_ops.relative_index t f = ok o ∧
        ∀ i : Std.Usize, o = some i → i.val ≤ t.val - f.val - 1 ⌝ ⦄ :=
  triple_total_of (by
    obtain ⟨o, ho, -, hval⟩ := relative_index_eq t f
    exact ⟨o, ho, ho, fun i hi => by rw [hval i hi]; exact Nat.mod_le _ _⟩)

section
attribute [local spec] bl_len_total bl_with_length_total bl_new_total
  expect_total shift_loop_total

/-- `shift_window` no entra en panico ni se cuelga, si la lista no pasa de
    su capacidad. Y devuelve lo que dice el teorema 3. -/
theorem shift_window_total_spec (slots : ssz.SszBitlist 262144#usize)
    (delta : Std.Usize) (hcap : slots.bits.val.length ≤ 262144) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.shift_window slots delta
    ⦃ ⇓ r => ⌜ r.bits.val = slots.bits.val.drop delta.val ⌝ ⦄ := by
  unfold justified_slots_ops.shift_window
  hax_mvcgen
  -- delta = 0: no se toca nada.
  · rename_i h
    subst h
    simp
  -- delta >= largo: queda vacia.
  · rename_i hne n hge hn hnew
    rw [hnew]
    exact (List.drop_eq_nil_of_le (by scalar_tac)).symm
  -- el `expect` de `with_length`: lo que queda entra en la capacidad.
  · rename_i hne n hnge hn rem hrem hle r hwl
    obtain ⟨b, hb, -⟩ := hwl (by scalar_tac)
    exact ⟨b, hb⟩
  -- lo que deja el loop es `drop delta`.
  · rename_i hne n hnge hn rem hrem hle r hwl nb hnb res hl hd
    refine desplazado_fin (by omega) ?_
    rw [hl]; exact hd
  -- las tres hipotesis del loop.
  all_goals try (
    rename_i hne n hnge hn rem hrem hle r hwl nb hnb
    have hbits : nb.bits.val = List.replicate rem.val false := by
      obtain ⟨b, hb, hbb⟩ := hwl (by scalar_tac)
      rw [hnb] at hb
      injection hb with hb
      subst hb
      exact hbb
    first
      | (rw [hbits]; simp; done)
      | omega
      | (rw [hbits]; exact desplazado_ini _ _ _))
  -- `largo - delta` no desborda por abajo.
  all_goals (exfalso; scalar_tac)
end

section
attribute [local spec] relative_index_total bl_len_total bl_with_length_total
  expect_total extend_loop_total

/-- `extend_to_slot` no entra en panico ni se cuelga, si el slot pedido esta
    a lo sumo 262144 por encima del finalizado. Y devuelve lo que dice el
    teorema 1. -/
theorem extend_to_slot_total_spec (slots : ssz.SszBitlist 262144#usize)
    (f t : Std.U64) (hcap : t.val - f.val ≤ 262144) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.extend_to_slot slots f t
    ⦃ ⇓ r => ⌜ r.bits.val = slots.bits.val ++
        List.replicate (r.bits.val.length - slots.bits.val.length) false ⌝ ⦄ := by
  unfold justified_slots_ops.extend_to_slot
  hax_mvcgen
  -- el slot ya esta finalizado: no se toca nada.
  · simp
  -- la lista ya alcanza: no se toca nada.
  · simp
  -- el `expect` de `with_length`: la capacidad pedida entra.
  · rename_i o idx ho hri rc hrc n hnge hn r hwl
    have h1 := hri.2 idx rfl
    obtain ⟨b, hb, -⟩ := hwl (by scalar_tac)
    exact ⟨b, hb⟩
  -- lo que deja el loop es la lista vieja mas ceros.
  · rename_i o idx ho hri rc hrc n hnge hn r hwl ext hext res hcop
    exact copiado_fin hcop
  -- las dos hipotesis del loop.
  · rename_i o idx ho hri rc hrc n hnge hn r hwl ext hext
    exact hn
  · rename_i o idx ho hri rc hrc n hnge hn r hwl ext hext
    have h1 := hri.2 idx rfl
    have hbits : ext.bits.val = List.replicate rc.val false := by
      obtain ⟨b, hb, hbb⟩ := hwl (by scalar_tac)
      rw [hext] at hb
      injection hb with hb
      subst hb
      exact hbb
    rw [hbits]
    exact copiado_ini _ _ (by scalar_tac)
  -- `required_idx + 1` no desborda.
  · rename_i o idx ho hri hov
    have h1 := hri.2 idx rfl
    exfalso
    scalar_tac
end

/-- `is_slot_justified` nunca entra en panico. -/
theorem is_slot_justified_total (slots : ssz.SszBitlist 262144#usize)
    (f s : Std.U64) :
    ∃ r, justified_slots_ops.is_slot_justified slots f s = ok r := by
  obtain ⟨o, ho, -, -⟩ := relative_index_eq s f
  unfold justified_slots_ops.is_slot_justified
  rw [ho]
  cases o with
  | none => exact ⟨_, rfl⟩
  | some idx =>
    obtain ⟨n, hn, -⟩ := len_eq slots
    cases hg : slots.bits.val[idx.val]? <;>
      simp [get_eq, hn, hg, core.option.Option.ok_or]

/-- Si `is_slot_justified` responde (`Ok`), `set_justified` no entra en
    panico. -/
theorem set_justified_total (slots : ssz.SszBitlist 262144#usize)
    (f t : Std.U64) (b : Bool)
    (h : justified_slots_ops.is_slot_justified slots f t =
           ok (core.result.Result.Ok b)) :
    ∃ slots', justified_slots_ops.set_justified slots f t = ok slots' := by
  obtain ⟨o, ho, -, -⟩ := relative_index_eq t f
  cases o with
  | none =>
    unfold justified_slots_ops.set_justified
    rw [ho]
    exact ⟨slots, rfl⟩
  | some idx =>
    have hbit := is_slot_justified_lee slots f t idx b ho h
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hbit
    obtain ⟨⟨r1, s1⟩, hset, -, hok⟩ := set_eq slots idx true
    have hr1 : r1 = core.result.Result.Ok () := hok.mpr hlt
    subst hr1
    unfold justified_slots_ops.set_justified
    rw [ho]
    simp [hset, core.result.Result.expect]

/-- Y si `is_slot_justified` rechaza (`Err`: el slot esta fuera de la
    ventana), `set_justified` ENTRA en panico. Los dos lemas juntos dicen
    exactamente cuando se dispara el `expect("index out of bounds")`. -/
theorem set_justified_panico (slots : ssz.SszBitlist 262144#usize)
    (f t : Std.U64) (e : stf.Error)
    (h : justified_slots_ops.is_slot_justified slots f t =
           ok (core.result.Result.Err e)) :
    justified_slots_ops.set_justified slots f t = fail Error.panic := by
  obtain ⟨o, ho, -, -⟩ := relative_index_eq t f
  cases o with
  | none =>
    unfold justified_slots_ops.is_slot_justified at h
    rw [ho] at h
    simp at h
  | some idx =>
    obtain ⟨n, hn, -⟩ := len_eq slots
    have hnone : ¬ idx.val < slots.bits.val.length := by
      intro hlt
      unfold justified_slots_ops.is_slot_justified at h
      rw [ho] at h
      simp [get_eq, hn, List.getElem?_eq_getElem hlt, core.option.Option.ok_or] at h
    obtain ⟨⟨r1, s1⟩, hset, -, hok⟩ := set_eq slots idx true
    have hr1 : r1 = core.result.Result.Err () := by
      cases r1 with
      | Ok u => exact absurd (hok.mp rfl) hnone
      | Err u => rfl
    subst hr1
    unfold justified_slots_ops.set_justified
    rw [ho]
    simp [hset, core.result.Result.expect, core.panicking.internal.panic]

/- ====================================================================
   Los enunciados.
   ==================================================================== -/

/-- `shift_window` DEVUELVE, y devuelve la lista sin sus primeros `delta`
    bits. Sin condicional de panico. -/
theorem shift_window_devuelve (slots : ssz.SszBitlist 262144#usize)
    (delta : Std.Usize) (hcap : slots.bits.val.length ≤ 262144) :
    ∃ slots', justified_slots_ops.shift_window slots delta = ok slots' ∧
      slots'.bits.val = slots.bits.val.drop delta.val :=
  of_triple_total (shift_window_total_spec slots delta hcap)

/-- `extend_to_slot` DEVUELVE, y devuelve la lista vieja mas ceros al final.
    Sin condicional de panico. -/
theorem extend_to_slot_devuelve (slots : ssz.SszBitlist 262144#usize)
    (f t : Std.U64) (hcap : t.val - f.val ≤ 262144) :
    ∃ slots', justified_slots_ops.extend_to_slot slots f t = ok slots' ∧
      slots'.bits.val = slots.bits.val ++
        List.replicate (slots'.bits.val.length - slots.bits.val.length) false :=
  of_triple_total (extend_to_slot_total_spec slots f t hcap)

/-- El compuesto (teorema 4), ahora sin condicional: `shift_window` devuelve
    y la respuesta se conserva. -/
theorem finalizar_conserva_justificados_total
    (slots : ssz.SszBitlist 262144#usize) (f f' s : Std.U64)
    (delta : Std.Usize) (b : Bool)
    (hff : f.val ≤ f'.val) (hfs : f'.val < s.val)
    (hdelta : delta.val = f'.val - f.val)
    (hfit : s.val - f.val - 1 < 2 ^ UScalarTy.Usize.numBits)
    (hcap : slots.bits.val.length ≤ 262144)
    (hj : justified_slots_ops.is_slot_justified slots f s =
            ok (core.result.Result.Ok b)) :
    ∃ slots', justified_slots_ops.shift_window slots delta = ok slots' ∧
      justified_slots_ops.is_slot_justified slots' f' s =
        ok (core.result.Result.Ok b) := by
  obtain ⟨slots', hsh, -⟩ := shift_window_devuelve slots delta hcap
  exact ⟨slots', hsh,
    finalizar_conserva_justificados slots slots' f f' s delta b hff hfs hdelta hfit hj hsh⟩

/- ====================================================================
   En el punto de uso: el `expect` de `set_justified` no se dispara en
   `process_attestations`.
   ==================================================================== -/

theorem is_slot_justified_eco_spec (b : ssz.SszBitlist 262144#usize) (x y : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.is_slot_justified b x y
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ justified_slots_ops.is_slot_justified b x y = ok r ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv => hv)

/-- `branch` sobre un `Result`: si sigue (`Continue v`), el resultado era
    `Ok v`. -/
theorem branch_modelo_spec {T E : Type} (r : core.result.Result T E) :
    ⦃ ⌜ True ⌝ ⦄ core.result.Result.Insts.CoreOpsTry_traitTry.branch r
    ⦃ PostCond.mayThrow (fun cf => ⌜ ∀ v,
        cf = core.ops.control_flow.ControlFlow.Continue v →
        r = core.result.Result.Ok v ⌝) ⦄ :=
  triple_mayThrow_of (fun cf hcf v hv => by
    subst hv
    cases r with
    | Ok x =>
      simp [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch] at hcf
      rw [hcf]
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch] at hcf)

section
attribute [local spec] ST7.ssz_deref_spec is_slot_justified_eco_spec
  ST7.justifiable_spec ST7.from_residual_err_spec ST7.matches_chain_spec
  branch_modelo_spec

/-- Un voto que `is_valid_vote` acepta tiene su target DENTRO de la ventana:
    `is_slot_justified` respondio `Ok(false)` sobre el. -/
theorem is_valid_vote_ventana_spec (st : tipos.State) (d : tipos.AttestationData) :
    ⦃ ⌜ True ⌝ ⦄ stf.is_valid_vote st d
    ⦃ PostCond.mayThrow (fun r => ⌜ r = core.result.Result.Ok true →
        justified_slots_ops.is_slot_justified st.justified_slots
          st.latest_finalized.slot d.target.slot =
          ok (core.result.Result.Ok false) ⌝) ⦄ := by
  unfold stf.is_valid_vote
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | grind
end

/-- Despues de un voto valido, `set_justified` sobre su target no entra en
    panico. Es la llamada que hace el loop de `process_attestations`, con el
    mismo estado entre las dos. -/
theorem set_justified_tras_voto_valido (st : tipos.State) (d : tipos.AttestationData)
    (h : stf.is_valid_vote st d = ok (core.result.Result.Ok true)) :
    ∃ slots', justified_slots_ops.set_justified st.justified_slots
        st.latest_finalized.slot d.target.slot = ok slots' :=
  set_justified_total _ _ _ false
    (of_triple_mayThrow (is_valid_vote_ventana_spec st d) h rfl)

end NP

/- ===========================================================================
   Teorema 11: que cubre la ventana despues del header (17 nov 2026)

   El comentario de `is_valid_vote` en el codigo de ethlambda dice:

       After `process_block_header` the window covers up to
       `block.slot - 1`, so this is exactly a vote whose source or target
       slot is at or beyond the importing block's own slot.

   Es una afirmacion sobre el codigo que nadie habia verificado. Aca esta,
   en dos mitades:

     - `tras_header_cubre`: si `process_block_header` acepta, sobre todo
       slot anterior al del bloque `is_slot_justified` responde `Ok`. Vale
       para cualquier estado de entrada.
     - `tras_header_rechaza`: y del slot del bloque en adelante responde
       `Err` (es el `JustifiedSlotOutOfRange`). Esta es la mitad del
       "exactly", y NO vale para cualquier estado: pide que la ventana de
       entrada no llegara ya mas alla del slot anterior al bloque. Con una
       ventana mas larga de lo debido, un voto con slot posterior al bloque
       no se rechazaria.

   Lo que hizo falta: el largo EXACTO que deja `extend_to_slot` (el maximo
   entre el que tenia y el pedido), que no estaba en el teorema 9, y que
   ventana deja `process_block_header`: la de entrada pasada por
   `extend_to_slot` hasta `block.slot - 1`, con el mismo slot finalizado.

   Las dos piden que las distancias entren en un `usize`, por el mismo
   `as usize` del teorema 9.

   Lo que NO esta: que la hipotesis de `tras_header_rechaza` se conserve a
   lo largo de la transicion. Es el invariante "la ventana llega exactamente
   hasta el ultimo slot materializado", y hay que seguirlo a traves de
   `process_attestations`, donde `shift_window` la acorta.
   =========================================================================== -/

namespace VC
open mini_stf
open Std.Tactic
open ST3 JS NP

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

section
attribute [local spec] bl_get_spec bl_set_spec opt_eq_true_spec
  ST7.expect_modelo_spec

/-- El loop de copia de `extend_to_slot` no cambia el largo de la lista
    nueva. -/
theorem extend_loop_largo_spec (slots ext0 : ssz.SszBitlist 262144#usize)
    (n : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.extend_to_slot_loop { start := 0#usize, «end» := n } slots ext0
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.bits.val.length = ext0.bits.val.length ⌝) ⦄ := by
  unfold justified_slots_ops.extend_to_slot_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × (ssz.SszBitlist 262144#usize) =>
       x.2.bits.val.length = ext0.bits.val.length)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · rfl
  · intro x hinv
    obtain ⟨iter, ext⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    simp only at hinv
    unfold justified_slots_ops.extend_to_slot_loop.body
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | trivial
      | assumption
      | simp [PostCond.div, PostCond.mayThrow]
      | (simp_all [PostCond.okAssertion]; done)
end

theorem relative_index_eco_spec (t f : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.relative_index t f
    ⦃ PostCond.mayThrow (fun o =>
        ⌜ justified_slots_ops.relative_index t f = ok o ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv => hv)

section
attribute [local spec] relative_index_eco_spec bl_len_spec bl_with_length_spec
  ST7.expect_modelo_spec extend_loop_largo_spec

/-- El largo exacto que deja `extend_to_slot`. -/
theorem extend_to_slot_largo_spec (slots : ssz.SszBitlist 262144#usize)
    (f t : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄
    justified_slots_ops.extend_to_slot slots f t
    ⦃ PostCond.mayThrow (fun r => ⌜
        (justified_slots_ops.relative_index t f = ok none → r = slots) ∧
        (∀ idx : Std.Usize,
           justified_slots_ops.relative_index t f = ok (some idx) →
           r.bits.val.length = max slots.bits.val.length (idx.val + 1)) ⌝) ⦄ := by
  unfold justified_slots_ops.extend_to_slot
  hax_mvcgen
  -- el slot ya esta finalizado: no se toca nada.
  · rename_i o ho hri
    exact ⟨fun _ => trivial, fun idx h => by rw [hri] at h; simp at h⟩
  -- la lista ya alcanza: no se toca nada, y ya era mas larga.
  · rename_i o idx ho hri rc hrc n hge hn
    refine ⟨fun _ => trivial, fun idx' h => ?_⟩
    rw [hri] at h
    simp at h
    subst h
    have hle : idx.val + 1 ≤ slots.bits.val.length := by scalar_tac
    omega
  -- se arma la lista nueva: queda del largo pedido.
  · rename_i o idx ho hri rc hrc n hnge hn r hwl ext hext res hlen
    refine ⟨fun h => by rw [hri] at h; simp at h, fun idx' h => ?_⟩
    rw [hri] at h
    simp at h
    subst h
    have hbits := hwl ext hext
    have hext_len : ext.bits.val.length = rc.val := by rw [hbits]; simp
    have hlt : slots.bits.val.length < idx.val + 1 := by scalar_tac
    rw [hlen, hext_len]
    scalar_tac
end

theorem extend_eco_spec (b : ssz.SszBitlist 262144#usize) (x y : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.extend_to_slot b x y
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ justified_slots_ops.extend_to_slot b x y = ok r ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv => hv)

section
attribute [local spec] ssz_len_spec ST3H.current_proposer_spec ST3H.ok_or_spec
  ST3H.branch_spec ST3H.header_hash_spec ST3H.ne_default_spec ST3H.take_spec
  ST3H.into_inner_spec ST3H.push_spec ST3H.header_loop_spec ST3H.try_from_spec
  ST3H.expect_spec ST3H.body_hash_spec ST7.from_residual_err_spec
  extend_eco_spec

/-- Que ventana deja `process_block_header` cuando acepta: la que tenia,
    pasada por `extend_to_slot` hasta `block.slot - 1`, con el mismo slot
    finalizado. -/
theorem header_ventana_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block_header state block
    ⦃ PostCond.mayThrow (fun r => ⌜ r.1 = core.result.Result.Ok () →
        ∃ ultimo : Std.U64, ultimo.val + 1 = block.slot.val ∧
          justified_slots_ops.extend_to_slot state.justified_slots
            state.latest_finalized.slot ultimo = ok r.2.justified_slots ∧
          r.2.latest_finalized.slot = state.latest_finalized.slot ⌝) ⦄ := by
  unfold stf.process_block_header
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
  -- Las dos ramas que llegan al final (con y sin anclaje del genesis):
  -- el testigo es `block.slot - 1`.
  all_goals (
    refine ⟨_, ?_, by assumption⟩
    scalar_tac)
end

/-- Indice dentro de la lista: `is_slot_justified` responde. -/
theorem is_slot_justified_dentro (slots : ssz.SszBitlist 262144#usize)
    (f s : Std.U64) (idx : Std.Usize)
    (ho : justified_slots_ops.relative_index s f = ok (some idx))
    (hlt : idx.val < slots.bits.val.length) :
    ∃ b, justified_slots_ops.is_slot_justified slots f s =
      ok (core.result.Result.Ok b) :=
  ⟨_, is_slot_justified_de_bit slots f s idx _ ho (List.getElem?_eq_getElem hlt)⟩

/-- Indice fuera de la lista: `is_slot_justified` rechaza. -/
theorem is_slot_justified_fuera (slots : ssz.SszBitlist 262144#usize)
    (f s : Std.U64) (idx : Std.Usize)
    (ho : justified_slots_ops.relative_index s f = ok (some idx))
    (hge : slots.bits.val.length ≤ idx.val) :
    ∃ e, justified_slots_ops.is_slot_justified slots f s =
      ok (core.result.Result.Err e) := by
  unfold justified_slots_ops.is_slot_justified
  rw [ho]
  obtain ⟨n, hn, -⟩ := len_eq slots
  simp [get_eq, hn, List.getElem?_eq_none hge, core.option.Option.ok_or]

/-- Despues de `process_block_header`, la ventana cubre todos los slots
    anteriores al del bloque: `is_slot_justified` responde `Ok` sobre cada
    uno. Es la primera mitad del comentario de `is_valid_vote`. -/
theorem tras_header_cubre (state state' : tipos.State) (block : tipos.Block)
    (s : Std.U64)
    (h : stf.process_block_header state block =
           ok (core.result.Result.Ok (), state'))
    (hs : s.val < block.slot.val)
    (hfit : block.slot.val - state.latest_finalized.slot.val <
              2 ^ UScalarTy.Usize.numBits) :
    ∃ b, justified_slots_ops.is_slot_justified state'.justified_slots
        state'.latest_finalized.slot s = ok (core.result.Result.Ok b) := by
  obtain ⟨ult, hult, hext, hfin⟩ :=
    of_triple_mayThrow (header_ventana_spec state block) h rfl
  rw [hfin]
  obtain ⟨-, hsome⟩ := of_triple_mayThrow
    (extend_to_slot_largo_spec state.justified_slots state.latest_finalized.slot ult) hext
  obtain ⟨os, hos, hosnone, hosval⟩ :=
    relative_index_eq s state.latest_finalized.slot
  cases os with
  | none =>
    refine ⟨true, ?_⟩
    unfold justified_slots_ops.is_slot_justified
    rw [hos]
    rfl
  | some idx =>
    have hsf : state.latest_finalized.slot.val < s.val := by
      by_contra hle
      have := hosnone.mpr (by omega)
      simp at this
    have hidx : idx.val ≤ s.val - state.latest_finalized.slot.val - 1 := by
      rw [hosval idx rfl]; exact Nat.mod_le _ _
    obtain ⟨ou, hou, hounone, houval⟩ :=
      relative_index_eq ult state.latest_finalized.slot
    cases ou with
    | none => have := hounone.mp rfl; omega
    | some iu =>
      have hiu : iu.val = ult.val - state.latest_finalized.slot.val - 1 := by
        rw [houval iu rfl]; exact Nat.mod_eq_of_lt (by omega)
      have hlen := hsome iu hou
      have hge : iu.val + 1 ≤ state'.justified_slots.bits.val.length := by
        rw [hlen]; exact Nat.le_max_right _ _
      exact is_slot_justified_dentro _ _ _ idx hos (by omega)

/-- Y si la ventana de entrada no llegaba mas alla del slot anterior al
    bloque, del slot del bloque en adelante `is_slot_justified` rechaza. Es
    la segunda mitad: "exactamente". -/
theorem tras_header_rechaza (state state' : tipos.State) (block : tipos.Block)
    (s : Std.U64)
    (h : stf.process_block_header state block =
           ok (core.result.Result.Ok (), state'))
    (hlen : state.justified_slots.bits.val.length +
              state.latest_finalized.slot.val + 1 ≤ block.slot.val)
    (hs : block.slot.val ≤ s.val)
    (hfit : s.val - state.latest_finalized.slot.val - 1 <
              2 ^ UScalarTy.Usize.numBits) :
    ∃ e, justified_slots_ops.is_slot_justified state'.justified_slots
        state'.latest_finalized.slot s = ok (core.result.Result.Err e) := by
  obtain ⟨ult, hult, hext, hfin⟩ :=
    of_triple_mayThrow (header_ventana_spec state block) h rfl
  rw [hfin]
  obtain ⟨hnone, hsome⟩ := of_triple_mayThrow
    (extend_to_slot_largo_spec state.justified_slots state.latest_finalized.slot ult) hext
  obtain ⟨idx, hos, hidx⟩ :=
    relative_index_arriba s state.latest_finalized.slot (by omega) hfit
  obtain ⟨ou, hou, hounone, houval⟩ :=
    relative_index_eq ult state.latest_finalized.slot
  cases ou with
  | none =>
    have hule := hounone.mp rfl
    rw [hnone hou]
    exact is_slot_justified_fuera _ _ _ idx hos (by omega)
  | some iu =>
    have hfu : state.latest_finalized.slot.val < ult.val := by
      by_contra hle
      have := hounone.mpr (by omega)
      simp at this
    have hiu : iu.val = ult.val - state.latest_finalized.slot.val - 1 := by
      rw [houval iu rfl]; exact Nat.mod_eq_of_lt (by omega)
    have hle : state.justified_slots.bits.val.length ≤ iu.val + 1 := by omega
    have hl' : state'.justified_slots.bits.val.length = iu.val + 1 := by
      rw [hsome iu hou]; exact Nat.max_eq_right hle
    exact is_slot_justified_fuera _ _ _ idx hos (by omega)

end VC

/- ===========================================================================
   Teorema 12: donde termina la ventana, a lo largo de la transicion
   (17 nov 2026)

   El teorema 11 dejo una hipotesis suelta: que la ventana de entrada no
   llegara mas alla del slot anterior al bloque. Aca esta como invariante de
   la transicion entera.

     - `VentanaNoPasa st`: largo de la ventana + slot finalizado <= slot del
       ultimo header. Vale en el genesis (ventana vacia, finalizado en cero).
     - `VentanaJusta st`: largo + finalizado + 1 = slot del ultimo header. Es
       decir, la ventana cubre exactamente del finalizado + 1 al slot del
       header - 1.

   Lo demostrado:

     - `state_transition_conserva_ventana`: si `VentanaNoPasa` vale antes de
       un bloque, vale despues, lo acepte o lo rechace.
     - `state_transition_ventana_justa`: y si lo acepta, queda `VentanaJusta`.
     - `tras_header_rechaza_inv`: el "exactly" del comentario de
       `is_valid_vote`, con el invariante en lugar de la hipotesis suelta.

   Por que vale. `process_block_header` extiende la ventana hasta
   `block.slot - 1`, y con eso la deja justa. Despues, en el loop de
   attestations, `set_justified` no cambia el largo, y `try_finalize` mueve
   las dos cosas a la vez: la finalidad avanza `source.slot - finalizado` y
   `shift_window` acorta la ventana esa misma cantidad. La suma no cambia.
   Para que la cuenta cierre hace falta que el source este dentro de la
   ventana, y eso lo da `is_valid_vote`: solo acepta el voto si
   `is_slot_justified` respondio `Ok(true)` sobre el source.

   Todo el teorema lleva la hipotesis `h64`: que `usize` es de 64 bits. Es el
   mismo `as usize` de los teoremas 9 y 11, que aca aparece tres veces (el
   indice del source, el `delta` de `shift_window`, el indice del ultimo slot
   en el header). En 32 bits esos casts truncan y la cuenta no cierra.

   Lo que NO esta: que la ventana no pase de 262144 bits. De `VentanaNoPasa`
   sale que no pasa del slot del header; falta acotar ese slot, y eso depende
   del tope de `historical_block_hashes`.
   =========================================================================== -/

namespace VI
open mini_stf
open Std.Tactic
open ST3 JS NP VC

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

/-- En 64 bits, pasar un `u64` a `usize` no cambia el valor. -/
theorem cast_usize_64 (h64 : UScalarTy.Usize.numBits = 64) (x : Std.U64) :
    (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq, h64]
  exact Nat.mod_eq_of_lt (by scalar_tac)

theorem serialize_no_toca_ventana
    (state state' : tipos.State) (j : mapa.MapaVotos) (vc : Std.Usize)
    (h : stf.serialize_justifications state j vc = ok state') :
    state'.justified_slots = state.justified_slots := by
  unfold stf.serialize_justifications at h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  simp only [RustM.ok.injEq] at h
  subst h
  rfl

theorem process_slots_no_toca_ventana
    (state state' : tipos.State) (t : Std.U64)
    (res : core.result.Result Unit stf.Error)
    (h : stf.process_slots state t = ok (res, state')) :
    state'.justified_slots = state.justified_slots := by
  unfold stf.process_slots at h
  obtain ⟨_, _, h⟩ := bind_da_ok h
  split at h
  · simp only [RustM.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hst⟩ := h
    subst hst
    rfl
  · obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    obtain ⟨_, _, h⟩ := bind_da_ok h
    simp only [RustM.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hst⟩ := h
    subst hst
    rfl

theorem set_justified_largo_spec (slots : ssz.SszBitlist 262144#usize)
    (f t : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.set_justified slots f t
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ r.bits.val.length = slots.bits.val.length ⌝) ⦄ :=
  triple_mayThrow_of (fun r hr => by
    rcases set_justified_eq slots r f t hr with ⟨-, h⟩ | ⟨idx, -, -, hbits⟩
    · rw [h]
    · rw [hbits]; simp)

theorem shift_eco_spec (b : ssz.SszBitlist 262144#usize) (d : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.shift_window b d
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ justified_slots_ops.shift_window b d = ok r ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv => hv)

theorem trivial_spec {α : Type} (x : RustM α) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ :=
  triple_mayThrow_of (fun _ _ => trivial)

theorem hay_slot_spec (a b c : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ stf.hay_slot_justificable a b c
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ := trivial_spec _

theorem inc_fin_spec (s : Str) :
    ⦃ ⌜ True ⌝ ⦄ stubs.metrics.inc_finalizations s
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ := trivial_spec _

theorem vec_new_spec (T : Type) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.new T
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ := trivial_spec _

theorem largo_spec (m : mapa.MapaVotos) :
    ⦃ ⌜ True ⌝ ⦄ mapa.MapaVotos.largo m
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ := trivial_spec _

theorem tf_loop_spec (it : core.ops.range.Range Std.Usize) (s : Std.U64)
    (j : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global)
    (c : alloc.vec.Vec Bool) :
    ⦃ ⌜ True ⌝ ⦄ stf.try_finalize_loop it s j rts c
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ := trivial_spec _

theorem vec_deref_spec {T : Type} (v : alloc.vec.Vec T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref v
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ := trivial_spec _

theorem filtrado_spec (m : mapa.MapaVotos) (s : Slice Bool) :
    ⦃ ⌜ True ⌝ ⦄ mapa.MapaVotos.filtrado m s
    ⦃ PostCond.mayThrow (fun _ => ⌜ True ⌝) ⦄ := trivial_spec _

section
attribute [local spec] hay_slot_spec inc_fin_spec vec_new_spec largo_spec
  tf_loop_spec vec_deref_spec filtrado_spec shift_eco_spec

/-- Que le hace `try_finalize` a la ventana: o no toca nada, o pone la
    finalidad en el `source` y corre la ventana esa distancia. -/
theorem try_finalize_ventana_spec (state : tipos.State)
    (source target : tipos.Checkpoint) (j : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    stf.try_finalize state source target j rts
    ⦃ PostCond.mayThrow (fun r => ⌜
        (r.1.justified_slots = state.justified_slots ∧
         r.1.latest_finalized = state.latest_finalized) ∨
        (r.1.latest_finalized = source ∧
         state.latest_finalized.slot.val < source.slot.val ∧
         ∃ i1 : Std.U64, i1.val = source.slot.val - state.latest_finalized.slot.val ∧
           justified_slots_ops.shift_window state.justified_slots
             (UScalar.cast .Usize i1) = ok r.1.justified_slots) ⌝) ⦄ := by
  unfold stf.try_finalize
  hax_mvcgen
  -- el source no avanza: no se toca nada.
  · exact Or.inl trivial
  -- hay un slot justificable en el medio: tampoco.
  · exact Or.inl trivial
  -- se finaliza: la ventana se corre `source.slot - finalizado`.
  · subst_vars
    refine Or.inr ⟨trivial, ?_, _, ?_, by assumption⟩
    · scalar_tac
    · assumption
end

section
attribute [local spec] ST7.ssz_deref_spec is_slot_justified_eco_spec
  ST7.justifiable_spec ST7.from_residual_err_spec ST7.matches_chain_spec
  branch_modelo_spec

/-- Un voto que `is_valid_vote` acepta tiene su SOURCE justificado segun la
    ventana: `is_slot_justified` respondio `Ok(true)` sobre el. -/
theorem is_valid_vote_fuente_spec (st : tipos.State) (d : tipos.AttestationData) :
    ⦃ ⌜ True ⌝ ⦄ stf.is_valid_vote st d
    ⦃ PostCond.mayThrow (fun r => ⌜ r = core.result.Result.Ok true →
        justified_slots_ops.is_slot_justified st.justified_slots
          st.latest_finalized.slot d.source.slot =
          ok (core.result.Result.Ok true) ⌝) ⦄ := by
  unfold stf.is_valid_vote
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    | grind
end

/-- La cuenta. Si la ventana `js` (del mismo largo que `js0`) llegaba justo
    hasta `L`, el source estaba justificado en `js0`, y la ventana se corre
    `src - f`, la ventana nueva sigue llegando justo hasta `L` medida desde
    `src`. -/
theorem ventana_tras_finalizar (js0 js js' : ssz.SszBitlist 262144#usize)
    (f src i1 : Std.U64) (L : Nat)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hlen : js.bits.val.length = js0.bits.val.length)
    (hq : js0.bits.val.length + f.val + 1 = L)
    (hlt : f.val < src.val)
    (hsrc : justified_slots_ops.is_slot_justified js0 f src =
              ok (core.result.Result.Ok true))
    (hi1 : i1.val = src.val - f.val)
    (hsh : justified_slots_ops.shift_window js (UScalar.cast .Usize i1) = ok js') :
    js'.bits.val.length + src.val + 1 = L := by
  have hs : src.val < 2 ^ 64 := by scalar_tac
  obtain ⟨idx, ho, hidx⟩ := relative_index_arriba src f hlt (by rw [h64]; omega)
  have hbit := is_slot_justified_lee js0 f src idx true ho hsrc
  obtain ⟨hin, -⟩ := List.getElem?_eq_some_iff.mp hbit
  have hdelta : (UScalar.cast .Usize i1).val = src.val - f.val := by
    rw [cast_usize_64 h64, hi1]
  rw [shift_window_eq js js' _ hsh, List.length_drop, hdelta, hlen]
  omega

/-- Cierre de las dos ramas de la justificacion: `set_justified` no cambia
    el largo, y `try_finalize` o no toca nada o corre la ventana justo lo que
    avanza la finalidad. -/
theorem cierre_ventana (st r : tipos.State) (sb : ssz.SszBitlist 262144#usize)
    (src : tipos.Checkpoint) (v : Bool)
    (res : core.result.Result Bool stf.Error) (L : Nat)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hinv : st.justified_slots.bits.val.length +
              st.latest_finalized.slot.val + 1 = L)
    (hvoto : res = core.result.Result.Ok true →
       justified_slots_ops.is_slot_justified st.justified_slots
         st.latest_finalized.slot src.slot = ok (core.result.Result.Ok true))
    (hres : res = core.result.Result.Ok v) (hv : v = true)
    (hset : sb.bits.val.length = st.justified_slots.bits.val.length)
    (hfin : (r.justified_slots = sb ∧
             r.latest_finalized = st.latest_finalized) ∨
            (r.latest_finalized = src ∧
             st.latest_finalized.slot.val < src.slot.val ∧
             ∃ i1 : Std.U64, i1.val = src.slot.val - st.latest_finalized.slot.val ∧
               justified_slots_ops.shift_window sb (UScalar.cast .Usize i1) =
                 ok r.justified_slots)) :
    r.justified_slots.bits.val.length + r.latest_finalized.slot.val + 1 = L := by
  rcases hfin with ⟨e1, e2⟩ | ⟨e1, hlt, i1, hi1, hsh⟩
  · rw [e1, e2, hset]; exact hinv
  · rw [e1]
    exact ventana_tras_finalizar st.justified_slots sb r.justified_slots
      st.latest_finalized.slot src.slot i1 L h64 hset hinv hlt
      (hvoto (by rw [hres, hv])) hi1 hsh

section
attribute [local spec] is_none_spec dato_en_spec bits_en_uno_en_spec
  primer_bit_spec votos_vacios_spec poner_si_falta_spec
  marcar_votos_spec cuenta_votos_spec sin_spec div_ceil_spec
  set_justified_largo_spec is_valid_vote_fuente_spec try_finalize_ventana_spec

/-- El loop de attestations conserva "la ventana llega justo hasta `L`". -/
theorem process_attestations_loop_ventana
    (s0 : tipos.State)
    (attestations : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (validator_count n : Std.Usize)
    (j0 : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global)
    (L : Nat) (h64 : UScalarTy.Usize.numBits = 64)
    (h0 : s0.justified_slots.bits.val.length +
            s0.latest_finalized.slot.val + 1 = L) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations_loop { start := 0#usize, «end» := n } s0
      attestations validator_count 0#u64 j0 rts core.option.Option.None
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.1.justified_slots.bits.val.length +
                      r.1.latest_finalized.slot.val + 1 = L ⌝) ⦄ := by
  unfold stf.process_attestations_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × Acc =>
              x.2.1.justified_slots.bits.val.length +
                x.2.1.latest_finalized.slot.val + 1 = L)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · exact h0
  · intro x hinv
    obtain ⟨iter, st, ap, jj, fl⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    simp only at hinv
    unfold stf.process_attestations_loop.body
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | assumption
      | trivial
      | simp [PostCond.div, PostCond.mayThrow]
      | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
    all_goals first
      | exact cierre_ventana _ _ _ _ _ _ _ h64 hinv (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption)
end

/-- Lo mismo sin `L`: el loop conserva la suma "largo de la ventana + slot
    finalizado". Es la forma que `mvcgen` puede componer. -/
theorem process_attestations_loop_ventana_spec
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
        (fun r => ⌜ UScalarTy.Usize.numBits = 64 →
            r.1.justified_slots.bits.val.length + r.1.latest_finalized.slot.val =
            s0.justified_slots.bits.val.length + s0.latest_finalized.slot.val ⌝) ⦄ :=
  triple_mayThrow_of (fun _ hv h64 => by
    have := of_triple_mayThrow
      (process_attestations_loop_ventana s0 attestations validator_count n j0 rts
        _ h64 rfl) hv
    omega)

theorem serialize_ventana_spec (st : tipos.State) (j : mapa.MapaVotos)
    (vc : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.serialize_justifications st j vc
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.justified_slots = st.justified_slots ∧
                    r.latest_finalized = st.latest_finalized ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv =>
    ⟨serialize_no_toca_ventana st v j vc hv,
     serialize_no_toca_finalized st v j vc hv⟩)

section
attribute [local spec] timer_spec inc_procesadas_spec contar_datos_spec
  hay_raiz_cero_spec construir_mapa_spec construir_rts_spec ssz_len_spec
  bitlist_len_spec serialize_ventana_spec process_attestations_loop_ventana_spec

/-- `process_attestations` conserva "largo de la ventana + slot finalizado". -/
theorem process_attestations_ventana (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (h64 : UScalarTy.Usize.numBits = 64) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations state atts
    ⦃ PostCond.mayThrow
        (fun r => ⌜ r.2.justified_slots.bits.val.length +
                      r.2.latest_finalized.slot.val =
                    state.justified_slots.bits.val.length +
                      state.latest_finalized.slot.val ⌝) ⦄ := by
  unfold stf.process_attestations
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | simp [PostCond.div, PostCond.mayThrow]
    | exact (by assumption : _ = 64 → _) h64
    | (have a := (by assumption : _ = 64 → _) h64
       obtain ⟨b1, b2⟩ := (by assumption : _ = _ ∧ _ = _)
       rw [b1, b2]; exact a)
end

section
attribute [local spec] ssz_len_spec ST3H.current_proposer_spec ST3H.ok_or_spec
  ST3H.branch_spec ST3H.header_hash_spec ST3H.ne_default_spec ST3H.take_spec
  ST3H.into_inner_spec ST3H.push_spec ST3H.header_loop_spec ST3H.try_from_spec
  ST3H.expect_spec ST3H.body_hash_spec ST7.from_residual_err_spec
  extend_eco_spec

/-- Todo lo que `process_block_header` le hace a la ventana, al slot
    finalizado y al slot del header, acepte o rechace. -/
theorem header_todo_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block_header state block
    ⦃ PostCond.mayThrow (fun r => ⌜
        (r.1 = core.result.Result.Ok () →
          ∃ ultimo : Std.U64, ultimo.val + 1 = block.slot.val ∧
            justified_slots_ops.extend_to_slot state.justified_slots
              state.latest_finalized.slot ultimo = ok r.2.justified_slots ∧
            r.2.latest_finalized.slot = state.latest_finalized.slot ∧
            r.2.latest_block_header.slot = block.slot ∧
            state.latest_block_header.slot.val < block.slot.val) ∧
        (r.1 ≠ core.result.Result.Ok () →
          r.2.justified_slots = state.justified_slots ∧
          r.2.latest_finalized.slot = state.latest_finalized.slot ∧
          r.2.latest_block_header.slot = state.latest_block_header.slot) ⌝) ⦄ := by
  unfold stf.process_block_header
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
  -- Las dos ramas que llegan al final, con y sin anclaje del genesis.
  all_goals (
    refine ⟨⟨_, ?_, by assumption, trivial, trivial, ?_⟩, fun h => absurd rfl h⟩
    · scalar_tac
    · scalar_tac)
end

/-- La ventana no pasa del ultimo slot materializado. Vale en el genesis. -/
def VentanaNoPasa (st : tipos.State) : Prop :=
  st.justified_slots.bits.val.length + st.latest_finalized.slot.val ≤
    st.latest_block_header.slot.val

/-- La ventana termina JUSTO en el ultimo slot materializado: cubre del
    finalizado + 1 al slot del header - 1. -/
def VentanaJusta (st : tipos.State) : Prop :=
  st.justified_slots.bits.val.length + st.latest_finalized.slot.val + 1 =
    st.latest_block_header.slot.val

theorem ventanaJusta_noPasa {st : tipos.State} (h : VentanaJusta st) :
    VentanaNoPasa st := by
  unfold VentanaJusta at h
  unfold VentanaNoPasa
  omega

/-- `process_block_header`: si la ventana no pasaba, sigue sin pasar; y si
    acepta el bloque, queda justa. -/
theorem header_ventana (state state' : tipos.State) (block : tipos.Block)
    (res : core.result.Result Unit stf.Error)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hp : VentanaNoPasa state)
    (h : stf.process_block_header state block = ok (res, state')) :
    VentanaNoPasa state' ∧
    (res = core.result.Result.Ok () → VentanaJusta state') := by
  unfold VentanaNoPasa at hp
  obtain ⟨hok, hfail⟩ := of_triple_mayThrow (header_todo_spec state block) h
  by_cases hres : res = core.result.Result.Ok ()
  · obtain ⟨ult, hult, hext, hf, hhs, hlt⟩ := hok hres
    obtain ⟨hnone, hsome⟩ := of_triple_mayThrow
      (extend_to_slot_largo_spec state.justified_slots
        state.latest_finalized.slot ult) hext
    have hjusta : VentanaJusta state' := by
      unfold VentanaJusta
      rw [hf, hhs]
      obtain ⟨ou, hou, hounone, houval⟩ :=
        relative_index_eq ult state.latest_finalized.slot
      cases ou with
      | none =>
        have hule := hounone.mp rfl
        rw [hnone hou]
        omega
      | some iu =>
        have hfu : state.latest_finalized.slot.val < ult.val := by
          by_contra hle
          have := hounone.mpr (by omega)
          simp at this
        have hub : ult.val < 2 ^ 64 := by scalar_tac
        have hiu : iu.val = ult.val - state.latest_finalized.slot.val - 1 := by
          rw [houval iu rfl, h64]; exact Nat.mod_eq_of_lt (by omega)
        have hle : state.justified_slots.bits.val.length ≤ iu.val + 1 := by omega
        have hl' : state'.justified_slots.bits.val.length = iu.val + 1 := by
          rw [hsome iu hou]; exact Nat.max_eq_right hle
        omega
    exact ⟨ventanaJusta_noPasa hjusta, fun _ => hjusta⟩
  · obtain ⟨e1, e2, e3⟩ := hfail hres
    refine ⟨?_, fun h => absurd h hres⟩
    unfold VentanaNoPasa
    rw [e1, e2, e3]
    exact hp

/-- `process_attestations` conserva "la ventana es justa". -/
theorem atts_ventana (state state' : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (res : core.result.Result Unit stf.Error)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hj : VentanaJusta state)
    (h : stf.process_attestations state atts = ok (res, state')) :
    VentanaJusta state' := by
  unfold VentanaJusta at hj ⊢
  have hs := of_triple_mayThrow (process_attestations_ventana state atts h64) h
  have hh := of_triple_mayThrow (ST2.process_attestations_header_spec state atts) h
  simp only at hs hh
  rw [hh]
  omega

/-- `process_slots` no toca nada de lo que mira el invariante. -/
theorem slots_ventana (state state' : tipos.State) (t : Std.U64)
    (res : core.result.Result Unit stf.Error)
    (hp : VentanaNoPasa state)
    (h : stf.process_slots state t = ok (res, state')) :
    VentanaNoPasa state' := by
  unfold VentanaNoPasa at hp ⊢
  obtain ⟨-, e2, -, e4⟩ := ST7.process_slots_no_toca state state' t res h
  rw [process_slots_no_toca_ventana state state' t res h, e2, e4]
  exact hp

theorem header_inv_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_block_header state block
    ⦃ PostCond.mayThrow (fun r => ⌜ UScalarTy.Usize.numBits = 64 →
        VentanaNoPasa state →
        (VentanaNoPasa r.2 ∧
         (r.1 = core.result.Result.Ok () → VentanaJusta r.2)) ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv h64 hp => by
    obtain ⟨res, st'⟩ := v
    exact header_ventana state st' block res h64 hp hv)

theorem atts_inv_spec (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_attestations state atts
    ⦃ PostCond.mayThrow (fun r => ⌜ UScalarTy.Usize.numBits = 64 →
        VentanaJusta state → VentanaJusta r.2 ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv h64 hj => by
    obtain ⟨res, st'⟩ := v
    exact atts_ventana state st' atts res h64 hj hv)

theorem slots_inv_spec (state : tipos.State) (t : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_slots state t
    ⦃ PostCond.mayThrow (fun r => ⌜ VentanaNoPasa state → VentanaNoPasa r.2 ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv hp => by
    obtain ⟨res, st'⟩ := v
    exact slots_ventana state st' t res hp hv)

section
attribute [local spec] branch_modelo_spec ST7.from_residual_err_spec
  ST3T.time_block_spec header_inv_spec atts_inv_spec

theorem process_block_inv_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_block state block
    ⦃ PostCond.mayThrow (fun r => ⌜ UScalarTy.Usize.numBits = 64 →
        VentanaNoPasa state →
        (VentanaNoPasa r.2 ∧
         (r.1 = core.result.Result.Ok () → VentanaJusta r.2)) ⌝) ⦄ := by
  unfold stf.process_block
  hax_mvcgen
  all_goals (
    have h64 := (by assumption : UScalarTy.Usize.numBits = 64)
    have hp := (by assumption : VentanaNoPasa state)
    obtain ⟨hnp, hju⟩ :=
      (by assumption : _ = 64 → VentanaNoPasa state → _) h64 hp
    first
      -- el header acepto: la ventana quedo justa y attestations la conserva.
      | (have hj1 := hju ((by assumption :
           ∀ v : Unit, _ = core.result.Result.Ok v) ())
         have hj2 := (by assumption :
           _ = 64 → VentanaJusta _ → VentanaJusta _) h64 hj1
         first
           | exact ⟨ventanaJusta_noPasa hj2, hj2⟩
           | exact ⟨ventanaJusta_noPasa hj2, fun _ => hj2⟩)
      -- el header rechazo: no pasa, y el resultado no es `Ok`.
      | exact ⟨hnp, fun h => absurd h ((by assumption :
          ∀ v : Unit, _ ≠ core.result.Result.Ok v) ())⟩)
end

section
attribute [local spec] branch_modelo_spec ST7.from_residual_err_spec
  ST3H.ne_default_spec ST3T.time_transition_spec ST3T.state_hash_spec
  slots_inv_spec process_block_inv_spec

theorem state_transition_inv_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄ stf.state_transition state block
    ⦃ PostCond.mayThrow (fun r => ⌜ UScalarTy.Usize.numBits = 64 →
        VentanaNoPasa state →
        (VentanaNoPasa r.2 ∧
         (r.1 = core.result.Result.Ok () → VentanaJusta r.2)) ⌝) ⦄ := by
  unfold stf.state_transition
  hax_mvcgen
  -- 1. `process_block` acepto y la raiz del estado no coincide: se devuelve
  --    `Err`, con la ventana como la dejo `process_block`.
  · have h64 := (by assumption : UScalarTy.Usize.numBits = 64)
    have hp := (by assumption : VentanaNoPasa state)
    have hs := (by assumption : VentanaNoPasa state → VentanaNoPasa _) hp
    have hb := (by assumption : _ = 64 → VentanaNoPasa _ → _ ∧ _) h64 hs
    refine ⟨hb.1, fun h => ?_⟩
    cases h
  -- 2. `process_block` acepto y la raiz coincide: se devuelve `Ok`.
  · have h64 := (by assumption : UScalarTy.Usize.numBits = 64)
    have hp := (by assumption : VentanaNoPasa state)
    have hs := (by assumption : VentanaNoPasa state → VentanaNoPasa _) hp
    have hb := (by assumption : _ = 64 → VentanaNoPasa _ → _ ∧ _) h64 hs
    exact ⟨hb.1, hb.2 ((by assumption :
      ∀ v : Unit, _ = core.result.Result.Ok v) ())⟩
  -- 3. `process_block` rechazo.
  · have h64 := (by assumption : UScalarTy.Usize.numBits = 64)
    have hp := (by assumption : VentanaNoPasa state)
    have hs := (by assumption : VentanaNoPasa state → VentanaNoPasa _) hp
    have hb := (by assumption : _ = 64 → VentanaNoPasa _ → _ ∧ _) h64 hs
    exact ⟨hb.1, fun h => absurd h ((by assumption :
      ∀ v : Unit, _ ≠ core.result.Result.Ok v) ())⟩
  -- 4. `process_slots` rechazo.
  · have hp := (by assumption : VentanaNoPasa state)
    have hs := (by assumption : VentanaNoPasa state → VentanaNoPasa _) hp
    exact ⟨hs, fun h => absurd h ((by assumption :
      ∀ v : Unit, _ ≠ core.result.Result.Ok v) ())⟩
end

/- ====================================================================
   Los enunciados.
   ==================================================================== -/

/-- El caso inicial: con la ventana vacia y el finalizado en cero, la
    ventana no pasa. Es como arranca el estado del genesis. -/
theorem ventanaNoPasa_inicial (st : tipos.State)
    (hv : st.justified_slots.bits.val = [])
    (hf : st.latest_finalized.slot.val = 0) : VentanaNoPasa st := by
  unfold VentanaNoPasa
  rw [hv, hf]
  simp

/-- La transicion de un bloque conserva "la ventana no pasa del ultimo slot
    materializado", acepte el bloque o lo rechace. -/
theorem state_transition_conserva_ventana
    (state state' : tipos.State) (block : tipos.Block)
    (res : core.result.Result Unit stf.Error)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hp : VentanaNoPasa state)
    (h : stf.state_transition state block = ok (res, state')) :
    VentanaNoPasa state' :=
  (of_triple_mayThrow (state_transition_inv_spec state block) h h64 hp).1

/-- Y si acepta el bloque, la ventana queda JUSTA: termina exactamente en el
    slot anterior al del bloque. -/
theorem state_transition_ventana_justa
    (state state' : tipos.State) (block : tipos.Block)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hp : VentanaNoPasa state)
    (h : stf.state_transition state block =
           ok (core.result.Result.Ok (), state')) :
    VentanaJusta state' :=
  (of_triple_mayThrow (state_transition_inv_spec state block) h h64 hp).2 rfl

/-- El "exactly" del comentario de `is_valid_vote`, ahora con el invariante
    en lugar de la hipotesis suelta sobre el largo: si la ventana no pasaba,
    despues del header se rechaza todo slot del bloque en adelante. -/
theorem tras_header_rechaza_inv (state state' : tipos.State) (block : tipos.Block)
    (s : Std.U64)
    (h : stf.process_block_header state block =
           ok (core.result.Result.Ok (), state'))
    (hp : VentanaNoPasa state)
    (hs : block.slot.val ≤ s.val)
    (hfit : s.val - state.latest_finalized.slot.val - 1 <
              2 ^ UScalarTy.Usize.numBits) :
    ∃ e, justified_slots_ops.is_slot_justified state'.justified_slots
        state'.latest_finalized.slot s = ok (core.result.Result.Err e) := by
  obtain ⟨-, -, -, -, -, hlt⟩ :=
    (of_triple_mayThrow (header_todo_spec state block) h).1 rfl
  unfold VentanaNoPasa at hp
  exact tras_header_rechaza state state' block s h (by omega) hs hfit

end VI

/- ===========================================================================
   Teorema 13: la ventana no pasa de su capacidad (17 nov 2026)

   El teorema 12 dejo la ventana acotada por el slot del ultimo header. Aca
   se acota ese slot, y con eso la ventana.

   El invariante nuevo, `HistorialAcotado`:

     - `historical_block_hashes` tiene exactamente un hash por slot: su largo
       es el slot del ultimo header;
     - y ese slot no pasa de 262144, que es `HISTORICAL_ROOTS_LIMIT`.

   Vale en el genesis (historial vacio, header en el slot cero) y se conserva
   por `state_transition`, acepte el bloque o lo rechace.

   Por que vale. `process_block_header` le agrega al historial la raiz del
   padre y un cero por cada slot vacio entre el padre y el bloque: en total
   `block.slot - parent.slot` elementos, asi que si antes tenia uno por slot,
   despues tambien. Y antes de agregarlos chequea que el total no pase de
   `HISTORICAL_ROOTS_LIMIT`; si pasa, rechaza con `SlotGapTooLarge`. Ese total
   ES el slot del bloque. El resto de la transicion no toca el historial.

   De ahi salen dos cosas:

     - `header_acepta_slot_acotado`: `process_block_header` no acepta ningun
       bloque con slot mayor que 262144. No es una diferencia con la
       especificacion: el tope es el mismo en leanSpec (`2**18`) y en el
       codigo de ethlambda. Es una consecuencia del tope que conviene tener
       escrita: con un hash por slot desde el genesis, la cadena de bloques no
       pasa del slot 262144.
     - `ventana_en_capacidad` y `shift_window_no_falla`: con los dos
       invariantes (este y el del teorema 12), la ventana no pasa de 262144
       bits, y `shift_window` sobre ella devuelve. Es la hipotesis de
       capacidad del teorema 10, descargada.

   Hizo falta: el largo EXACTO que deja el loop que rellena los slots vacios
   (hasta ahora solo estaba que agrega al final), y que `process_attestations`
   no toca el historial sin ninguna hipotesis (el teorema 7 lo tenia bajo
   `EnElHistorial`).

   Lleva la misma hipotesis `h64` del teorema 12: la cantidad de slots vacios
   pasa por un `as usize`.
   =========================================================================== -/

namespace HC
open mini_stf
open Std.Tactic
open ST3 JS NP VC VI

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

theorem limite_val : tipos.HISTORICAL_ROOTS_LIMIT.val = 262144 := by
  first
    | (simp [tipos.HISTORICAL_ROOTS_LIMIT]; done)
    | (unfold tipos.HISTORICAL_ROOTS_LIMIT; rfl)
    | scalar_tac

theorem ssz_len_eq {T : Type} {N : Std.Usize} (l : ssz.SszList T N) :
    ∃ n : Std.Usize, ssz.SszList.len l = ok n ∧ n.val = l.items.val.length := by
  unfold ssz.SszList.len
  simp [alloc.vec.Vec.len, rust_primitives.sequence.seq_len]

theorem ssz_len_modelo_spec {T : Type} {N : Std.Usize} (l : ssz.SszList T N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszList.len l
    ⦃ PostCond.mayThrow (fun r => ⌜ r.val = l.items.val.length ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨n, hn, hval⟩ := ssz_len_eq l
    rw [hv] at hn
    simp only [RustM.ok.injEq] at hn
    subst hn
    exact hval)

/-- `Vec::push` agrega exactamente un elemento al final. -/
theorem push_exacto_spec {T : Type} (v : alloc.vec.Vec T) (x : T) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.push v x
    ⦃ PostCond.mayThrow (fun r => ⌜ r.val = v.val ++ [x] ⌝) ⦄ :=
  triple_mayThrow_of (fun r hr => by
    unfold alloc.vec.Vec.push at hr
    obtain ⟨s, hs, hr⟩ := bind_da_ok hr
    simp only [RustM.ok.injEq] at hr
    subst hr
    unfold rust_primitives.sequence.seq_push at hs
    dsimp only at hs
    split at hs
    · simp only [RustM.ok.injEq] at hs
      subst hs
      rfl
    · simp at hs)

section
attribute [local spec] push_exacto_spec

/-- El loop que rellena los slots vacios agrega exactamente `n` elementos. -/
theorem header_loop_largo_spec (n : Std.Usize) (v0 : alloc.vec.Vec tipos.H256) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block_header_loop { start := 0#usize, «end» := n } v0
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ r.val.length = v0.val.length + n.val ⌝) ⦄ := by
  unfold stf.process_block_header_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × (alloc.vec.Vec tipos.H256) =>
       x.1.«end» = n ∧ x.1.start.val ≤ n.val ∧
       x.2.val.length = v0.val.length + x.1.start.val)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · exact ⟨rfl, by simp, by simp⟩
  · intro x hinv
    obtain ⟨iter, v⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    obtain ⟨hend, hle, hlen⟩ := hinv
    simp only at hend hle hlen
    subst hend
    unfold stf.process_block_header_loop.body
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | trivial
      | simp [PostCond.div, PostCond.mayThrow]
    -- se agrega un cero y el contador avanza uno.
    · rename_i hlt s hs r hr
      refine ⟨by omega, ?_⟩
      rw [hr]
      simp
      omega
    -- se termino el rango.
    · rename_i hge
      show v.val.length = v0.val.length + hasta.val
      omega
end

section
attribute [local spec] ssz_len_modelo_spec ST3H.current_proposer_spec
  ST3H.ok_or_spec ST3H.branch_spec ST3H.header_hash_spec ST3H.ne_default_spec
  ST7.take_modelo_spec ST7.into_inner_modelo_spec push_exacto_spec
  header_loop_largo_spec ST7.try_from_modelo_spec ST7.expect_modelo_spec
  ST3H.extend_spec ST3H.body_hash_spec ST7.from_residual_err_spec

/-- Lo que `process_block_header` le hace al historial y al slot del header. -/
theorem header_historial_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block_header state block
    ⦃ PostCond.mayThrow (fun r => ⌜ UScalarTy.Usize.numBits = 64 →
        state.historical_block_hashes.items.val.length =
          state.latest_block_header.slot.val →
        (r.1 = core.result.Result.Ok () →
           r.2.historical_block_hashes.items.val.length = block.slot.val ∧
           r.2.latest_block_header.slot = block.slot ∧
           block.slot.val ≤ 262144) ∧
        (r.1 ≠ core.result.Result.Ok () →
           r.2.historical_block_hashes = state.historical_block_hashes ∧
           r.2.latest_block_header.slot = state.latest_block_header.slot) ⌝) ⦄ := by
  unfold stf.process_block_header
  hax_mvcgen
  all_goals try first
    | rfl
    | trivial
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
  -- Las dos ramas que llegan al final, con y sin anclaje del genesis.
  -- El historial nuevo es el viejo, mas la raiz del padre, mas un cero por
  -- cada slot vacio: en total queda del largo `block.slot`.
  all_goals (
    have h64 := (by assumption : UScalarTy.Usize.numBits = 64)
    have e1 := (by assumption :
      ∀ l : ssz.SszList tipos.H256 262144#usize,
        _ = core.result.Result.Ok l → l.items = _) _ (by assumption)
    have e2 := congrArg List.length (by assumption : _ = _ ++ [_])
    have e3 := congrArg (fun v : alloc.vec.Vec tipos.H256 => v.val.length)
      (by assumption : (_ : alloc.vec.Vec tipos.H256) =
        ssz.SszList.items (Prod.fst (_ :
          ssz.SszList tipos.H256 262144#usize ×
          ssz.SszList tipos.H256 262144#usize)))
    have e4 := (by assumption : Prod.fst _ = state.historical_block_hashes)
    have hlim := limite_val
    simp only [cast_usize_64 h64] at *
    rw [e4] at e3
    simp at e2 e3
    refine ⟨⟨?_, trivial, ?_⟩, fun h => absurd rfl h⟩
    · rw [e1]; scalar_tac
    · scalar_tac)
end

/- ====================================================================
   `process_attestations` no toca el historial.
   ==================================================================== -/

theorem try_finalize_historial_spec (state : tipos.State)
    (source target : tipos.Checkpoint) (j : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    stf.try_finalize state source target j rts
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ r.1.historical_block_hashes = state.historical_block_hashes ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => by
    obtain ⟨st', j'⟩ := v
    exact (ST7.try_finalize_adelante state st' source target j j' rts hv).2)

theorem serialize_historial_spec (st : tipos.State) (j : mapa.MapaVotos)
    (vc : Std.Usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.serialize_justifications st j vc
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ r.historical_block_hashes = st.historical_block_hashes ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv => ST7.serialize_no_toca_historial st v j vc hv)

section
attribute [local spec] is_none_spec dato_en_spec bits_en_uno_en_spec
  is_valid_vote_spec primer_bit_spec votos_vacios_spec poner_si_falta_spec
  marcar_votos_spec cuenta_votos_spec sin_spec div_ceil_spec set_justified_spec
  try_finalize_historial_spec

theorem process_attestations_loop_historial_spec
    (s0 : tipos.State)
    (attestations : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (validator_count n : Std.Usize)
    (j0 : mapa.MapaVotos)
    (rts : std.collections.hash.map.HashMap tipos.H256 Std.U64
             std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations_loop { start := 0#usize, «end» := n } s0
      attestations validator_count 0#u64 j0 rts core.option.Option.None
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ r.1.historical_block_hashes = s0.historical_block_hashes ⌝) ⦄ := by
  unfold stf.process_attestations_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × Acc =>
              x.2.1.historical_block_hashes = s0.historical_block_hashes)
    (γ := Nat) (rel := (· < ·)) (termination := fun _ => 0)
  · exact Nat.lt_wfRel.wf
  · rfl
  · intro x hinv
    obtain ⟨iter, st, ap, jj, fl⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    simp only at hinv
    unfold stf.process_attestations_loop.body
    hax_mvcgen
    all_goals try (refine ⟨?_, Or.inr ?_⟩)
    all_goals try first
      | rfl
      | assumption
      | trivial
      | simp [PostCond.div, PostCond.mayThrow]
      | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
end

section
attribute [local spec] timer_spec inc_procesadas_spec contar_datos_spec
  hay_raiz_cero_spec construir_mapa_spec construir_rts_spec ssz_len_spec
  bitlist_len_spec serialize_historial_spec
  process_attestations_loop_historial_spec

theorem process_attestations_historial_spec (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_attestations state atts
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ r.2.historical_block_hashes = state.historical_block_hashes ⌝) ⦄ := by
  unfold stf.process_attestations
  hax_mvcgen
  all_goals try first
    | rfl
    | assumption
    | trivial
    | simp [PostCond.div, PostCond.mayThrow]
    | (simp_all [PostCond.okAssertion, PostCond.mayThrow]; done)
end

/- ====================================================================
   El invariante y su conservacion.
   ==================================================================== -/

/-- El historial tiene exactamente un hash por slot, y el slot del ultimo
    header no pasa del tope del historial. Vale en el genesis. -/
def HistorialAcotado (st : tipos.State) : Prop :=
  st.historical_block_hashes.items.val.length =
    st.latest_block_header.slot.val ∧
  st.latest_block_header.slot.val ≤ 262144

theorem header_historial (state state' : tipos.State) (block : tipos.Block)
    (res : core.result.Result Unit stf.Error)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hh : HistorialAcotado state)
    (h : stf.process_block_header state block = ok (res, state')) :
    HistorialAcotado state' := by
  obtain ⟨hok, hfail⟩ :=
    of_triple_mayThrow (header_historial_spec state block) h h64 hh.1
  by_cases hres : res = core.result.Result.Ok ()
  · obtain ⟨e1, e2, e3⟩ := hok hres
    exact ⟨by rw [e1, e2], by rw [e2]; exact e3⟩
  · obtain ⟨e1, e2⟩ := hfail hres
    exact ⟨by rw [e1, e2]; exact hh.1, by rw [e2]; exact hh.2⟩

theorem atts_historial (state state' : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize)
    (res : core.result.Result Unit stf.Error)
    (hh : HistorialAcotado state)
    (h : stf.process_attestations state atts = ok (res, state')) :
    HistorialAcotado state' := by
  have e1 := of_triple_mayThrow (process_attestations_historial_spec state atts) h
  have e2 := of_triple_mayThrow (ST2.process_attestations_header_spec state atts) h
  simp only at e1 e2
  exact ⟨by rw [e1, e2]; exact hh.1, by rw [e2]; exact hh.2⟩

theorem slots_historial (state state' : tipos.State) (t : Std.U64)
    (res : core.result.Result Unit stf.Error)
    (hh : HistorialAcotado state)
    (h : stf.process_slots state t = ok (res, state')) :
    HistorialAcotado state' := by
  obtain ⟨-, -, e3, e4⟩ := ST7.process_slots_no_toca state state' t res h
  exact ⟨by rw [e3, e4]; exact hh.1, by rw [e4]; exact hh.2⟩

theorem header_hist_inv_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_block_header state block
    ⦃ PostCond.mayThrow (fun r => ⌜ UScalarTy.Usize.numBits = 64 →
        HistorialAcotado state → HistorialAcotado r.2 ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv h64 hh => by
    obtain ⟨res, st'⟩ := v
    exact header_historial state st' block res h64 hh hv)

theorem atts_hist_inv_spec (state : tipos.State)
    (atts : ssz.SszList tipos.AggregatedAttestation 4096#usize) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_attestations state atts
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ HistorialAcotado state → HistorialAcotado r.2 ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv hh => by
    obtain ⟨res, st'⟩ := v
    exact atts_historial state st' atts res hh hv)

theorem slots_hist_inv_spec (state : tipos.State) (t : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_slots state t
    ⦃ PostCond.mayThrow (fun r =>
        ⌜ HistorialAcotado state → HistorialAcotado r.2 ⌝) ⦄ :=
  triple_mayThrow_of (fun v hv hh => by
    obtain ⟨res, st'⟩ := v
    exact slots_historial state st' t res hh hv)

section
attribute [local spec] ST3H.branch_spec ST3H.from_residual_spec
  ST3T.time_block_spec header_hist_inv_spec atts_hist_inv_spec

theorem process_block_hist_inv_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_block state block
    ⦃ PostCond.mayThrow (fun r => ⌜ UScalarTy.Usize.numBits = 64 →
        HistorialAcotado state → HistorialAcotado r.2 ⌝) ⦄ := by
  unfold stf.process_block
  hax_mvcgen
  all_goals solve_by_elim
end

section
attribute [local spec] ST3H.branch_spec ST3H.from_residual_spec
  ST3H.ne_default_spec ST3T.time_transition_spec ST3T.state_hash_spec
  slots_hist_inv_spec process_block_hist_inv_spec

theorem state_transition_hist_inv_spec (state : tipos.State) (block : tipos.Block) :
    ⦃ ⌜ True ⌝ ⦄ stf.state_transition state block
    ⦃ PostCond.mayThrow (fun r => ⌜ UScalarTy.Usize.numBits = 64 →
        HistorialAcotado state → HistorialAcotado r.2 ⌝) ⦄ := by
  unfold stf.state_transition
  hax_mvcgen
  all_goals solve_by_elim
end

/- ====================================================================
   Los enunciados.
   ==================================================================== -/

/-- El caso inicial: historial vacio y header en el slot cero. -/
theorem historialAcotado_inicial (st : tipos.State)
    (hh : st.historical_block_hashes.items.val = [])
    (hs : st.latest_block_header.slot.val = 0) : HistorialAcotado st := by
  unfold HistorialAcotado
  rw [hh, hs]
  simp

/-- La transicion de un bloque conserva "un hash por slot, y el slot no pasa
    del tope", acepte el bloque o lo rechace. -/
theorem state_transition_conserva_historial
    (state state' : tipos.State) (block : tipos.Block)
    (res : core.result.Result Unit stf.Error)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hh : HistorialAcotado state)
    (h : stf.state_transition state block = ok (res, state')) :
    HistorialAcotado state' :=
  of_triple_mayThrow (state_transition_hist_inv_spec state block) h h64 hh

/-- Si el historial tiene un hash por slot, `process_block_header` no acepta
    ningun bloque con slot mayor que 262144. -/
theorem header_acepta_slot_acotado
    (state state' : tipos.State) (block : tipos.Block)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hlen : state.historical_block_hashes.items.val.length =
              state.latest_block_header.slot.val)
    (h : stf.process_block_header state block =
           ok (core.result.Result.Ok (), state')) :
    block.slot.val ≤ 262144 :=
  ((of_triple_mayThrow (header_historial_spec state block) h h64 hlen).1 rfl).2.2

/-- Con los dos invariantes, la ventana no pasa de su capacidad. -/
theorem ventana_en_capacidad (st : tipos.State)
    (hv : VentanaNoPasa st) (hh : HistorialAcotado st) :
    st.justified_slots.bits.val.length ≤ 262144 := by
  unfold VentanaNoPasa at hv
  have := hh.2
  omega

/-- Y entonces `shift_window` sobre la ventana de un estado asi no entra en
    panico: devuelve, y devuelve la ventana corrida. Es la hipotesis de
    capacidad del teorema 10, descargada. -/
theorem shift_window_no_falla (st : tipos.State) (delta : Std.Usize)
    (hv : VentanaNoPasa st) (hh : HistorialAcotado st) :
    ∃ slots', justified_slots_ops.shift_window st.justified_slots delta = ok slots' ∧
      slots'.bits.val = st.justified_slots.bits.val.drop delta.val :=
  shift_window_devuelve st.justified_slots delta (ventana_en_capacidad st hv hh)

/-- Los dos invariantes juntos se conservan a lo largo de la transicion. -/
theorem state_transition_conserva_acotado
    (state state' : tipos.State) (block : tipos.Block)
    (res : core.result.Result Unit stf.Error)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hv : VentanaNoPasa state) (hh : HistorialAcotado state)
    (h : stf.state_transition state block = ok (res, state')) :
    VentanaNoPasa state' ∧ HistorialAcotado state' :=
  ⟨state_transition_conserva_ventana state state' block res h64 hv h,
   state_transition_conserva_historial state state' block res h64 hh h⟩

end HC

/- ===========================================================================
   Teorema 14: cinco funciones de la transicion no entran en panico
   (17 nov 2026)

   El teorema 10 lo hizo para el modulo auxiliar de la ventana. Aca empieza
   la transicion propiamente dicha, por las cinco funciones chicas de
   `stf.rs`:

     - `current_proposer`: devuelve siempre. Sin validadores, `None`; con
       validadores, `Some(slot % n)`. El enunciado dice que devuelve, no solo
       que devuelve.
     - `is_proposer`: devuelve siempre.
     - `slot_is_justifiable_after`: devuelve siempre. La unica cuenta que
       podria desbordar es el cuadrado de la raiz entera, y no desborda
       porque no supera al numero del que se saco la raiz.
     - `attestation_data_matches_chain`: devuelve siempre. Cada indice se
       chequea contra el largo antes de leer.
     - `is_valid_vote`: devuelve siempre, para cualquier estado y cualquier
       voto.

   Ninguna lleva hipotesis: valen para toda entrada.

   Hizo falta que `core.bool.Bool.then` dejara de ser un axioma (ver
   supuestos/FunsExternal.lean), porque `current_proposer` es
   `(n > 0).then(|| slot % n)`. Y que la igualdad de `H256` termine: el loop
   de 32 bytes, ahora con medida de terminacion y con los dos indices en
   rango.

   Los cinco resultados dependen solo de los tres axiomas estandar de Lean.
   Es la primera vez en este archivo que un resultado sobre el codigo
   traducido no arrastra ni un axioma nativo ni una declaracion sin
   contenido. Siguen apoyandose en dos modelos nuestros, `bool::then` e
   `isqrt`, que son definiciones y por eso no aparecen en `#print axioms`.
   =========================================================================== -/

namespace NP2
open mini_stf
open Std.Tactic
open ST3 JS NP

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

/-- El resto de la division devuelve, si el divisor no es cero. -/
theorem rem_eq (x n : Std.U64) (h : n.val ≠ 0) :
    ∃ r : Std.U64, (x % n : RustM Std.U64) = ok r ∧ r.val = x.val % n.val :=
  WP.spec_imp_exists (UScalar.rem_spec x h)

/-- `current_proposer`: nunca entra en panico. Sin validadores devuelve
    `None`; con validadores, `Some(slot % n)`. -/
theorem current_proposer_eq (slot n : Std.U64) :
    (n.val = 0 → stf.current_proposer slot n = ok none) ∧
    (n.val ≠ 0 → ∃ r : Std.U64,
       stf.current_proposer slot n = ok (some r) ∧ r.val = slot.val % n.val) := by
  unfold stf.current_proposer
  constructor
  · intro h0
    have hn : ¬ (n > 0#u64) := by scalar_tac
    simp [core.bool.Bool.then, hn]
  · intro hne
    have hn : n > 0#u64 := by scalar_tac
    obtain ⟨r, hr, hv⟩ := rem_eq slot n hne
    refine ⟨r, ?_, hv⟩
    simp [core.bool.Bool.then, hn,
      stf.current_proposer.closure.Insts.CoreOpsFunctionFnOnceTupleU64.call_once, hr]

theorem current_proposer_total (slot n : Std.U64) :
    ∃ o, stf.current_proposer slot n = ok o := by
  obtain ⟨h0, hne⟩ := current_proposer_eq slot n
  by_cases h : n.val = 0
  · exact ⟨_, h0 h⟩
  · obtain ⟨r, hr, -⟩ := hne h
    exact ⟨_, hr⟩

/-- `is_proposer` nunca entra en panico. -/
theorem is_proposer_total (v slot n : Std.U64) :
    ∃ b, stf.is_proposer v slot n = ok b := by
  obtain ⟨o, ho⟩ := current_proposer_total slot n
  unfold stf.is_proposer
  rw [ho]
  cases o <;>
    simp [core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.U64.Insts.CoreCmpPartialEqU64]

theorem isqrt_total (x : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ core.num.U64.isqrt x ⦃ ⇓ r => ⌜ r.val = Nat.sqrt x.val ⌝ ⦄ :=
  triple_total_of ⟨_, rfl, rfl⟩

theorem pow_total (x : Std.U64) (e : Std.U32) :
    ⦃ ⌜ x.val ^ e.val ≤ U64.max ⌝ ⦄ core.num.U64.pow x e
    ⦃ ⇓ r => ⌜ r.val = x.val ^ e.val ⌝ ⦄ := by
  by_cases hp : x.val ^ e.val ≤ U64.max
  · simp [core.num.U64.pow, rust_primitives.arithmetic.pow_u64, UScalar.tryMk,
      UScalar.tryMkOpt, RustM.ofOption, hp, Triple, WP.wp, PredTrans.apply]
    have hlt : x.val ^ e.val < 18446744073709551616 := by scalar_tac
    simp [hlt]
  · simp [hp, Triple, WP.wp, PredTrans.apply]

theorem checked_sub_total (x y : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ core.num.U64.checked_sub x y ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  triple_total_of ⟨_, checked_sub_eq x y, trivial⟩

theorem checked_mul_devuelve (x y : Std.U64) :
    ∃ o, core.num.U64.checked_mul x y = ok o := by
  simp [core.num.U64.checked_mul, core.num.U64.overflowing_mul,
    rust_primitives.arithmetic.overflowing_mul_u64, uoverflowing_mul]
  split <;> simp

theorem checked_add_devuelve (x y : Std.U64) :
    ∃ o, core.num.U64.checked_add x y = ok o := by
  simp [core.num.U64.checked_add, core.num.U64.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_u64]
  generalize UScalar.overflowing_add x y = p
  obtain ⟨r, ov⟩ := p
  cases ov <;> simp

theorem checked_mul_total (x y : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ core.num.U64.checked_mul x y ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  obtain ⟨o, ho⟩ := checked_mul_devuelve x y
  exact triple_total_of ⟨o, ho, trivial⟩

theorem checked_add_total (x y : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ core.num.U64.checked_add x y ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  obtain ⟨o, ho⟩ := checked_add_devuelve x y
  exact triple_total_of ⟨o, ho, trivial⟩

section
attribute [local spec] checked_sub_total isqrt_total pow_total
  checked_mul_total checked_add_total

/-- `slot_is_justifiable_after` nunca entra en panico. La unica cuenta que
    podria desbordar es el cuadrado de la raiz entera, y no desborda porque
    no supera al numero del que se saco la raiz. -/
theorem slot_is_justifiable_total_spec (s f : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ stf.slot_is_justifiable_after s f ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold stf.slot_is_justifiable_after
  simp only [core.option.Option.and_then, core.option.Option.is_some_and,
    stf.slot_is_justifiable_after.closure.Insts.CoreOpsFunctionFnOnceTupleU64OptionU64,
    stf.slot_is_justifiable_after.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64Bool,
    stf.slot_is_justifiable_after.closure.Insts.CoreOpsFunctionFnOnceTupleU64OptionU64.call_once,
    stf.slot_is_justifiable_after.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once]
  hax_mvcgen
  -- Los dos lugares donde se eleva al cuadrado una raiz entera.
  all_goals (
    rename_i r hr
    rw [hr]
    have h2 : (2#u32 : Std.U32).val = 2 := rfl
    rw [h2]
    refine le_trans (Nat.sqrt_le' _) ?_
    scalar_tac)
end

theorem slot_is_justifiable_total (s f : Std.U64) :
    ∃ b, stf.slot_is_justifiable_after s f = ok b := by
  obtain ⟨b, hb, -⟩ := of_triple_total (slot_is_justifiable_total_spec s f)
  exact ⟨b, hb⟩

/- ====================================================================
   La igualdad de `H256` termina y no entra en panico.
   ==================================================================== -/

theorem array_eq_loop_total (a b : Array Std.U8 32#usize) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreCmpPartialEqArray.eq_loop
      core.U8.Insts.CoreCmpPartialEqU8 a b 0#usize
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop
  apply Aeneas.Std.loop_spec
    (inv := fun i : Std.Usize => i.val ≤ 32)
    (γ := Nat) (rel := (· < ·)) (termination := fun i => 32 - i.val)
  · exact Nat.lt_wfRel.wf
  · simp
  · intro i hinv
    unfold core.Array.Insts.CoreCmpPartialEqArray.eq_loop.body
    simp only [core.U8.Insts.CoreCmpPartialEqU8]
    hax_mvcgen
    all_goals first
      -- el byte coincide: el indice avanza y lo que falta baja.
      | (refine ⟨?_, Or.inl ?_⟩ <;> scalar_tac)
      -- `i + 1` no desborda, y los dos indices estan en rango.
      | (exfalso; scalar_tac)
      | (exfalso; simp [Array.to_slice] at *; scalar_tac)

theorem h256_eq_total (a b : tipos.H256) :
    ⦃ ⌜ True ⌝ ⦄ tipos.H256.Insts.CoreCmpPartialEqH256.eq a b
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold tipos.H256.Insts.CoreCmpPartialEqH256.eq
  exact array_eq_loop_total a b

section
attribute [local spec] h256_eq_total

/-- `attestation_data_matches_chain` nunca entra en panico: cada indice se
    chequea contra el largo antes de leer. -/
theorem matches_chain_total_spec (s : Slice tipos.H256) (d : tipos.AttestationData) :
    ⦃ ⌜ True ⌝ ⦄ stf.attestation_data_matches_chain s d ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold stf.attestation_data_matches_chain
  simp only [core.slice.Slice.len]
  hax_mvcgen
end

theorem matches_chain_total (s : Slice tipos.H256) (d : tipos.AttestationData) :
    ∃ b, stf.attestation_data_matches_chain s d = ok b := by
  obtain ⟨b, hb, -⟩ := of_triple_total (matches_chain_total_spec s d)
  exact ⟨b, hb⟩

/- ====================================================================
   `is_valid_vote` nunca entra en panico.
   ==================================================================== -/

theorem is_slot_justified_total_spec (b : ssz.SszBitlist 262144#usize)
    (x y : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ justified_slots_ops.is_slot_justified b x y
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  obtain ⟨r, hr⟩ := is_slot_justified_total b x y
  exact triple_total_of ⟨r, hr, trivial⟩

/-- `branch` sobre un `Result` devuelve siempre, y si corta (`Break`) lo que
    lleva adentro es un `Err`. -/
theorem branch_total {T E : Type} (r : core.result.Result T E) :
    ⦃ ⌜ True ⌝ ⦄ core.result.Result.Insts.CoreOpsTry_traitTry.branch r
    ⦃ ⇓ cf => ⌜ ∀ res, cf = core.ops.control_flow.ControlFlow.Break res →
        ∃ e, res = core.result.Result.Err e ⌝ ⦄ :=
  triple_total_of (by
    cases r with
    | Ok x =>
      refine ⟨core.ops.control_flow.ControlFlow.Continue x, ?_, ?_⟩
      · simp [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
      · intro res h; cases h
    | Err e =>
      refine ⟨core.ops.control_flow.ControlFlow.Break
                (core.result.Result.Err e), ?_, ?_⟩
      · simp [core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
      · intro res h
        injection h with h
        exact ⟨e, h.symm⟩)

/-- `from_residual` devuelve si el residuo es un `Err`. -/
theorem from_residual_total (T : Type) {E : Type}
    (r : core.result.Result core.convert.Infallible E) :
    ⦃ ⌜ ∃ e, r = core.result.Result.Err e ⌝ ⦄
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
      T (core.convert.From.Blanket E) r
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  cases r with
  | Ok x => simp [Triple, WP.wp, PredTrans.apply]
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      core.convert.From.Blanket.from, Triple, WP.wp, PredTrans.apply]

theorem ssz_deref_total {T : Type} {N : Std.Usize} (l : ssz.SszList T N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszList.Insts.CoreOpsDerefDerefSlice.deref l
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  triple_total_of (by
    refine ⟨l.items, ?_, trivial⟩
    simp [ssz.SszList.Insts.CoreOpsDerefDerefSlice.deref,
      alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
      rust_primitives.sequence.seq_to_slice])

section
attribute [local spec] is_slot_justified_total_spec branch_total
  from_residual_total ssz_deref_total matches_chain_total_spec
  slot_is_justifiable_total_spec

/-- `is_valid_vote` nunca entra en panico, para cualquier estado y cualquier
    voto. -/
theorem is_valid_vote_total_spec (st : tipos.State) (d : tipos.AttestationData) :
    ⦃ ⌜ True ⌝ ⦄ stf.is_valid_vote st d ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold stf.is_valid_vote
  hax_mvcgen
  -- Los dos `?`: cuando `branch` corta, lo que lleva es un `Err`, y con eso
  -- `from_residual` devuelve.
  all_goals (
    rename_i h
    exact h _ rfl)
end

theorem is_valid_vote_total (st : tipos.State) (d : tipos.AttestationData) :
    ∃ r, stf.is_valid_vote st d = ok r := by
  obtain ⟨r, hr, -⟩ := of_triple_total (is_valid_vote_total_spec st d)
  exact ⟨r, hr⟩

end NP2

/- ===========================================================================
   Teorema 15 — `process_slots` y `process_block_header` no entran en panico

   Siguen las dos funciones de `stf.rs` que hashean. El hash de este crate es
   un sustituto del de ustedes (ver la propuesta), asi que no probamos que
   termine: "el hash devuelve" va escrito como hipotesis en cada enunciado,
   una por cada llamada.

   `process_slots` no lleva ninguna otra hipotesis. Su unica resta,
   `target_slot - state.slot`, esta protegida por el chequeo de arriba.

   `process_block_header` lleva dos mas:

   - `usize` de 64 bits, por el `as usize` de `num_empty_slots`.
   - que el historial tenga tantas entradas como el slot del ultimo header.
     Es la primera mitad de `HC.HistorialAcotado`, que el teorema 13 prueba
     que la transicion conserva.

   La segunda hace falta de verdad. El largo nuevo se calcula como
   `current_len + 1 + num_empty_slots` ANTES de compararlo contra
   `HISTORICAL_ROOTS_LIMIT`. Con el historial alineado esa suma vale
   exactamente `block.slot` y entra en un `u64`. Sin esa hipotesis la prueba
   no cierra: quedan abiertas esas dos sumas y la capacidad de la ventana
   (control negativo en la bitacora). No es un estado alcanzable segun el
   teorema 13; es la precondicion que el codigo da por sentada.

   Con esas hipotesis, todo lo demas sale: las dos restas, el `push`, el loop
   que rellena los slots vacios (ahora con medida de terminacion), el
   `try_from` cuyo `expect` dice "pre-validated", y `extend_to_slot`, que
   recibe una ventana que entra en la capacidad.
   =========================================================================== -/

namespace NP3
open mini_stf
open Std.Tactic
open ST3 JS NP NP2 VC VI HC

set_option mvcgen.warning false
set_option maxHeartbeats 8000000

/-- Un lema para usar "esta llamada devuelve" como hipotesis. -/
theorem devuelve_spec {α : Type} (x : RustM α) (h : ∃ r, x = ok r) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  obtain ⟨r, hr⟩ := h
  exact triple_total_of ⟨r, hr, trivial⟩

theorem state_hash_total (s : tipos.State)
    (h : ∃ r, tipos.State.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root s = ok r) :
    ⦃ ⌜ True ⌝ ⦄ tipos.State.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root s
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := devuelve_spec _ h

theorem time_slots_total :
    ⦃ ⌜ True ⌝ ⦄ stubs.metrics.time_slots_processing ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  triple_total_of ⟨(), rfl, trivial⟩

theorem inc_slots_total (c : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ stubs.metrics.inc_slots_processed c ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  triple_total_of ⟨(), rfl, trivial⟩

section
attribute [local spec] h256_eq_total state_hash_total time_slots_total
  inc_slots_total

/-- `process_slots` no entra en panico, si el hash del estado devuelve. -/
theorem process_slots_total_spec (state : tipos.State) (t : Std.U64)
    (hhash : ∃ r, tipos.State.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root state = ok r) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_slots state t ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold stf.process_slots
  hax_mvcgen
  -- `target_slot - state.slot` no desborda por abajo: el chequeo de arriba
  -- ya descarto `state.slot >= target_slot`.
  all_goals (exfalso; scalar_tac)
end

theorem process_slots_devuelve (state : tipos.State) (t : Std.U64)
    (hhash : ∃ r, tipos.State.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root state = ok r) :
    ∃ r, stf.process_slots state t = ok r := by
  obtain ⟨r, hr, -⟩ := of_triple_total (process_slots_total_spec state t hhash)
  exact ⟨r, hr⟩

/- ====================================================================
   Las piezas de `process_block_header`, ahora totales.
   ==================================================================== -/

theorem ssz_len_total {T : Type} {N : Std.Usize} (l : ssz.SszList T N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszList.len l ⦃ ⇓ r => ⌜ r.val = l.items.val.length ⌝ ⦄ :=
  triple_total_of (ssz_len_eq l)

theorem current_proposer_total_spec (a b : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄ stf.current_proposer a b ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  devuelve_spec _ (current_proposer_total a b)

theorem ok_or_total {T E : Type} (o : core.option.Option T) (e : E) :
    ⦃ ⌜ True ⌝ ⦄ core.option.Option.ok_or o e ⦃ ⇓ _ => ⌜ True ⌝ ⦄ :=
  triple_total_of (by cases o <;> exact ⟨_, rfl, trivial⟩)

theorem ne_default_total (a b : tipos.H256) :
    ⦃ ⌜ True ⌝ ⦄
    core.cmp.PartialEq.ne.default tipos.H256.Insts.CoreCmpPartialEqH256 a b
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  obtain ⟨b', hb, -⟩ := of_triple_total (h256_eq_total a b)
  refine triple_total_of ⟨decide (b' = false), ?_, trivial⟩
  unfold core.cmp.PartialEq.ne.default
  show (do let b ← tipos.H256.Insts.CoreCmpPartialEqH256.eq a b
           ok (decide (b = false))) = _
  rw [hb]
  rfl

theorem header_hash_total (h : tipos.BlockHeader)
    (hd : ∃ r, tipos.BlockHeader.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root h = ok r) :
    ⦃ ⌜ True ⌝ ⦄ tipos.BlockHeader.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root h
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := devuelve_spec _ hd

theorem body_hash_total (b : tipos.BlockBody)
    (hd : ∃ r, tipos.BlockBody.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root b = ok r) :
    ⦃ ⌜ True ⌝ ⦄ tipos.BlockBody.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root b
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := devuelve_spec _ hd

/-- `mem::take` sobre el historial devuelve, y devuelve lo que habia. -/
theorem take_ssz_total (x : ssz.SszList tipos.H256 262144#usize) :
    ⦃ ⌜ True ⌝ ⦄
    core.mem.take (ssz.SszList.Insts.CoreDefaultDefault tipos.H256 262144#usize) x
    ⦃ ⇓ r => ⌜ r.1.items.val.length = x.items.val.length ⌝ ⦄ :=
  triple_total_of (by
    refine ⟨(x, { items := Slice.new tipos.H256 }), ?_, rfl⟩
    simp [core.mem.take, ssz.SszList.Insts.CoreDefaultDefault.default, ssz.SszList.new,
      alloc.vec.Vec.new, rust_primitives.sequence.seq_empty])

theorem into_inner_total {T : Type} {N : Std.Usize} (l : ssz.SszList T N) :
    ⦃ ⌜ True ⌝ ⦄ ssz.SszList.into_inner l ⦃ ⇓ r => ⌜ r = l.items ⌝ ⦄ :=
  triple_total_of ⟨l.items, rfl, rfl⟩

/-- `Vec::push` devuelve si hay lugar para un elemento mas. -/
theorem push_total {T : Type} (v : alloc.vec.Vec T) (x : T)
    (h : v.val.length < Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ alloc.vec.Vec.push v x
    ⦃ ⇓ r => ⌜ r.val.length = v.val.length + 1 ⌝ ⦄ := by
  have hle : (v.val ++ [x]).length ≤ Usize.max := by simp; omega
  refine triple_total_of ⟨⟨v.val ++ [x], hle⟩, ?_, by simp⟩
  simp only [alloc.vec.Vec.push, rust_primitives.sequence.seq_push]
  rw [dif_pos hle]
  rfl

/-- El `try_from` de un vector que entra en la capacidad da `Ok`. -/
theorem try_from_total {T : Type} (N : Std.Usize) (v : alloc.vec.Vec T)
    (h : v.val.length ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    ssz.SszList.Insts.CoreConvertTryFromVecFueraDeCapacidad.try_from N v
    ⦃ ⇓ r => ⌜ ∃ t, r = core.result.Result.Ok t ⌝ ⦄ :=
  triple_total_of (by
    refine ⟨core.result.Result.Ok { items := v }, ?_, _, rfl⟩
    have : ¬ N.val < v.val.length := by omega
    simp [ssz.SszList.Insts.CoreConvertTryFromVecFueraDeCapacidad.try_from,
      alloc.vec.Vec.len, rust_primitives.sequence.seq_len, this])

section
attribute [local spec] push_total

/-- El loop que rellena los slots vacios termina y no entra en panico, si
    lo que va a quedar entra en un `Vec`. -/
theorem header_loop_total (n : Std.Usize) (v0 : alloc.vec.Vec tipos.H256)
    (hcap : v0.val.length + n.val ≤ Usize.max) :
    ⦃ ⌜ True ⌝ ⦄
    stf.process_block_header_loop { start := 0#usize, «end» := n } v0
    ⦃ ⇓ r => ⌜ r.val.length = v0.val.length + n.val ⌝ ⦄ := by
  unfold stf.process_block_header_loop
  apply Aeneas.Std.loop_spec
    (inv := fun x : (core.ops.range.Range Std.Usize) × (alloc.vec.Vec tipos.H256) =>
       x.1.«end» = n ∧ x.1.start.val ≤ n.val ∧
       x.2.val.length = v0.val.length + x.1.start.val)
    (γ := Nat) (rel := (· < ·))
    (termination := fun x => x.1.«end».val - x.1.start.val)
  · exact Nat.lt_wfRel.wf
  · exact ⟨rfl, by simp, by simp⟩
  · intro x hinv
    obtain ⟨iter, v⟩ := x
    obtain ⟨desde, hasta⟩ := iter
    obtain ⟨hend, hle, hlen⟩ := hinv
    simp only at hend hle hlen
    subst hend
    unfold stf.process_block_header_loop.body
    hax_mvcgen
    -- 1. El `push` tiene lugar.
    · omega
    -- 2. Se agrego un cero, y el contador baja.
    · rename_i hlt s hs r hr
      exact ⟨⟨trivial, by omega, by omega⟩, Or.inl (by omega)⟩
    -- 3. Se termino el rango.
    · rename_i hge
      show v.val.length = v0.val.length + hasta.val
      omega
end

section
attribute [local spec] ssz_len_total current_proposer_total_spec ok_or_total
  branch_total header_hash_total ne_default_total take_ssz_total
  into_inner_total push_total header_loop_total try_from_total expect_total
  extend_to_slot_total_spec body_hash_total from_residual_total

theorem process_block_header_total_spec (state : tipos.State) (block : tipos.Block)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hlen : state.historical_block_hashes.items.val.length =
      state.latest_block_header.slot.val)
    (hpadre : ∃ r, tipos.BlockHeader.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root
      state.latest_block_header = ok r)
    (hcuerpo : ∃ r, tipos.BlockBody.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root
      block.body = ok r) :
    ⦃ ⌜ True ⌝ ⦄ stf.process_block_header state block ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold stf.process_block_header
  hax_mvcgen
  all_goals (have hlim := limite_val)
  all_goals try subst_vars
  all_goals try simp only [cast_usize_64 h64] at *
  -- Lo que queda es aritmetica: ninguna resta baja de cero, ninguna suma
  -- desborda, y lo que se arma entra en la capacidad. La ultima meta es el
  -- error de `ok_or`, que se propaga tal cual.
  all_goals first
    | scalar_tac
    | (exfalso; scalar_tac)
    | simp_all
end

/-- `process_block_header` no entra en panico. -/
theorem process_block_header_devuelve (state : tipos.State) (block : tipos.Block)
    (h64 : UScalarTy.Usize.numBits = 64)
    (hlen : state.historical_block_hashes.items.val.length =
      state.latest_block_header.slot.val)
    (hpadre : ∃ r, tipos.BlockHeader.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root
      state.latest_block_header = ok r)
    (hcuerpo : ∃ r, tipos.BlockBody.Insts.Mini_stfTiposHashTreeRoot.hash_tree_root
      block.body = ok r) :
    ∃ r, stf.process_block_header state block = ok r := by
  obtain ⟨r, hr, -⟩ := of_triple_total
    (process_block_header_total_spec state block h64 hlen hpadre hcuerpo)
  exact ⟨r, hr⟩

end NP3

#print axioms bind_da_ok
#print axioms try_finalize_no_retrocede
#print axioms try_finalize_no_toca_justified
#print axioms ST3.process_attestations_loop_no_retrocede
#print axioms ST3.process_attestations_no_retrocede
#print axioms ST3.process_slots_no_toca_checkpoints
#print axioms ST3F.process_attestations_fin_no_retrocede
#print axioms ST3H.process_block_header_no_mueve_slots
#print axioms ST3T.process_block_no_retrocede
#print axioms ST3.state_transition_no_retrocede
#print axioms ST7.h256_eq_true
#print axioms ST7.process_attestations_adelante
#print axioms ST7.process_block_header_no_toca_checkpoints
#print axioms ST7.state_transition_adelante
#print axioms ST1.process_slots_avanza
#print axioms ST1.process_slots_rechaza
#print axioms ST2.process_block_header_slot
#print axioms ST2.state_transition_conserva_no_genesis
#print axioms ST4.state_transition_justificado_ge_finalizado
#print axioms ST6.finalizacion_irreversible
#print axioms JS.set_luego_is_justified
#print axioms JS.extend_to_slot_no_pierde_bits
#print axioms JS.shift_window_corre
#print axioms JS.extend_to_slot_conserva_respuestas
#print axioms JS.finalizar_conserva_justificados
#print axioms NP.is_slot_justified_total
#print axioms NP.set_justified_total
#print axioms NP.set_justified_panico
#print axioms NP.set_justified_tras_voto_valido
#print axioms NP.extend_to_slot_devuelve
#print axioms NP.shift_window_devuelve
#print axioms NP.finalizar_conserva_justificados_total
#print axioms VC.tras_header_cubre
#print axioms VC.tras_header_rechaza
#print axioms VI.state_transition_conserva_ventana
#print axioms VI.state_transition_ventana_justa
#print axioms VI.tras_header_rechaza_inv
#print axioms HC.header_acepta_slot_acotado
#print axioms HC.state_transition_conserva_acotado
#print axioms HC.shift_window_no_falla
#print axioms NP2.current_proposer_eq
#print axioms NP2.is_proposer_total
#print axioms NP2.slot_is_justifiable_total
#print axioms NP2.matches_chain_total
#print axioms NP2.is_valid_vote_total
#print axioms NP3.process_slots_devuelve
#print axioms NP3.process_block_header_devuelve
