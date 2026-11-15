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
