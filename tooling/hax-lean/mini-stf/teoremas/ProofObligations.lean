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

   `ST-3` es una de las 36 proposiciones de NyxFoundation/formal-leanSpec:

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
   ST-3 mitad 2: donde quedo, 4 nov

   Falta la otra mitad: que `latest_justified.slot` tampoco retroceda en el
   loop de `process_attestations`. El intento esta en
   `teoremas/ST3-en-progreso.lean`, que NO es parte de la biblioteca.

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

#print axioms bind_da_ok
#print axioms try_finalize_no_retrocede
#print axioms try_finalize_no_toca_justified
