/- Teoremas escritos a mano sobre las definiciones extraidas.

   hax crea este archivo una vez y despues no lo toca. Es donde van los
   enunciados: la traduccion da las definiciones, los teoremas los pone
   una persona.

   Copia de trabajo: este archivo vive en `teoremas/` del crate (que si se
   commitea) y se copia a `proofs/lean/MiniStf/Verification/` (que no).
-/
import MiniStf

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
