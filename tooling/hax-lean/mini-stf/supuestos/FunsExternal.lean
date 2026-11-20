-- [mini_stf]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import MiniStf.Extraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open mini_stf

/- ⚠️ ACA NO VAN AXIOMAS DE FUNCIONES QUE SE EXTRAEN.

   Hasta el 5 nov este archivo tenia dos axiomas muertos,
   `stf.process_attestations` y `stf.serialize_justifications`, de cuando esas
   dos funciones eran `--opaque`. Se reescribieron y hoy traducen con cuerpo
   completo, pero los axiomas quedaron, con las firmas viejas (`HashMap` donde
   hoy va `mapa.MapaVotos`).

   Y no chocaban con las definiciones generadas, que es lo peligroso: este
   archivo NO abre `namespace mini_stf`, asi que declara `stf.foo` a secas
   mientras el generado declara `mini_stf.stf.foo`. Son dos nombres distintos.
   Al escribir `stf.foo` con `open mini_stf`, gana el axioma.

   O sea que se puede escribir un teorema contra el axioma en vez de contra el
   codigo, y compila. No prueba nada y parece que si. Lo unico que lo delata es
   `#print axioms`.

   Es un riesgo del flujo y no un descuido: hax siembra este archivo UNA vez y
   despues no lo vuelve a mirar, asi que cuando una funcion deja de ser opaca
   su axioma se queda. Al sacar un `--opaque`, sacar tambien su axioma de aca,
   y revisar `#print axioms` de los teoremas.
-/

/-- [mini_stf::ssz::{impl core::fmt::Debug for mini_stf::ssz::FueraDeCapacidad}::fmt]:
    Source: 'src/ssz.rs', lines 15:9-15:14
    Visibility: public -/
axiom ssz.FueraDeCapacidad.Insts.CoreFmtDebug.fmt
  :
  ssz.FueraDeCapacidad → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::ssz::{impl core::fmt::Debug for mini_stf::ssz::SszList<T, N>}::fmt]:
    Source: 'src/ssz.rs', lines 19:9-19:14
    Visibility: public -/
axiom ssz.SszList.Insts.CoreFmtDebug.fmt
  {T : Type} {N : Std.Usize} (corefmtDebugInst : core.fmt.Debug T) :
  ssz.SszList T N → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::ssz::{impl core::fmt::Debug for mini_stf::ssz::SszBitlist<N>}::fmt]:
    Source: 'src/ssz.rs', lines 91:9-91:14
    Visibility: public -/
axiom ssz.SszBitlist.Insts.CoreFmtDebug.fmt
  {N : Std.Usize} :
  ssz.SszBitlist N → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::stf::{impl core::fmt::Debug for mini_stf::stf::Error}::fmt]:
    Source: 'src/stf.rs', lines 22:9-22:14
    Visibility: public -/
axiom stf.Error.Insts.CoreFmtDebug.fmt
  :
  stf.Error → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::stf::{impl core::fmt::Display for mini_stf::stf::Error}::fmt]:
    Source: 'src/stf.rs', lines 22:16-22:32
    Visibility: public -/
axiom stf.Error.Insts.CoreFmtDisplay.fmt
  :
  stf.Error → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::H256}::fmt]:
    Source: 'src/tipos.rs', lines 23:9-23:14
    Visibility: public -/
axiom tipos.H256.Insts.CoreFmtDebug.fmt
  :
  tipos.H256 → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Display for mini_stf::tipos::H256}::fmt]:
    Source: 'src/tipos.rs', lines 31:4-37:5
    Visibility: public -/
axiom tipos.H256.Insts.CoreFmtDisplay.fmt
  :
  tipos.H256 → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Display for mini_stf::tipos::ShortRoot<'_0>}::fmt]:
    Source: 'src/tipos.rs', lines 44:4-49:5
    Visibility: public -/
axiom tipos.ShortRoot.Insts.CoreFmtDisplay.fmt
  :
  tipos.ShortRoot → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::Checkpoint}::fmt]:
    Source: 'src/tipos.rs', lines 146:9-146:14
    Visibility: public -/
axiom tipos.Checkpoint.Insts.CoreFmtDebug.fmt
  :
  tipos.Checkpoint → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::AttestationData}::fmt]:
    Source: 'src/tipos.rs', lines 159:9-159:14
    Visibility: public -/
axiom tipos.AttestationData.Insts.CoreFmtDebug.fmt
  :
  tipos.AttestationData → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::AggregatedAttestation}::fmt]:
    Source: 'src/tipos.rs', lines 194:9-194:14
    Visibility: public -/
axiom tipos.AggregatedAttestation.Insts.CoreFmtDebug.fmt
  :
  tipos.AggregatedAttestation → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::BlockHeader}::fmt]:
    Source: 'src/tipos.rs', lines 213:9-213:14
    Visibility: public -/
axiom tipos.BlockHeader.Insts.CoreFmtDebug.fmt
  :
  tipos.BlockHeader → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::BlockBody}::fmt]:
    Source: 'src/tipos.rs', lines 240:9-240:14
    Visibility: public -/
axiom tipos.BlockBody.Insts.CoreFmtDebug.fmt
  :
  tipos.BlockBody → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::Block}::fmt]:
    Source: 'src/tipos.rs', lines 265:9-265:14
    Visibility: public -/
axiom tipos.Block.Insts.CoreFmtDebug.fmt
  :
  tipos.Block → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::Validator}::fmt]:
    Source: 'src/tipos.rs', lines 333:9-333:14
    Visibility: public -/
axiom tipos.Validator.Insts.CoreFmtDebug.fmt
  :
  tipos.Validator → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::StateConfig}::fmt]:
    Source: 'src/tipos.rs', lines 344:9-344:14
    Visibility: public -/
axiom tipos.StateConfig.Insts.CoreFmtDebug.fmt
  :
  tipos.StateConfig → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::State}::fmt]:
    Source: 'src/tipos.rs', lines 350:9-350:14
    Visibility: public -/
axiom tipos.State.Insts.CoreFmtDebug.fmt
  :
  tipos.State → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)



-- ---------------------------------------------------------------------------
-- Modelos a mano de funciones de `core` que `CoreModels` no cubre.
--
-- Aeneas las NOMBRA en el codigo generado sin avisar nada; la extraccion sale
-- limpia y el agujero recien aparece en `lake build`:
--   error: Unknown identifier `core.num.U64.isqrt`
--
-- Cada una de estas es un SUPUESTO. Todo teorema que pase por ellas vale solo
-- si el supuesto describe bien lo que hace el Rust.
-- ---------------------------------------------------------------------------

namespace core.bool.Bool

/-- `bool::then(self, f)`: `Some(f())` si es true, `None` si no.

    Era un axioma; desde el 17 nov 2026 es una definicion. Misma razon que
    `isqrt` y `mem::take`: de un axioma no se sabe nada, ni siquiera que
    devuelve. `current_proposer` es `(n > 0).then(|| slot % n)`, y con `then`
    axiomatico no se podia demostrar ni que no entra en panico ni que devuelve
    el resto de la division.

    EL SUPUESTO QUE QUEDA, ahora explicito: que `bool::then` de Rust llama al
    closure solo cuando el booleano es `true` y envuelve el resultado en
    `Some`. Es lo que dice su documentacion. -/
def «then» {F T : Type} (inst : core.ops.function.FnOnce F Unit T)
    (b : Bool) (f : F) : RustM (core.option.Option T) :=
  if b then do
    let t ← inst.call_once f ()
    ok (core.option.Option.Some t)
  else ok core.option.Option.None

end core.bool.Bool

namespace core.mem

/-- `mem::take(&mut x)`: devuelve el valor viejo y deja el default en su lugar.
    El par es (lo que saco, como queda).

    Era un axioma; desde el 15 nov 2026 es una definicion. La razon es la
    misma que con `isqrt`: de un axioma no se sabe nada, ni siquiera que lo
    que devuelve tiene que ver con lo que recibe. `process_block_header` saca
    `historical_block_hashes` del estado con `mem::take`, le agrega la raiz
    del padre y lo vuelve a guardar; con `take` axiomatico era imposible
    demostrar que el historial viejo sigue ahi, que es lo que necesita ST-7.

    EL SUPUESTO QUE QUEDA, ahora explicito: que `mem::take` de Rust devuelve
    el valor que habia y deja `Default::default()`. Es lo que dice su
    documentacion. -/
def take {T : Type} (inst : core.default.Default T) (x : T) : RustM (T × T) := do
  let d ← inst.default
  ok (x, d)

end core.mem

namespace core.num.U64

/-- `u64::isqrt()`: raiz cuadrada entera truncada.

    Era un axioma; desde el 30 oct 2026 es una definicion sobre `Nat.sqrt`.
    La diferencia importa: de un axioma no se sabe NADA, ni siquiera que
    devuelve lo mismo para el mismo argumento, asi que todo teorema sobre
    `slot_is_justifiable_after` era imposible, no dificil.

    La cota sale sola: `Nat.sqrt n <= n`, y si `x` entra en 64 bits su raiz
    tambien.

    EL SUPUESTO QUE QUEDA, y ahora es explicito y chequeable: que el
    `u64::isqrt` de Rust calcula lo mismo que `Nat.sqrt` de Lean. La
    documentacion de Rust dice "raiz cuadrada entera truncada", que es
    exactamente `Nat.sqrt`. Eso lo estamos creyendo, no demostrando -- pero
    ahora se sabe que se esta creyendo. -/
def isqrt (x : Std.U64) : RustM Std.U64 :=
  ok (Aeneas.Std.U64.ofNatCore (Nat.sqrt x.val)
        (Nat.lt_of_le_of_lt (Nat.sqrt_le_self x.val) x.hBounds))

end core.num.U64

namespace core.Array.Insts.CoreCmpOrd

/-- Comparacion lexicografica de dos listas, usando el `cmp` del elemento:
    se comparan de a pares desde el principio y decide el primer par
    distinto. -/
def cmp_listas {T : Type} (inst : core.cmp.Ord T) :
    List T → List T → RustM core.cmp.Ordering
  | [], [] => ok core.cmp.Ordering.Equal
  | [], _ :: _ => ok core.cmp.Ordering.Less
  | _ :: _, [] => ok core.cmp.Ordering.Greater
  | x :: xs, y :: ys => do
      let o ← inst.cmp x y
      match o with
      | core.cmp.Ordering.Equal => cmp_listas inst xs ys
      | _ => ok o

/-- El `Ord` de `[T; N]`, orden lexicografico.

    ESTO ERA UN AXIOMA hasta el 19 nov 2026, y ahora es una definicion. Es
    la cuarta afirmacion de modelado del paquete, despues de `isqrt`,
    `mem::take` y `bool::then`.

    Por que. El ordenamiento de raices compara dos `H256` con `<`, y `H256`
    es `[u8; 32]`. Con esto como firma sin contenido no se podia demostrar
    ni que la comparacion devuelve, y esa era una hipotesis de
    `serialize_justifications`, `process_attestations`, `process_block` y
    `state_transition`.

    Que se esta creyendo. Que el `Ord` de un array en Rust es el orden
    lexicografico de sus elementos. Es lo que dice la documentacion de
    `core` ("implements comparison of arrays lexicographically"). Dos
    arrays de un mismo tipo `[T; N]` miden lo mismo, asi que los dos casos
    de largo distinto de `cmp_listas` no se alcanzan nunca. -/
def cmp {T : Type} {N : Std.Usize} (inst : core.cmp.Ord T)
    (a b : Array T N) : RustM core.cmp.Ordering :=
  cmp_listas inst a.val b.val

end core.Array.Insts.CoreCmpOrd

namespace core.Array.Insts.CoreHashHash

/-- El `Hash` de `[T; N]`. -/
axiom hash {T H : Type} {N : Std.Usize}
  (instT : core.hash.Hash T) (instH : core.hash.Hasher H) :
  Array T N -> H -> RustM H

end core.Array.Insts.CoreHashHash

-- ---------------------------------------------------------------------------
-- Las tres operaciones de `HashMap` que usa `root_to_slot`.
--
-- `root_to_slot` sigue siendo un `HashMap` a proposito: se construye con hasta
-- HISTORICAL_ROOTS_LIMIT entradas y solo se consulta con `get`, nunca se
-- recorre. Cambiarlo por una lista de pares lo volveria cuadratico.
--
-- ERAN AXIOMAS hasta el 19 nov 2026. Ahora `new`, `get` e `insert` son
-- definiciones sobre la lista de pares de TypesExternal.lean, y `Borrow` es
-- una estructura con su funcion `borrow`. Es la quinta afirmacion de
-- modelado del paquete, y la mas grande.
--
-- Por que. Que las tres devuelvan era una hipotesis de `try_finalize`,
-- `process_attestations`, `process_block` y `state_transition`, y como
-- firmas sin contenido no se podia demostrar.
--
-- Que se esta creyendo. Que un `HashMap` se comporta como una lista de pares
-- sin claves repetidas: `get` devuelve el valor de la clave igual a la que se
-- pide, e `insert` reemplaza el valor si la clave ya estaba y la agrega si
-- no. Eso es lo que dice su documentacion, y vale bajo el contrato que
-- `HashMap` le pide a sus claves: que dos claves iguales tengan el mismo
-- hash. El modelo NO mira el hash: compara con `Eq` y nada mas.
--
-- Lo que sigue sin contenido: `BuildHasher`, el hasher por defecto y el
-- `hash` de un array. Son argumentos que el modelo recibe y no usa.
-- ---------------------------------------------------------------------------

-- `core.hash.BuildHasher` tampoco esta en CoreModels: de `core.hash` solo
-- estan `Hash` y `Hasher`. Alcanza con que el tipo exista -- es un argumento
-- de instancia que nadie mira.
namespace core.hash

axiom BuildHasher (S : Type) : Type

end core.hash

namespace core.borrow

/-- El trait `Borrow`: de un `K` se saca un `Q` prestado. -/
structure Borrow (Q K : Type) where
  borrow : K → RustM Q

/-- Todo tipo se presta a si mismo. -/
def Borrow.Blanket (T : Type) : Borrow T T := { borrow := fun x => ok x }

end core.borrow

namespace std.hash.random

axiom RandomState.Insts.CoreHashBuildHasherDefaultHasher :
  core.hash.BuildHasher RandomState

end std.hash.random

namespace std.collections.hash.map

/-- Un mapa nuevo esta vacio. -/
def HashMapKVRandomStateGlobal.new (K V : Type) :
    RustM (HashMap K V std.hash.random.RandomState alloc.alloc.Global) :=
  ok { entradas := [] }

/-- Buscar una clave en la lista de pares: el valor del primer par cuya
    clave, prestada, es igual a la que se pide. -/
def HashMap.buscar {K V Q : Type} (instBorrow : core.borrow.Borrow Q K)
    (instEqQ : core.cmp.Eq Q) :
    List (K × V) → Q → RustM (core.option.Option V)
  | [], _ => ok core.option.Option.None
  | (k, v) :: resto, q => do
      let kq ← instBorrow.borrow k
      let igual ← instEqQ.PartialEqInst.eq kq q
      if igual then ok (core.option.Option.Some v)
      else HashMap.buscar instBorrow instEqQ resto q

def HashMap.get {K V S A Q : Type}
    (instEqK : core.cmp.Eq K) (instHashK : core.hash.Hash K)
    (instBH : core.hash.BuildHasher S)
    (instBorrow : core.borrow.Borrow Q K)
    (instHashQ : core.hash.Hash Q) (instEqQ : core.cmp.Eq Q)
    (m : HashMap K V S A) (q : Q) : RustM (core.option.Option V) :=
  HashMap.buscar instBorrow instEqQ m.entradas q

/-- Poner un par en la lista: si la clave ya estaba se reemplaza el valor y
    se devuelve el viejo; si no, se agrega al final y se devuelve `None`. -/
def HashMap.poner {K V : Type} (instEqK : core.cmp.Eq K) :
    List (K × V) → K → V → RustM ((core.option.Option V) × List (K × V))
  | [], k, v => ok (core.option.Option.None, [(k, v)])
  | (k', v') :: resto, k, v => do
      let igual ← instEqK.PartialEqInst.eq k' k
      if igual then ok (core.option.Option.Some v', (k', v) :: resto)
      else do
        let (viejo, resto') ← HashMap.poner instEqK resto k v
        ok (viejo, (k', v') :: resto')

def HashMap.insert {K V S A : Type}
    (instEqK : core.cmp.Eq K) (instHashK : core.hash.Hash K)
    (instBH : core.hash.BuildHasher S)
    (m : HashMap K V S A) (k : K) (v : V) :
    RustM ((core.option.Option V) × HashMap K V S A) := do
  let (viejo, entradas) ← HashMap.poner instEqK m.entradas k v
  ok (viejo, { entradas := entradas })

end std.collections.hash.map
