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
    Source: 'src/stf.rs', lines 17:9-17:14
    Visibility: public -/
axiom stf.Error.Insts.CoreFmtDebug.fmt
  :
  stf.Error → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::stf::{impl core::fmt::Display for mini_stf::stf::Error}::fmt]:
    Source: 'src/stf.rs', lines 17:16-17:32
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
    Source: 'src/tipos.rs', lines 76:9-76:14
    Visibility: public -/
axiom tipos.Checkpoint.Insts.CoreFmtDebug.fmt
  :
  tipos.Checkpoint → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::AttestationData}::fmt]:
    Source: 'src/tipos.rs', lines 89:9-89:14
    Visibility: public -/
axiom tipos.AttestationData.Insts.CoreFmtDebug.fmt
  :
  tipos.AttestationData → core.fmt.Formatter → RustM ((core.result.Result
    Unit core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::AggregatedAttestation}::fmt]:
    Source: 'src/tipos.rs', lines 119:9-119:14
    Visibility: public -/
axiom tipos.AggregatedAttestation.Insts.CoreFmtDebug.fmt
  :
  tipos.AggregatedAttestation → core.fmt.Formatter → RustM
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::BlockHeader}::fmt]:
    Source: 'src/tipos.rs', lines 138:9-138:14
    Visibility: public -/
axiom tipos.BlockHeader.Insts.CoreFmtDebug.fmt
  :
  tipos.BlockHeader → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::BlockBody}::fmt]:
    Source: 'src/tipos.rs', lines 159:9-159:14
    Visibility: public -/
axiom tipos.BlockBody.Insts.CoreFmtDebug.fmt
  :
  tipos.BlockBody → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::Block}::fmt]:
    Source: 'src/tipos.rs', lines 172:9-172:14
    Visibility: public -/
axiom tipos.Block.Insts.CoreFmtDebug.fmt
  :
  tipos.Block → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::Validator}::fmt]:
    Source: 'src/tipos.rs', lines 234:9-234:14
    Visibility: public -/
axiom tipos.Validator.Insts.CoreFmtDebug.fmt
  :
  tipos.Validator → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::StateConfig}::fmt]:
    Source: 'src/tipos.rs', lines 245:9-245:14
    Visibility: public -/
axiom tipos.StateConfig.Insts.CoreFmtDebug.fmt
  :
  tipos.StateConfig → core.fmt.Formatter → RustM ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [mini_stf::tipos::{impl core::fmt::Debug for mini_stf::tipos::State}::fmt]:
    Source: 'src/tipos.rs', lines 251:9-251:14
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

/-- `bool::then(self, f)`: `Some(f())` si es true, `None` si no. -/
axiom «then» {F T : Type} (inst : core.ops.function.FnOnce F Unit T) :
  Bool -> F -> RustM (core.option.Option T)

end core.bool.Bool

namespace core.mem

/-- `mem::take(&mut x)`: devuelve el valor viejo y deja el default en su lugar.
    El par es (lo que saco, como queda). -/
axiom take {T : Type} (inst : core.default.Default T) : T -> RustM (T × T)

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

/-- El `Ord` de `[T; N]`, orden lexicografico. -/
axiom cmp {T : Type} {N : Std.Usize} (inst : core.cmp.Ord T) :
  Array T N -> Array T N -> RustM core.cmp.Ordering

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
-- Quedan como AXIOMAS. Para `ST-3` no molesta: esa propiedad habla de
-- `latest_justified` y `latest_finalized`, y `root_to_slot` solo interviene en
-- la poda de `justifications`. Si alguna vez hace falta razonar sobre el mapa,
-- hay que reemplazarlos por definiciones sobre la lista de pares que ya
-- declaramos en TypesExternal.
-- ---------------------------------------------------------------------------

-- `core.hash.BuildHasher` tampoco esta en CoreModels: de `core.hash` solo
-- estan `Hash` y `Hasher`. Alcanza con que el tipo exista -- es un argumento
-- de instancia que nadie mira.
namespace core.hash

axiom BuildHasher (S : Type) : Type

end core.hash

namespace core.borrow

axiom Borrow (Q K : Type) : Type

axiom Borrow.Blanket (T : Type) : Borrow T T

end core.borrow

namespace std.hash.random

axiom RandomState.Insts.CoreHashBuildHasherDefaultHasher :
  core.hash.BuildHasher RandomState

end std.hash.random

namespace std.collections.hash.map

axiom HashMapKVRandomStateGlobal.new (K V : Type) :
  RustM (HashMap K V std.hash.random.RandomState alloc.alloc.Global)

axiom HashMap.get {K V S A Q : Type}
  (instEqK : core.cmp.Eq K) (instHashK : core.hash.Hash K)
  (instBH : core.hash.BuildHasher S)
  (instBorrow : core.borrow.Borrow Q K)
  (instHashQ : core.hash.Hash Q) (instEqQ : core.cmp.Eq Q) :
  HashMap K V S A -> Q -> RustM (core.option.Option V)

axiom HashMap.insert {K V S A : Type}
  (instEqK : core.cmp.Eq K) (instHashK : core.hash.Hash K)
  (instBH : core.hash.BuildHasher S) :
  HashMap K V S A -> K -> V -> RustM ((core.option.Option V) × HashMap K V S A)

end std.collections.hash.map
