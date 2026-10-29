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

/-- [mini_stf::stf::process_attestations]:
    Source: 'src/stf.rs', lines 251:0-413:1 -/
axiom stf.process_attestations
  :
  tipos.State → ssz.SszList tipos.AggregatedAttestation 4096#usize → RustM
    ((core.result.Result Unit stf.Error) × tipos.State)

/-- [mini_stf::stf::serialize_justifications]:
    Source: 'src/stf.rs', lines 541:0-569:1 -/
axiom stf.serialize_justifications
  :
  tipos.State → std.collections.hash.map.HashMap tipos.H256 (alloc.vec.Vec
    Bool) std.hash.random.RandomState alloc.alloc.Global → Std.Usize →
    RustM tipos.State

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

/-- `u64::isqrt()`: raiz cuadrada entera.

    ATENCION: esto es un axioma, no una definicion. `slot_is_justifiable_after`
    lo usa para detectar cuadrados perfectos, asi que cualquier teorema sobre
    esa funcion es vacio hasta que esto se reemplace por una definicion real
    sobre `Nat.sqrt`. Es el primer supuesto que hay que cerrar. -/
axiom isqrt : Std.U64 -> RustM Std.U64

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
