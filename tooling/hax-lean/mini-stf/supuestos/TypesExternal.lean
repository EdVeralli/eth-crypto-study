-- [mini_stf]: external types.
-- Seeded by hax from Extraction/TypesExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
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


-- ---------------------------------------------------------------------------
-- Modelos a mano de los tipos de `std` que Aeneas nombra pero no define.
--
-- `CoreModels` trae modelos de las colecciones de `core` y `alloc`, pero NO de
-- `HashMap`. Aparece en las firmas generadas y, sin esto, el proyecto no tipa:
--   error: Unknown identifier `std.collections.hash.map.HashMap`
-- ---------------------------------------------------------------------------

namespace std.hash.random

/-- El generador de semillas de `HashMap`. Ningun teorema lo va a mirar. -/
structure RandomState where
  semilla : Nat

end std.hash.random

namespace std.collections.hash.map

/-- `HashMap<K, V, S, A>` como lista de pares.
    Alcanza para que tipen las firmas. Si despues hace falta recuperar
    `try_finalize`, `get` y `retain` se definen sobre esto. -/
structure HashMap (K V S A : Type) where
  entradas : List (K × V)

end std.collections.hash.map
