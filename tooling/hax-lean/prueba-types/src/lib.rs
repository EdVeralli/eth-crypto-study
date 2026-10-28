//! Prueba de factibilidad: paso 1.
//!
//! No hace nada util. Su unico trabajo es TOCAR los tipos `State` y `Block`
//! de ethlambda para obligar a Charon y Aeneas a traerlos, junto con todo lo
//! que ellos arrastran (SSZ, sha2, serde).
//!
//! Lo que se mide no es el resultado de estas funciones: es si la extraccion
//! escribe archivos o se cae, y con que error.
//!
//! Corrida:   cargo hax into lean
//!
//! Como leer el resultado:
//!   - escribe Funs.lean y Types.lean  -> el camino B existe
//!   - no escribe nada                 -> el error nombra la dependencia que
//!                                        lo traba; cualquier cosa que toque
//!                                        State necesita tipos a mano (camino C)
//!   - escribe pero con `sorry`        -> los tipos pasan, los cuerpos no

use ethlambda_types::{block::Block, state::State};

/// Lee un campo escalar del estado.
pub fn slot_del_estado(state: &State) -> u64 {
    state.slot
}

/// Lee un campo escalar del bloque.
pub fn slot_del_bloque(block: &Block) -> u64 {
    block.slot
}

/// Compara los dos: obliga a que ambos tipos entren en la misma funcion.
pub fn el_bloque_avanza(state: &State, block: &Block) -> bool {
    block.slot > state.slot
}

/// Toca un campo compuesto, no solo un u64: el checkpoint finalizado.
pub fn slot_finalizado(state: &State) -> u64 {
    state.latest_finalized.slot
}
