// CAMBIADO: ya no hace falta `HashSet` -- el conteo de datos distintos va con
// dos loops. `HashMap` se queda: `root_to_slot` lo sigue usando, y solo con
// `get` e `insert`, que no llevan closures.
use std::collections::HashMap;

// CAMBIADO: los tipos vienen de este crate en vez de `ethlambda_types`.
use crate::tipos::{
    AggregatedAttestations, AggregationBits, AttestationData, Block, BlockHeader, Checkpoint,
    H256, HashTreeRoot as _, JustificationRoots, JustificationValidators, ShortRoot, State,
    HISTORICAL_ROOTS_LIMIT, MAX_ATTESTATIONS_DATA,
};
// CAMBIADO: `tracing` y `metrics` son stubs sin efecto, definidos en este crate.
use crate::stubs::{info_stub as info, warn_stub as warn};
// CAMBIADO: `justifications` dejo de ser un HashMap. Ver src/mapa.rs.
use crate::mapa::MapaVotos;
use crate::{justified_slots_ops, stubs::metrics};

// QUITADO: `pub mod beacon;` (otra cadena de bloques, 47.160 lineas, no es la STF
// de lean) y las declaraciones de `justified_slots_ops` y `metrics`, que en este
// crate viven en la raiz.

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("target slot {target_slot} is in the past (current is {current_slot})")]
    StateSlotIsNewer { target_slot: u64, current_slot: u64 },
    #[error("advanced state slot {state_slot} is different from block slot {block_slot}")]
    SlotMismatch { state_slot: u64, block_slot: u64 },
    #[error("parent slot {parent_slot} is newer than block slot {block_slot}")]
    ParentSlotIsNewer { parent_slot: u64, block_slot: u64 },
    #[error("invalid proposer: expected {expected}, found {found}")]
    InvalidProposer { expected: u64, found: u64 },
    #[error("parent root mismatch: expected {expected}, found {found}")]
    InvalidParent { expected: H256, found: H256 },
    #[error("no validators in state")]
    NoValidators,
    #[error("state root mismatch: expected {expected}, computed {computed}")]
    StateRootMismatch { expected: H256, computed: H256 },
    #[error("slot gap {gap} would exceed historical roots limit (current: {current}, max: {max})")]
    SlotGapTooLarge {
        gap: usize,
        current: usize,
        max: usize,
    },
    #[error("zero hash found in justifications_roots")]
    ZeroHashInJustificationRoots,
    #[error(
        "justification vote list length {actual} does not equal tracked-root count times validator count {expected}"
    )]
    JustificationVotesLengthMismatch { expected: usize, actual: usize },
    #[error("aggregated attestation has no participants")]
    EmptyAggregationBits,
    #[error("aggregation bit set at index {index} beyond validator count {validator_count}")]
    AggregationBitsOutOfBounds {
        index: usize,
        validator_count: usize,
    },
    #[error(
        "justified slot {slot} is outside the tracked range (finalized_boundary={finalized_slot}, tracked_length={tracked_length})"
    )]
    JustifiedSlotOutOfRange {
        slot: u64,
        finalized_slot: u64,
        tracked_length: usize,
    },
    #[error("block carries {count} distinct AttestationData entries; maximum is {max}")]
    TooManyAttestationData { count: usize, max: usize },
}

/// Transition the given pre-state to the block's post-state.
///
/// Similar to the spec's `State.state_transition`: https://github.com/leanEthereum/leanSpec/blob/bf0f606a75095cf1853529bc770516b1464d9716/src/lean_spec/subspecs/containers/state/state.py#L569
pub fn state_transition(state: &mut State, block: &Block) -> Result<(), Error> {
    let _timing = metrics::time_state_transition();

    process_slots(state, block.slot)?;
    process_block(state, block)?;

    // Uncomment for debugging state transitions
    // std::fs::write(
    //     &format!("block_slot_{}.ssz", state.slot),
    //     block.as_ssz_bytes(),
    // )
    // .unwrap();
    // std::fs::write(
    //     &format!("post_state_slot_{}.ssz", state.slot),
    //     state.as_ssz_bytes(),
    // )
    // .unwrap();

    let computed_state_root = state.hash_tree_root();
    if block.state_root != computed_state_root {
        return Err(Error::StateRootMismatch {
            expected: block.state_root,
            computed: computed_state_root,
        });
    }
    Ok(())
}

/// Advance the state through empty slots up to, but not including, target_slot.
///
/// The spec (`state.py` process_slots) iterates slot-by-slot in a while loop.
/// We jump directly to target_slot instead, which is equivalent because:
///
/// 1. The state root is only cached on the first iteration (when state_root == ZERO).
///    After that, subsequent iterations only increment the slot counter.
/// 2. The hash is computed from the same state in both approaches: slot = current,
///    state_root = ZERO (the check happens before the slot assignment).
/// 3. No other state fields are modified in the spec's loop body.
///
/// If the spec ever adds per-slot side effects, this must be revisited.
pub fn process_slots(state: &mut State, target_slot: u64) -> Result<(), Error> {
    let _timing = metrics::time_slots_processing();

    if state.slot >= target_slot {
        return Err(Error::StateSlotIsNewer {
            target_slot,
            current_slot: state.slot,
        });
    }
    if state.latest_block_header.state_root == H256::ZERO {
        state.latest_block_header.state_root = state.hash_tree_root();
    }
    let slots_processed = target_slot - state.slot;
    state.slot = target_slot;
    metrics::inc_slots_processed(slots_processed);
    Ok(())
}

/// Apply full block processing including header and body.
pub fn process_block(state: &mut State, block: &Block) -> Result<(), Error> {
    let _timing = metrics::time_block_processing();

    process_block_header(state, block)?;
    process_attestations(state, &block.body.attestations)?;

    Ok(())
}

/// Validate the block header and update header-linked state.
fn process_block_header(state: &mut State, block: &Block) -> Result<(), Error> {
    let parent_header = &state.latest_block_header;

    // Validation

    // TODO: this is redundant if we assume process_slots has been called
    if block.slot != state.slot {
        return Err(Error::SlotMismatch {
            state_slot: state.slot,
            block_slot: block.slot,
        });
    }
    if block.slot <= parent_header.slot {
        return Err(Error::ParentSlotIsNewer {
            parent_slot: parent_header.slot,
            block_slot: block.slot,
        });
    }
    let num_validators = state.validators.len() as u64;
    let expected_proposer =
        current_proposer(block.slot, num_validators).ok_or(Error::NoValidators)?;
    if block.proposer_index != expected_proposer {
        return Err(Error::InvalidProposer {
            expected: expected_proposer,
            found: block.proposer_index,
        });
    }
    // TODO: this is redundant in normal operation
    let parent_root = parent_header.hash_tree_root();
    if block.parent_root != parent_root {
        return Err(Error::InvalidParent {
            expected: parent_root,
            found: block.parent_root,
        });
    }

    // State Updates

    // Special case: first block after genesis.
    // TODO: this could be moved to genesis state initialization
    let is_genesis_parent = parent_header.slot == 0;
    if is_genesis_parent {
        state.latest_justified.root = parent_root;
        state.latest_finalized.root = parent_root;
    }

    // Guard: reject blocks whose slot gap would overflow historical_block_hashes.
    // The spec relies on the SSZ list limit (HISTORICAL_ROOTS_LIMIT) to enforce
    // this implicitly during serialization. We check explicitly before allocating
    // to prevent OOM from a crafted block with a large slot gap.
    let num_empty_slots = (block.slot - parent_header.slot - 1) as usize;
    let current_len = state.historical_block_hashes.len();
    let new_total = current_len + 1 + num_empty_slots; // +1 for parent_root push
    if new_total > HISTORICAL_ROOTS_LIMIT {
        return Err(Error::SlotGapTooLarge {
            gap: num_empty_slots,
            current: current_len,
            max: HISTORICAL_ROOTS_LIMIT,
        });
    }

    let mut historical_block_hashes: Vec<_> =
        std::mem::take(&mut state.historical_block_hashes).into_inner();
    historical_block_hashes.push(parent_root);
    // CAMBIADO respecto del original, que decia:
    //     historical_block_hashes.extend(std::iter::repeat_n(H256::ZERO, num_empty_slots));
    // `repeat_n` y `Vec::extend` no estan en CoreModels y el proyecto Lean no
    // tipa. El loop hace lo mismo.
    for _ in 0..num_empty_slots {
        historical_block_hashes.push(H256::ZERO);
    }

    state.historical_block_hashes = historical_block_hashes
        .try_into()
        .expect("pre-validated: total does not exceed limit");

    // Extend justified_slots to cover slots up to (block.slot - 1)
    //
    // The storage is relative to the finalized boundary.
    // The current block's slot is not materialized until processing completes,
    // so we only extend up to the last materialized slot.
    let last_materialized_slot = block.slot - 1;
    justified_slots_ops::extend_to_slot(
        &mut state.justified_slots,
        state.latest_finalized.slot,
        last_materialized_slot,
    );

    let new_header = BlockHeader {
        slot: block.slot,
        proposer_index: block.proposer_index,
        parent_root: block.parent_root,
        body_root: block.body.hash_tree_root(),
        // Zeroed out until local state root computation.
        // This is later filled with the state root after all processing is done.
        state_root: H256::ZERO,
    };
    state.latest_block_header = new_header;
    Ok(())
}

/// Determine the proposer for a given slot using round-robin selection.
///
/// Returns `None` when `num_validators` is zero. The spec (validator.py L25)
/// does `slot % num_validators` without checking for zero, which would panic
/// on division by zero. This can't happen in practice (genesis always has at
/// least one validator), but we guard explicitly to avoid panics from crafted
/// inputs.
fn current_proposer(slot: u64, num_validators: u64) -> Option<u64> {
    (num_validators > 0).then(|| slot % num_validators)
}

/// Check if a validator is the proposer for a given slot.
///
/// Proposer selection uses simple round-robin: `slot % num_validators`.
pub fn is_proposer(validator_index: u64, slot: u64, num_validators: u64) -> bool {
    current_proposer(slot, num_validators) == Some(validator_index)
}

// ---------------------------------------------------------------------------
// Helpers de la reescritura. NO ESTAN EN EL ORIGINAL.
//
// Cada uno existe por una de dos razones:
//
//   1. Reemplaza un iterador con closure, que Aeneas no traduce.
//   2. Saca un loop que estaba adentro de otro. Un loop anidado falla con
//      "Could not match the contexts"; el mismo loop en una funcion aparte,
//      llamada desde el loop de afuera, traduce sin problema.
//
// Ninguno cambia el comportamiento. Los seis tests del original son la prueba.
// ---------------------------------------------------------------------------

/// Lecturas POR COPIA de las colecciones.
///
/// Existen por una regla que costo encontrar: ligar una referencia sacada de
/// una coleccion (un `Some(a)` de un `.get()`) adentro de un loop que ademas
/// muta otra coleccion hace fallar a Aeneas con "Internal error". Cada cosa
/// por separado pasa; las dos juntas no. Sacando la lectura a una funcion, la
/// referencia ya no se liga adentro del loop.
fn dato_en(atts: &AggregatedAttestations, i: usize) -> AttestationData {
    match atts.get(i) {
        Some(a) => a.data,
        None => AttestationData::default(),
    }
}

fn bits_largo_en(atts: &AggregatedAttestations, i: usize) -> usize {
    match atts.get(i) {
        Some(a) => a.aggregation_bits.len(),
        None => 0,
    }
}

fn bits_en_uno_en(atts: &AggregatedAttestations, i: usize) -> usize {
    match atts.get(i) {
        Some(a) => a.aggregation_bits.count_ones(),
        None => 0,
    }
}

fn bit_en(atts: &AggregatedAttestations, i: usize, j: usize) -> bool {
    match atts.get(i) {
        Some(a) => a.aggregation_bits.get(j) == Some(true),
        None => false,
    }
}

fn raiz_justificacion_en(roots: &JustificationRoots, i: usize) -> H256 {
    match roots.get(i) {
        Some(r) => *r,
        None => H256::ZERO,
    }
}

fn hash_historico_en(state: &State, slot: usize) -> Option<H256> {
    match state.historical_block_hashes.get(slot) {
        Some(r) => Some(*r),
        None => None,
    }
}

fn slot_de_raiz(m: &HashMap<H256, u64>, root: &H256) -> Option<u64> {
    match m.get(root) {
        Some(s) => Some(*s),
        None => None,
    }
}

fn raiz_de_lista(v: &Vec<H256>, i: usize) -> H256 {
    match v.get(i) {
        Some(x) => *x,
        None => H256::ZERO,
    }
}

/// `true` si el dato de la attestation `i` ya aparecio antes.
///
/// Reemplaza al `HashSet` del original. El loop vive aca y no en
/// `contar_datos_distintos` para no anidar.
fn dato_repetido_antes(attestations: &AggregatedAttestations, i: usize) -> bool {
    let actual = match attestations.get(i) {
        Some(a) => a.data,
        None => return false,
    };
    let mut repetido = false;
    for j in 0..i {
        match attestations.get(j) {
            Some(b) => {
                if b.data == actual {
                    repetido = true;
                }
            }
            None => {}
        }
    }
    repetido
}

/// Cuantos datos de attestation distintos trae el bloque.
fn contar_datos_distintos(attestations: &AggregatedAttestations) -> usize {
    let mut n = 0;
    for i in 0..attestations.len() {
        if !dato_repetido_antes(attestations, i) {
            n += 1;
        }
    }
    n
}

/// Reemplaza a `.iter().any(|root| root == &H256::ZERO)`.
fn hay_raiz_cero(roots: &JustificationRoots) -> bool {
    let mut hay = false;
    for i in 0..roots.len() {
        if raiz_justificacion_en(roots, i) == H256::ZERO {
            hay = true;
        }
    }
    hay
}

/// `n` votos en false. Reemplaza a `std::iter::repeat_n(false, n).collect()`.
fn votos_vacios(n: usize) -> Vec<bool> {
    let mut v: Vec<bool> = Vec::new();
    for _ in 0..n {
        v.push(false);
    }
    v
}

/// El segmento de votos de la raiz `i` dentro de la lista plana del estado.
fn votos_del_segmento(state: &State, i: usize, validator_count: usize) -> Vec<bool> {
    let mut v: Vec<bool> = Vec::new();
    for j in (i * validator_count)..((i + 1) * validator_count) {
        v.push(state.justifications_validators.get(j) == Some(true));
    }
    v
}

/// Desarma la lista plana del estado en el mapa de votos.
fn construir_mapa_de_votos(state: &State, validator_count: usize) -> MapaVotos {
    let mut m = MapaVotos::nuevo();
    for i in 0..state.justifications_roots.len() {
        let r = raiz_justificacion_en(&state.justifications_roots, i);
        m.poner_si_falta(r, votos_del_segmento(state, i, validator_count));
    }
    m
}

/// Mapea cada raiz a su slot mas reciente.
///
/// Sigue siendo un `HashMap`: se construye con hasta HISTORICAL_ROOTS_LIMIT
/// entradas y solo se consulta con `get`, nunca se recorre. El
/// `entry().and_modify().or_insert()` del original era un closure y quedo como
/// `get` mas `insert`.
fn construir_root_to_slot(state: &State) -> HashMap<H256, u64> {
    let mut m: HashMap<H256, u64> = HashMap::new();
    for slot in (state.latest_finalized.slot + 1)..state.historical_block_hashes.len() as u64 {
        match hash_historico_en(state, slot as usize) {
            Some(root) => {
                let nuevo = match slot_de_raiz(&m, &root) {
                    Some(x) => {
                        if x > slot {
                            x
                        } else {
                            slot
                        }
                    }
                    None => slot,
                };
                m.insert(root, nuevo);
            }
            None => {}
        }
    }
    m
}

/// El primer bit en true a partir de `desde`. Reemplaza al `.find()`.
fn primer_bit_fuera_de_rango(
    atts: &AggregatedAttestations,
    idx: usize,
    desde: usize,
) -> Option<usize> {
    let largo = bits_largo_en(atts, idx);
    let mut encontrado: Option<usize> = None;
    for i in desde..largo {
        if encontrado.is_none() && bit_en(atts, idx, i) {
            encontrado = Some(i);
        }
    }
    encontrado
}

/// Marca en el mapa que cada validador de la agregacion voto.
/// Reemplaza a `votes.iter_mut().enumerate().take(...)`.
fn marcar_votos(mapa: &mut MapaVotos, p: usize, atts: &AggregatedAttestations, idx: usize) {
    let largo = bits_largo_en(atts, idx);
    for validator_id in 0..largo {
        if bit_en(atts, idx, validator_id) {
            mapa.votar(p, validator_id);
        }
    }
}

/// Reemplaza a `(desde..hasta).any(|slot| slot_is_justifiable_after(...))`.
fn hay_slot_justificable(desde: u64, hasta: u64, finalized: u64) -> bool {
    let mut hay = false;
    for slot in desde..hasta {
        if slot_is_justifiable_after(slot, finalized) {
            hay = true;
        }
    }
    hay
}

/// Vuelca los votos de una raiz en la lista plana, a partir de `base`.
/// Reemplaza al `flat_map().enumerate().filter().for_each()`.
fn volcar_votos(
    destino: &mut JustificationValidators,
    origen: &MapaVotos,
    root: H256,
    base: usize,
) {
    match origen.posicion(&root) {
        Some(p) => {
            let n = origen.largo_votos(p);
            for k in 0..n {
                if origen.voto(p, k) {
                    destino
                        .set(base + k, true)
                        .expect("we just updated the capacity");
                }
            }
        }
        None => {}
    }
}

/// Apply attestations and update justification/finalization
/// according to the Lean Consensus 3SF-mini rules.
fn process_attestations(
    state: &mut State,
    attestations: &AggregatedAttestations,
) -> Result<(), Error> {
    let _timing = metrics::time_attestations_processing();

    // Cap the distinct attestation data a block may carry (leanSpec #536).
    //
    // CAMBIADO: el original usaba un `HashSet<&AttestationData>` construido con
    // `.iter().map().collect()`. Mismo resultado, contado con dos loops.
    let distintos = contar_datos_distintos(attestations);
    if distintos > MAX_ATTESTATIONS_DATA {
        return Err(Error::TooManyAttestationData {
            count: distintos,
            max: MAX_ATTESTATIONS_DATA,
        });
    }

    let validator_count = state.validators.len();

    // An empty registry leaves no segment width, so the flat layout cannot be
    // recovered.
    if validator_count == 0 {
        return Err(Error::NoValidators);
    }

    // The flat vote list must hold exactly one full validator segment per tracked
    // root (leanSpec #1178).
    let expected_vote_count = state.justifications_roots.len() * validator_count;
    let actual_vote_count = state.justifications_validators.len();
    if actual_vote_count != expected_vote_count {
        return Err(Error::JustificationVotesLengthMismatch {
            expected: expected_vote_count,
            actual: actual_vote_count,
        });
    }

    // The zero hash marks a skipped slot, never a real block (spec state.py L389).
    // CAMBIADO: era `.iter().any(...)`.
    if hay_raiz_cero(&state.justifications_roots) {
        return Err(Error::ZeroHashInJustificationRoots);
    }

    let mut attestations_processed: u64 = 0;
    // CAMBIADO: `justifications` es un MapaVotos, no un HashMap. Ver src/mapa.rs.
    let mut justifications = construir_mapa_de_votos(state, validator_count);
    let root_to_slot = construir_root_to_slot(state);

    // CAMBIADO: el `for attestation in attestations` va por indice, y los dos
    // `return` que estaban adentro del loop son ahora una variable de resultado
    // mas `break`. Aeneas falla con "Early returns inside of loops are not
    // supported yet". El `continue` se puede dejar.
    // CAMBIADO. En el original esto es `for attestation in attestations` con
    // dos `return` y un `continue` adentro. Aca va por indice y, sobre todo,
    // con UNA SOLA SALIDA: nada de `break` ni `continue`, todo guardado por
    // banderas.
    //
    // Por que. Aeneas no soporta "early returns inside of loops", asi que los
    // `return` tenian que irse igual. Pero convertirlos en `break` tampoco
    // alcanzo: un loop con cuatro salidas distintas (el final mas tres breaks)
    // lo hace fallar con "Could not match the contexts" -- no logra unificar
    // el estado de todas las ramas. Con una sola salida, todas las vueltas
    // tienen la misma forma.
    //
    // El comportamiento es el mismo: una vez que `fallo` tiene algo, las
    // vueltas que quedan no hacen nada, igual que si hubiera cortado.
    let mut fallo: Option<Error> = None;
    for idx in 0..attestations.len() {
        if fallo.is_none() {
            let datos = dato_en(attestations, idx);
            let bits_en_uno = bits_en_uno_en(attestations, idx);
            let source = datos.source;
            let target = datos.target;

            let valido = match is_valid_vote(state, &datos) {
                Ok(v) => v,
                Err(e) => {
                    fallo = Some(e);
                    false
                }
            };

            // The spec asserts that an aggregated attestation references at
            // least one validator; the failed assert invalidates the whole
            // block.
            if fallo.is_none() && valido && bits_en_uno == 0 {
                fallo = Some(Error::EmptyAggregationBits);
            }

            // A set bit beyond the validator set crashes the spec (IndexError)
            // and invalidates the whole block.
            if fallo.is_none() && valido {
                match primer_bit_fuera_de_rango(attestations, idx, validator_count) {
                    Some(index) => {
                        fallo = Some(Error::AggregationBitsOutOfBounds {
                            index,
                            validator_count,
                        });
                    }
                    None => {}
                }
            }

            if fallo.is_none() && valido {
                // Record the vote
                attestations_processed += 1;
                let p =
                    justifications.poner_si_falta(target.root, votos_vacios(validator_count));

                // Mark that each validator in this aggregation has voted.
                marcar_votos(&mut justifications, p, attestations, idx);

                // Check whether the vote count crosses the supermajority
                // threshold
                let vote_count = justifications.cuenta_votos(p);
                if 3 * vote_count >= 2 * validator_count {
                    // If the slot is higher, update the latest justified.
                    // CAMBIADO: era `std::cmp::max_by_key(a, b, |c| c.slot)`,
                    // que ante empate se queda con el SEGUNDO -- de ahi el `>=`.
                    if target.slot >= state.latest_justified.slot {
                        state.latest_justified = target;
                    }
                    justified_slots_ops::set_justified(
                        &mut state.justified_slots,
                        state.latest_finalized.slot,
                        target.slot,
                    );

                    let justified_slot = target.slot;
                    let threshold = (2 * validator_count).div_ceil(3);
                    info!(
                        justified_slot,
                        justified_root = %ShortRoot(&target.root.0),
                        vote_count,
                        threshold,
                        "Checkpoint justified"
                    );

                    // CAMBIADO: era `justifications.remove(&target.root)`.
                    justifications = justifications.sin(&target.root);

                    try_finalize(state, source, target, &mut justifications, &root_to_slot);
                }
            }
        }
    }

    // El original corta con `return Err(...)` adentro del loop, en tres
    // lugares: el `?` de `is_valid_vote`, `EmptyAggregationBits` y
    // `AggregationBitsOutOfBounds`. Aca no se puede: Aeneas rechaza los
    // early returns adentro de un loop, asi que el error se junta en
    // `fallo` y se propaga recien aca.
    //
    // Tiene que ser ANTES de `serialize_justifications`: el original, al
    // cortar adentro del loop, nunca llega a serializar.
    match fallo {
        Some(e) => return Err(e),
        None => {}
    }

    serialize_justifications(state, justifications, validator_count);
    metrics::inc_attestations_processed(attestations_processed);
    Ok(())
}

/// Returns whether an attestation should be counted for fork choice.
///
/// Checks (all must pass):
/// 1. Source is already justified
/// 2. Target is not yet justified
/// 3. Both checkpoints match the canonical chain at their slots (which also
///    rejects zero-hash source or target roots)
/// 4. Target slot > source slot
/// 5. Target slot is justifiable after the finalized slot
///
/// A failed check drops the vote and leaves the block valid, matching the
/// spec's `continue` semantics. The exception is a source or target slot past
/// the tracked justification window: that has no justification status to read
/// at all, so it invalidates the whole block via `JustifiedSlotOutOfRange`
/// (leanSpec #1023). After `process_block_header` the window covers up to
/// `block.slot - 1`, so this is exactly a vote whose source or target slot is
/// at or beyond the importing block's own slot.
fn is_valid_vote(state: &State, data: &AttestationData) -> Result<bool, Error> {
    let source = data.source;
    let target = data.target;

    // Check that the source is already justified
    if !justified_slots_ops::is_slot_justified(
        &state.justified_slots,
        state.latest_finalized.slot,
        source.slot,
    )? {
        return Ok(false);
    }

    // Ignore votes for targets that have already reached consensus
    if justified_slots_ops::is_slot_justified(
        &state.justified_slots,
        state.latest_finalized.slot,
        target.slot,
    )? {
        return Ok(false);
    }

    // Ensure the vote refers to blocks that actually exist on our chain;
    // also rejects zero-hash source or target inline.
    if !attestation_data_matches_chain(&state.historical_block_hashes, data) {
        return Ok(false);
    }

    // Ensure time flows forward
    if target.slot <= source.slot {
        return Ok(false);
    }

    // Ensure the target falls on a slot that can be justified after the finalized one.
    if !slot_is_justifiable_after(target.slot, state.latest_finalized.slot) {
        return Ok(false);
    }

    Ok(true)
}

/// Attempt to advance finalization from source to target.
///
/// Finalization advances only when the source lies past the old finalized point
/// and there are no justifiable slots between source.slot and target.slot
/// (exclusive). A source at or behind the finalized boundary is already final:
/// it may justify a newer target, but it must not re-finalize or scan below the
/// finalized boundary. When finalization advances, shifts the justified_slots
/// window and prunes stale justifications.
fn try_finalize(
    state: &mut State,
    source: Checkpoint,
    target: Checkpoint,
    justifications: &mut MapaVotos,
    root_to_slot: &HashMap<H256, u64>,
) {
    // A stale or boundary source is already finalized; advancing from it would
    // rewind the finalized checkpoint and scan slots below the boundary.
    if source.slot <= state.latest_finalized.slot {
        return;
    }

    // Consider whether finalization can advance.
    // CAMBIADO: era `((source.slot + 1)..target.slot).any(...)`.
    if hay_slot_justificable(source.slot + 1, target.slot, state.latest_finalized.slot) {
        metrics::inc_finalizations("error");
        return;
    }

    let old_finalized_slot = state.latest_finalized.slot;
    state.latest_finalized = source;
    metrics::inc_finalizations("success");

    let finalized_slot = source.slot;
    let previous_finalized = old_finalized_slot;
    let justified_slot = state.latest_justified.slot;
    info!(
        finalized_slot,
        finalized_root = %ShortRoot(&source.root.0),
        previous_finalized,
        justified_slot,
        "Checkpoint finalized"
    );

    // Shift window to drop finalized slots from the front
    let delta = (state.latest_finalized.slot - old_finalized_slot) as usize;
    justified_slots_ops::shift_window(&mut state.justified_slots, delta);

    // Prune justifications whose roots are at or below the finalized slot.
    // The spec asserts all roots must be in root_to_slot (state.py L560).
    // A missing root means its slot <= finalized_slot, so prune it.
    //
    // CAMBIADO: era `justifications.retain(|root, _| ...)`, un closure sobre un
    // HashMap. Ahora se decide afuera cuales quedan y despues se filtra.
    let mut conservar: Vec<bool> = Vec::new();
    for i in 0..justifications.largo() {
        let root = justifications.clave(i);
        let queda = match slot_de_raiz(root_to_slot, &root) {
            Some(slot) => slot > state.latest_finalized.slot,
            None => {
                warn!(
                    root = %ShortRoot(&root.0),
                    finalized_slot = state.latest_finalized.slot,
                    "Justification root missing from root_to_slot, pruning"
                );
                false
            }
        };
        conservar.push(queda);
    }
    let filtrado = justifications.filtrado(&conservar);
    *justifications = filtrado;
}

/// Convert the in-memory vote HashMap back into SSZ-compatible state fields.
///
/// Sorts roots for deterministic output, then flattens vote bitfields
/// into `state.justifications_roots` and `state.justifications_validators`.
fn serialize_justifications(
    state: &mut State,
    justifications: MapaVotos,
    validator_count: usize,
) {
    // Sorting ensures that every node produces identical state representation.
    // CAMBIADO: era `justifications.keys().cloned().collect()` mas `.sort()`.
    // El orden lo hace `claves_ordenadas`, con insercion escrita a mano.
    let justification_roots = justifications.claves_ordenadas();

    let mut justifications_validators =
        JustificationValidators::with_length(justification_roots.len() * validator_count)
            .expect("maximum validator justifications reached");

    // CAMBIADO: era `.iter().flat_map(...).enumerate().filter(...).for_each(...)`.
    // El loop interno vive en `volcar_votos` para no anidar.
    let mut base = 0usize;
    for i in 0..justification_roots.len() {
        let root = raiz_de_lista(&justification_roots, i);
        volcar_votos(&mut justifications_validators, &justifications, root, base);
        base += validator_count;
    }

    state.justifications_roots = justification_roots
        .try_into()
        .expect("justifications_roots limit exceeded");
    state.justifications_validators = justifications_validators;
}

/// Whether the source, target, and head checkpoints in `data` match the chain
/// at their slots.
///
/// Callers pass a chain view as it would appear after `process_block_header`
/// on the consuming block: covering `[0, block.slot - 1]` with `parent_root`
/// at the parent slot and `H256::ZERO` for empty slots between parent and the
/// candidate.
///
/// Checking `head` against the canonical view keeps counted votes internally
/// consistent: justification is keyed on `target.root`, so a sibling head must
/// not pair a canonical FFG vote with an LMD head on a non-canonical fork.
pub fn attestation_data_matches_chain(
    historical_block_hashes: &[H256],
    data: &AttestationData,
) -> bool {
    if data.source.root == H256::ZERO
        || data.target.root == H256::ZERO
        || data.head.root == H256::ZERO
    {
        return false;
    }
    let source_slot = data.source.slot as usize;
    let target_slot = data.target.slot as usize;
    let head_slot = data.head.slot as usize;
    if source_slot >= historical_block_hashes.len()
        || target_slot >= historical_block_hashes.len()
        || head_slot >= historical_block_hashes.len()
    {
        return false;
    }
    historical_block_hashes[source_slot] == data.source.root
        && historical_block_hashes[target_slot] == data.target.root
        && historical_block_hashes[head_slot] == data.head.root
}

/// Checks if the slot is a valid candidate for justification after a given finalized slot.
///
/// According to the 3SF-mini specification, a slot is justifiable if its
/// distance (`delta`) from the last finalized slot is:
///     1. Less than or equal to 5.
///     2. A perfect square (e.g., 9, 16, 25...).
///     3. A pronic number (of the form x^2 + x, e.g., 6, 12, 20...).
///
/// See https://github.com/ethereum/research/blob/c003fe1c1a785797e7b53e3cbf9569b989be6e93/3sf-mini/consensus.py#L52-L54
/// for the 3SF-mini reference.
///
/// For why we have unjustifiable slots, consider that in high-latency
/// scenarios, validators may vote for many different slots, making none of them
/// reach the supermajority threshold. By having unjustifiable slots, we can
/// funnel votes towards only some slots, increasing finalization chances.
pub fn slot_is_justifiable_after(slot: u64, finalized_slot: u64) -> bool {
    let Some(delta) = slot.checked_sub(finalized_slot) else {
        // Candidate slot must not be before finalized slot
        return false;
    };
    // Rule 1: The first 5 slots after finalization are always justifiable.
    //
    // Examples: delta = 0, 1, 2, 3, 4, 5
    delta <= 5
        // Rule 2: Slots at perfect square distances are justifiable.
        //
        // Examples: delta = 1, 4, 9, 16, 25, 36, 49, 64, ...
        // Check: integer square root squared equals delta
        || delta.isqrt().pow(2) == delta
        // Rule 3: Slots at pronic number distances are justifiable.
        //
        // Pronic numbers have the form n(n+1): 2, 6, 12, 20, 30, 42, 56, ...
        // Mathematical insight: For pronic delta = n(n+1), we have:
        //   4*delta + 1 = 4n(n+1) + 1 = (2n+1)^2
        // Check: 4*delta+1 is an odd perfect square
        || delta
            .checked_mul(4)
            .and_then(|v| v.checked_add(1))
            .is_some_and(|val| val.isqrt().pow(2) == val && val % 2 == 1)
}


// ---------------------------------------------------------------------------
// Los tests del original, copiados tal cual de
// lambdaclass/ethlambda, crates/blockchain/state_transition/src/lib.rs (MIT).
//
// Son la red de seguridad de la reescritura: si pasan antes y despues de
// convertir los iteradores en loops de indice, tenemos evidencia de que el
// comportamiento se preservo. No es una demostracion de equivalencia, pero es
// mucho mejor que una promesa.
//
// Lo unico cambiado son los `use`.
//
// OJO: `hash_tree_root` en este crate es un stub que devuelve H256::ZERO, asi
// que los tests que comparan raices pueden pasar o fallar por el motivo
// equivocado. Ver README.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    // CAMBIADO: los tipos y la lista vienen de este crate.
    use crate::ssz::SszList;
    use crate::tipos::{
        AggregatedAttestation, AggregationBits, AttestationData, BlockBody, Checkpoint, H256,
        HashTreeRoot as _, JustifiedSlots, State, StateConfig, Validator,
    };

    fn make_validators(n: usize) -> Vec<Validator> {
        (0..n)
            .map(|i| Validator {
                attestation_pubkey: [i as u8; 32],
                proposal_pubkey: [i as u8; 32],
                index: i as u64,
            })
            .collect()
    }

    fn make_bits(set: &[usize], len: usize) -> AggregationBits {
        let mut b = AggregationBits::with_length(len).unwrap();
        for &i in set {
            b.set(i, true).unwrap();
        }
        b
    }

    fn make_attestation(
        att_slot: u64,
        src: (u64, H256),
        tgt: (u64, H256),
        head: (u64, H256),
        bits_set: &[usize],
        bits_len: usize,
    ) -> AggregatedAttestation {
        AggregatedAttestation {
            aggregation_bits: make_bits(bits_set, bits_len),
            data: AttestationData {
                slot: att_slot,
                source: Checkpoint {
                    slot: src.0,
                    root: src.1,
                },
                target: Checkpoint {
                    slot: tgt.0,
                    root: tgt.1,
                },
                head: Checkpoint {
                    slot: head.0,
                    root: head.1,
                },
            },
        }
    }

    /// leanSpec #833: `attestation_data_matches_chain` must reject a vote whose
    /// head sits off the canonical chain, even when source and target are both
    /// canonical. Justification is keyed on `target.root`, so accepting a
    /// canonical FFG vote paired with a sibling LMD head would decouple the two.
    #[test]
    fn matches_chain_rejects_off_canonical_head() {
        let r1 = H256([1u8; 32]);
        let r2 = H256([2u8; 32]);
        let sibling = H256([0x99u8; 32]);

        // Canonical chain: slot 0 genesis (ZERO is fine for source here only if
        // non-zero; use explicit roots), slot 1 -> r1, slot 2 -> r2.
        let g = H256([7u8; 32]);
        let hashes: Vec<H256> = vec![g, r1, r2];

        // source=(0,g), target=(1,r1) both canonical; head=(2, sibling) is not.
        let off_head = AttestationData {
            slot: 2,
            source: Checkpoint { slot: 0, root: g },
            target: Checkpoint { slot: 1, root: r1 },
            head: Checkpoint {
                slot: 2,
                root: sibling,
            },
        };
        assert!(
            !attestation_data_matches_chain(&hashes, &off_head),
            "off-canonical head must be rejected"
        );

        // Control: the same vote with the canonical head=(2, r2) is accepted.
        let canonical_head = AttestationData {
            head: Checkpoint { slot: 2, root: r2 },
            ..off_head
        };
        assert!(
            attestation_data_matches_chain(&hashes, &canonical_head),
            "fully canonical vote must be accepted"
        );

        // A zero-hash head is also rejected up front.
        let zero_head = AttestationData {
            head: Checkpoint {
                slot: 2,
                root: H256::ZERO,
            },
            ..off_head
        };
        assert!(
            !attestation_data_matches_chain(&hashes, &zero_head),
            "zero-hash head must be rejected"
        );

        // A head slot beyond the chain view is rejected.
        let out_of_range_head = AttestationData {
            head: Checkpoint { slot: 99, root: r2 },
            ..off_head
        };
        assert!(
            !attestation_data_matches_chain(&hashes, &out_of_range_head),
            "out-of-range head slot must be rejected"
        );
    }

    /// Regression: `process_attestations` must not let `state.latest_justified`
    /// regress within a single block when attestations appear in body order
    /// whose target slots are not monotonically increasing.
    ///
    /// Observed on devnet at canonical slot 27984: a block carried three
    /// supermajority attestations targeting slots 27978, 27981, and 27974 (in
    /// that order). Each reached the supermajority threshold and the
    /// unconditional `state.latest_justified = target` assignment caused the
    /// post-state to end at `latest_justified.slot = 27974`. Because the
    /// store had already latched `latest_justified = 27978` from importing a
    /// fork block, every subsequent proposal failed
    /// `JustifiedDivergenceNotClosed` and the chain froze.
    ///
    /// Compressed setup: finalized=0, source=3 (justified), targets in body
    /// order 4 / 9 / 6 — all justifiable from finalized=0 (Δ=4 ≤ 5, Δ=9=3²,
    /// Δ=6=2·3). With 4 validators, three votes is supermajority, so each
    /// attestation crosses the threshold.
    #[test]
    fn latest_justified_does_not_regress_within_block() {
        const NUM_VALIDATORS: usize = 4;
        let r3 = H256([3u8; 32]);
        let r4 = H256([4u8; 32]);
        let r6 = H256([6u8; 32]);
        let r9 = H256([9u8; 32]);

        // historical_block_hashes indexed by slot. Genesis at slot 0 is ZERO
        // (matches the default finalized checkpoint), then we place the
        // canonical roots at slots 3 / 4 / 6 / 9. Other slots are empty and
        // are not referenced by any attestation in the test.
        let mut hashes: Vec<H256> = vec![H256::ZERO; 10];
        hashes[3] = r3;
        hashes[4] = r4;
        hashes[6] = r6;
        hashes[9] = r9;

        let validators = make_validators(NUM_VALIDATORS);
        let mut justified_slots = JustifiedSlots::new();
        justified_slots_ops::extend_to_slot(&mut justified_slots, 0, 9);
        // Mark slot 3 as justified so source=(3, r3) passes is_valid_vote.
        justified_slots_ops::set_justified(&mut justified_slots, 0, 3);

        let mut state = State {
            config: StateConfig { genesis_time: 0 },
            slot: 10,
            latest_block_header: BlockHeader {
                slot: 9,
                proposer_index: 0,
                parent_root: H256::ZERO,
                state_root: H256::ZERO,
                body_root: BlockBody::default().hash_tree_root(),
            },
            latest_justified: Checkpoint { slot: 3, root: r3 },
            latest_finalized: Checkpoint {
                slot: 0,
                root: H256::ZERO,
            },
            historical_block_hashes: SszList::try_from(hashes).unwrap(),
            justified_slots,
            validators: SszList::try_from(validators).unwrap(),
            justifications_roots: Default::default(),
            justifications_validators: JustificationValidators::new(),
        };

        // Three supermajority attestations (3 of 4 validators each), all from
        // source=(3, r3), in body order targeting slots 4 → 9 → 6.
        let atts: Vec<AggregatedAttestation> = vec![
            make_attestation(3, (3, r3), (4, r4), (4, r4), &[0, 1, 3], NUM_VALIDATORS),
            make_attestation(3, (3, r3), (9, r9), (9, r9), &[0, 1, 2], NUM_VALIDATORS),
            make_attestation(3, (3, r3), (6, r6), (6, r6), &[0, 2, 3], NUM_VALIDATORS),
        ];
        let atts: AggregatedAttestations = atts.try_into().unwrap();

        process_attestations(&mut state, &atts).expect("process_attestations should succeed");

        // After processing, the chain's view of "latest justified" must be the
        // highest justified target (slot 9), not the last-processed one
        // (slot 6). Pre-fix this assertion fails with slot=6.
        assert_eq!(
            state.latest_justified.slot,
            9,
            "latest_justified regressed: got slot={}, root={}; expected slot=9",
            state.latest_justified.slot,
            ShortRoot(&state.latest_justified.root.0)
        );
        assert_eq!(state.latest_justified.root, r9);
    }

    /// Regression (leanSpec #802): a supermajority attestation whose source sits
    /// at or behind the finalized boundary may justify a newer target, but must
    /// never advance (rewind) finalization below that boundary.
    ///
    /// Setup: finalized = justified = slot 4. A supermajority votes from a stale
    /// source at slot 1 to a fresh target at slot 6 (Δ=2 is pronic, so the target
    /// is justifiable). The target should become justified while the finalized
    /// checkpoint stays pinned at slot 4.
    #[test]
    fn stale_finalized_source_justifies_without_rewinding_finalization() {
        const NUM_VALIDATORS: usize = 4;
        let r1 = H256([1u8; 32]);
        let r4 = H256([4u8; 32]);
        let r6 = H256([6u8; 32]);

        let mut hashes: Vec<H256> = vec![H256::ZERO; 7];
        hashes[1] = r1;
        hashes[4] = r4;
        hashes[6] = r6;

        let validators = make_validators(NUM_VALIDATORS);
        // Window is relative to finalized=4; cover up to slot 6 (slots 5 and 6).
        let mut justified_slots = JustifiedSlots::new();
        justified_slots_ops::extend_to_slot(&mut justified_slots, 4, 6);

        let mut state = State {
            config: StateConfig { genesis_time: 0 },
            slot: 7,
            latest_block_header: BlockHeader {
                slot: 6,
                proposer_index: 0,
                parent_root: H256::ZERO,
                state_root: H256::ZERO,
                body_root: BlockBody::default().hash_tree_root(),
            },
            latest_justified: Checkpoint { slot: 4, root: r4 },
            latest_finalized: Checkpoint { slot: 4, root: r4 },
            historical_block_hashes: SszList::try_from(hashes).unwrap(),
            justified_slots,
            validators: SszList::try_from(validators).unwrap(),
            justifications_roots: Default::default(),
            justifications_validators: JustificationValidators::new(),
        };

        // Supermajority (3 of 4) attesting from the stale source (slot 1) to the
        // fresh target (slot 6). Source slot 1 <= finalized 4, so it is implicitly
        // justified and passes is_valid_vote.
        let atts: Vec<AggregatedAttestation> = vec![make_attestation(
            7,
            (1, r1),
            (6, r6),
            (6, r6),
            &[0, 1, 2],
            NUM_VALIDATORS,
        )];
        let atts: AggregatedAttestations = atts.try_into().unwrap();

        process_attestations(&mut state, &atts).expect("process_attestations should succeed");

        // The target is justified.
        assert_eq!(state.latest_justified.slot, 6);
        assert_eq!(state.latest_justified.root, r6);
        // Finalization stays pinned at the boundary: the stale source must not
        // rewind or re-finalize.
        assert_eq!(state.latest_finalized.slot, 4);
        assert_eq!(state.latest_finalized.root, r4);
    }

    /// leanSpec #1178: a `State` whose flat justification vote list is not
    /// tracked-root count × validator count is rejected with a typed error rather
    /// than silently producing short vote segments. Reachable via a malformed
    /// checkpoint-sync anchor, whose SSZ decoding cannot enforce this cross-field
    /// invariant.
    #[test]
    fn process_attestations_rejects_justification_votes_length_mismatch() {
        const NUM_VALIDATORS: usize = 4;
        let r1 = H256([1u8; 32]);

        let mut state = State {
            config: StateConfig { genesis_time: 0 },
            slot: 2,
            latest_block_header: BlockHeader {
                slot: 1,
                proposer_index: 0,
                parent_root: H256::ZERO,
                state_root: H256::ZERO,
                body_root: BlockBody::default().hash_tree_root(),
            },
            latest_justified: Checkpoint {
                slot: 0,
                root: H256::ZERO,
            },
            latest_finalized: Checkpoint {
                slot: 0,
                root: H256::ZERO,
            },
            historical_block_hashes: SszList::try_from(vec![H256::ZERO, r1]).unwrap(),
            justified_slots: JustifiedSlots::new(),
            validators: SszList::try_from(make_validators(NUM_VALIDATORS)).unwrap(),
            // One tracked root, but a vote list of the wrong width (3, not 1 * 4).
            justifications_roots: SszList::try_from(vec![r1]).unwrap(),
            justifications_validators: JustificationValidators::with_length(3).unwrap(),
        };

        let atts: AggregatedAttestations = Vec::<AggregatedAttestation>::new().try_into().unwrap();
        let err = process_attestations(&mut state, &atts).unwrap_err();
        assert!(
            matches!(
                err,
                Error::JustificationVotesLengthMismatch {
                    expected: 4,
                    actual: 3
                }
            ),
            "expected JustificationVotesLengthMismatch {{ expected: 4, actual: 3 }}, got {err:?}"
        );
    }

    /// A vote whose target is already justified must be SKIPPED, not rejected:
    /// `is_valid_vote` returns `Ok(false)` and the loop does `continue`, so the
    /// block carrying it still applies cleanly.
    ///
    /// The block builder relies on this. It deliberately packs such votes,
    /// because they carry no justification value but still move LMD-GHOST
    /// (`insert_signed_block` records every attestation a block carries as a
    /// fork-choice vote, whatever this function decides). If the transition
    /// ever started erroring here instead, every proposer packing a settled
    /// target would produce blocks the network rejects.
    #[test]
    fn process_attestations_skips_an_already_justified_target_without_rejecting_the_block() {
        const NUM_VALIDATORS: usize = 4;
        let r1 = H256([1u8; 32]);
        let r2 = H256([2u8; 32]);

        let mut justified_slots = JustifiedSlots::new();
        justified_slots_ops::extend_to_slot(&mut justified_slots, 0, 1);
        justified_slots_ops::set_justified(&mut justified_slots, 0, 1);

        let mut state = State {
            config: StateConfig { genesis_time: 0 },
            slot: 3,
            latest_block_header: BlockHeader {
                slot: 2,
                proposer_index: 0,
                parent_root: r1,
                state_root: H256::ZERO,
                body_root: BlockBody::default().hash_tree_root(),
            },
            latest_justified: Checkpoint { slot: 1, root: r1 },
            latest_finalized: Checkpoint {
                slot: 0,
                root: H256::ZERO,
            },
            historical_block_hashes: SszList::try_from(vec![H256::ZERO, r1, r2]).unwrap(),
            justified_slots,
            validators: SszList::try_from(make_validators(NUM_VALIDATORS)).unwrap(),
            justifications_roots: SszList::try_from(vec![]).unwrap(),
            justifications_validators: JustificationValidators::new(),
        };

        // Target slot 1 is already justified above; source is genesis.
        let vote = AggregatedAttestation {
            aggregation_bits: make_bits(&[0, 1, 2], NUM_VALIDATORS),
            data: AttestationData {
                slot: 2,
                head: Checkpoint { slot: 1, root: r1 },
                target: Checkpoint { slot: 1, root: r1 },
                source: Checkpoint {
                    slot: 0,
                    root: H256::ZERO,
                },
            },
        };

        let before = state.latest_justified;
        let atts: AggregatedAttestations = vec![vote].try_into().unwrap();

        process_attestations(&mut state, &atts)
            .expect("an already-justified target is skipped, not an error");

        assert_eq!(
            state.latest_justified, before,
            "the skipped vote must not move justification"
        );
        assert!(
            state.justifications_roots.is_empty(),
            "the skipped vote must not open a tally for a settled target"
        );
    }

    /// leanSpec #1178: `process_attestations` on a state with no validators is
    /// rejected with a typed error. Belt-and-suspenders: the header stage already
    /// rejects an empty registry first in the normal flow, but the flat-vote
    /// unpack relies on a non-zero segment width directly.
    #[test]
    fn process_attestations_rejects_empty_validator_registry() {
        let mut state = State {
            config: StateConfig { genesis_time: 0 },
            slot: 1,
            latest_block_header: BlockHeader {
                slot: 0,
                proposer_index: 0,
                parent_root: H256::ZERO,
                state_root: H256::ZERO,
                body_root: BlockBody::default().hash_tree_root(),
            },
            latest_justified: Checkpoint {
                slot: 0,
                root: H256::ZERO,
            },
            latest_finalized: Checkpoint {
                slot: 0,
                root: H256::ZERO,
            },
            historical_block_hashes: SszList::try_from(vec![H256::ZERO]).unwrap(),
            justified_slots: JustifiedSlots::new(),
            validators: SszList::try_from(make_validators(0)).unwrap(),
            justifications_roots: Default::default(),
            justifications_validators: JustificationValidators::new(),
        };

        let atts: AggregatedAttestations = Vec::<AggregatedAttestation>::new().try_into().unwrap();
        let err = process_attestations(&mut state, &atts).unwrap_err();
        assert!(
            matches!(err, Error::NoValidators),
            "expected NoValidators, got {err:?}"
        );
    }
    /// NUEVO: no esta en la suite de ethlambda. `process_attestations` tiene
    /// que RECHAZAR el bloque cuando una attestation por lo demas valida no
    /// referencia a ningun validador.
    ///
    /// Por que lo agregamos. El original corta con `return Err(...)` adentro
    /// del loop, en tres lugares. Aca el loop tiene UNA SOLA SALIDA (Aeneas
    /// no soporta early returns adentro de loops) y el error se junta en la
    /// bandera `fallo`. La primera version de esa reescritura guardaba la
    /// bandera y no la miraba nunca: devolvia `Ok(())` con un bloque
    /// invalido, y encima serializaba, cosa que el original no hace al cortar.
    ///
    /// Los seis tests que trajimos de ethlambda no cubren este camino: los dos
    /// que chequean errores prueban los de ANTES del loop. Por eso el agujero
    /// paso desapercibido. Este test lo cierra.
    #[test]
    fn process_attestations_rejects_empty_aggregation_bits() {
        const NUM_VALIDATORS: usize = 4;
        let r3 = H256([3u8; 32]);
        let r4 = H256([4u8; 32]);

        let mut hashes: Vec<H256> = vec![H256::ZERO; 10];
        hashes[3] = r3;
        hashes[4] = r4;

        let mut justified_slots = JustifiedSlots::new();
        justified_slots_ops::extend_to_slot(&mut justified_slots, 0, 9);
        // Slot 3 justificado para que source=(3, r3) pase is_valid_vote.
        justified_slots_ops::set_justified(&mut justified_slots, 0, 3);

        let mut state = State {
            config: StateConfig { genesis_time: 0 },
            slot: 10,
            latest_block_header: BlockHeader {
                slot: 9,
                proposer_index: 0,
                parent_root: H256::ZERO,
                state_root: H256::ZERO,
                body_root: BlockBody::default().hash_tree_root(),
            },
            latest_justified: Checkpoint { slot: 3, root: r3 },
            latest_finalized: Checkpoint {
                slot: 0,
                root: H256::ZERO,
            },
            historical_block_hashes: SszList::try_from(hashes).unwrap(),
            justified_slots,
            validators: SszList::try_from(make_validators(NUM_VALIDATORS)).unwrap(),
            justifications_roots: Default::default(),
            justifications_validators: JustificationValidators::new(),
        };

        // El mismo voto valido del test de regresion, pero sin un solo bit.
        let atts: Vec<AggregatedAttestation> =
            vec![make_attestation(3, (3, r3), (4, r4), (4, r4), &[], NUM_VALIDATORS)];
        let atts: AggregatedAttestations = atts.try_into().unwrap();

        let before = state.latest_justified;
        let err = process_attestations(&mut state, &atts).unwrap_err();
        assert!(
            matches!(err, Error::EmptyAggregationBits),
            "expected EmptyAggregationBits, got {err:?}"
        );
        assert_eq!(
            state.latest_justified, before,
            "un bloque rechazado no puede mover la justificacion"
        );
    }

    /// NUEVO: no esta en la suite de ethlambda. El otro error que vivia adentro
    /// del loop: un bit prendido mas alla del conjunto de validadores.
    ///
    /// Los bits van de largo 6 con los indices 0, 1 y 5 prendidos, sobre 4
    /// validadores. El 5 esta fuera de rango. Los otros dos alcanzan para que
    /// NO sea el caso de EmptyAggregationBits, asi que el test distingue los
    /// dos errores en vez de confundirlos.
    #[test]
    fn process_attestations_rejects_an_out_of_range_bit() {
        const NUM_VALIDATORS: usize = 4;
        let r3 = H256([3u8; 32]);
        let r4 = H256([4u8; 32]);

        let mut hashes: Vec<H256> = vec![H256::ZERO; 10];
        hashes[3] = r3;
        hashes[4] = r4;

        let mut justified_slots = JustifiedSlots::new();
        justified_slots_ops::extend_to_slot(&mut justified_slots, 0, 9);
        justified_slots_ops::set_justified(&mut justified_slots, 0, 3);

        let mut state = State {
            config: StateConfig { genesis_time: 0 },
            slot: 10,
            latest_block_header: BlockHeader {
                slot: 9,
                proposer_index: 0,
                parent_root: H256::ZERO,
                state_root: H256::ZERO,
                body_root: BlockBody::default().hash_tree_root(),
            },
            latest_justified: Checkpoint { slot: 3, root: r3 },
            latest_finalized: Checkpoint {
                slot: 0,
                root: H256::ZERO,
            },
            historical_block_hashes: SszList::try_from(hashes).unwrap(),
            justified_slots,
            validators: SszList::try_from(make_validators(NUM_VALIDATORS)).unwrap(),
            justifications_roots: Default::default(),
            justifications_validators: JustificationValidators::new(),
        };

        let atts: Vec<AggregatedAttestation> =
            vec![make_attestation(3, (3, r3), (4, r4), (4, r4), &[0, 1, 5], 6)];
        let atts: AggregatedAttestations = atts.try_into().unwrap();

        let err = process_attestations(&mut state, &atts).unwrap_err();
        assert!(
            matches!(
                err,
                Error::AggregationBitsOutOfBounds {
                    index: 5,
                    validator_count: 4
                }
            ),
            "expected AggregationBitsOutOfBounds {{ index: 5, validator_count: 4 }}, got {err:?}"
        );
    }
}
