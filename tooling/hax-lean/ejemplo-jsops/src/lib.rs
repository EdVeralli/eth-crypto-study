// Ejemplo de traduccion Rust -> Lean con hax + Charon + Aeneas.
//
// El cuerpo de este archivo (de `relative_index` para abajo) es una copia
// textual de ethlambda:
//
//   lambdaclass/ethlambda, commit 22d1a72
//   crates/blockchain/state_transition/src/justified_slots_ops.rs
//   MIT License, Copyright (c) 2025 Lambdaclass
//
// Lo unico agregado son los dos sustitutos locales de mas abajo, que ocupan el
// lugar de `ethlambda_types::state::JustifiedSlots` y de `crate::Error`. Estan
// para que el crate sea autocontenido: la leccion del experimento es que el
// objetivo tiene que ser su propio crate, porque un solo `dyn` en el cierre de
// dependencias tira abajo la extraccion entera.
//
// Como correrlo, desde la raiz de este crate y adentro del contenedor:
//
//   cargo hax into lean
//
// Resultado esperado: 19 definiciones, cero `sorry`, cero errores, y la
// plantilla de cosas a modelar a mano vacia.

//!
//! The bitlist stores justification status relative to the finalized boundary:
//! - Index 0 = finalized_slot + 1
//! - Slots ≤ finalized_slot are implicitly justified (no storage needed)

// --- sustitutos locales de las dos dependencias, para aislar el modulo ---
#[derive(Clone, Default)]
pub struct JustifiedSlots {
    bits: Vec<bool>,
}

impl JustifiedSlots {
    pub fn new() -> Self { Self { bits: Vec::new() } }
    pub fn with_length(n: usize) -> Option<Self> { Some(Self { bits: vec![false; n] }) }
    pub fn len(&self) -> usize { self.bits.len() }
    pub fn get(&self, i: usize) -> Option<bool> {
        if i < self.bits.len() { Some(self.bits[i]) } else { None }
    }
    pub fn set(&mut self, i: usize, v: bool) -> Option<()> {
        if i < self.bits.len() { self.bits[i] = v; Some(()) } else { None }
    }
}


pub enum Error {
    JustifiedSlotOutOfRange { slot: u64, finalized_slot: u64, tracked_length: usize },
}
// --- fin de los sustitutos ---

/// Calculate relative index for a slot after finalization.
/// Returns None if slot <= finalized_slot (implicitly justified).
fn relative_index(target_slot: u64, finalized_slot: u64) -> Option<usize> {
    target_slot
        .checked_sub(finalized_slot)?
        .checked_sub(1)
        .map(|idx| idx as usize)
}

/// Check if a slot is justified (finalized slots are implicitly justified).
///
/// A slot past the finalized boundary but beyond the tracked bitlist has no
/// justification status to report. The spec surfaces that as a domain rejection
/// (leanSpec #1023, `JUSTIFIED_SLOT_OUT_OF_RANGE`) rather than reading it as
/// "not justified", so a block carrying such a vote is invalid. Callers on the
/// state transition path must propagate the error; callers that only pre-filter
/// candidate votes may treat it as "unknown, so not justified".
pub fn is_slot_justified(
    slots: &JustifiedSlots,
    finalized_slot: u64,
    target_slot: u64,
) -> Result<bool, Error> {
    // Finalized slots are implicitly justified and need no tracked bit.
    let Some(idx) = relative_index(target_slot, finalized_slot) else {
        return Ok(true);
    };
    slots.get(idx).ok_or(Error::JustifiedSlotOutOfRange {
        slot: target_slot,
        finalized_slot,
        tracked_length: slots.len(),
    })
}

/// Mark a slot as justified. No-op if slot is finalized.
pub fn set_justified(slots: &mut JustifiedSlots, finalized_slot: u64, target_slot: u64) {
    if let Some(idx) = relative_index(target_slot, finalized_slot) {
        slots.set(idx, true).expect("index out of bounds");
    }
}

/// Extend capacity to cover slots up to target_slot relative to finalized boundary.
/// New slots are initialized to false (unjustified).
pub fn extend_to_slot(slots: &mut JustifiedSlots, finalized_slot: u64, target_slot: u64) {
    let Some(required_idx) = relative_index(target_slot, finalized_slot) else {
        return;
    };
    let required_capacity = required_idx + 1;
    if slots.len() >= required_capacity {
        return;
    }
    let mut extended =
        JustifiedSlots::with_length(required_capacity).expect("capacity limit exceeded");
    for i in 0..slots.len() {
        if slots.get(i) == Some(true) {
            extended.set(i, true).expect("index within capacity");
        }
    }
    *slots = extended;
}

/// Shift window by dropping finalized slots when finalization advances.
pub fn shift_window(slots: &mut JustifiedSlots, delta: usize) {
    if delta == 0 {
        return;
    }
    if delta >= slots.len() {
        *slots = JustifiedSlots::new();
        return;
    }
    // Create new bitlist with shifted data
    let remaining = slots.len() - delta;
    let mut new_bits = JustifiedSlots::with_length(remaining).expect("capacity limit exceeded");
    for i in 0..remaining {
        if slots.get(i + delta).unwrap_or(false) {
            new_bits.set(i, true).unwrap();
        }
    }
    *slots = new_bits;
}
