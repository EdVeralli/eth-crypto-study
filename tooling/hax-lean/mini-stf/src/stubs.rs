//! Reemplazos sin efecto de `tracing` y de `ethlambda-metrics`.
//!
//! ESTO NO ES CODIGO DE ETHLAMBDA.
//!
//! Las dos son infraestructura con estado global: logging y contadores de
//! Prometheus. No participan de la logica del protocolo, pero si de las
//! firmas, asi que sacarlas obligaria a editar el cuerpo de la STF. Estos
//! stubs existen para evitar justamente eso: con ellos, el cuerpo de
//! `stf.rs` queda identico al original y solo cambian las lineas `use`.

/// `tracing::info!` sin efecto.
///
/// Los nombres llevan sufijo porque `warn` choca con el atributo `warn` que
/// trae Rust; en `stf.rs` se importan con alias y quedan como `info` y `warn`.
macro_rules! info_stub {
    ($($cualquier_cosa:tt)*) => {};
}

/// `tracing::warn!` sin efecto.
macro_rules! warn_stub {
    ($($cualquier_cosa:tt)*) => {};
}

pub(crate) use info_stub;
pub(crate) use warn_stub;

/// `ethlambda-metrics` sin efecto.
pub mod metrics {
    /// Lo que devuelven los `time_*`. En el original mide y reporta al
    /// soltarse; aca no hace nada.
    pub struct TimingGuard;

    pub fn inc_slots_processed(_count: u64) {}
    pub fn inc_attestations_processed(_count: u64) {}
    pub fn inc_finalizations(_result: &str) {}

    pub fn time_state_transition() -> TimingGuard {
        TimingGuard
    }
    pub fn time_slots_processing() -> TimingGuard {
        TimingGuard
    }
    pub fn time_block_processing() -> TimingGuard {
        TimingGuard
    }
    pub fn time_attestations_processing() -> TimingGuard {
        TimingGuard
    }
}
