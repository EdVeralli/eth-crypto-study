//! Mini crate para pasar la STF de ethlambda por la cadena de herramientas
//! Rust -> Lean (hax + Charon + Aeneas).
//!
//! Por que existe: Charon compila el crate Y TODAS SUS DEPENDENCIAS, pero
//! Aeneas solo EMITE definiciones del crate local. Los tipos que vienen de
//! una dependencia salen nombrados y sin definir, y el Lean generado no tipa.
//! Para que `State` y `Block` existan del otro lado tienen que estar adentro
//! del crate que se extrae. De ahi este crate.
//!
//! Que hay adentro:
//!
//! | modulo                  | de donde sale                                |
//! |-------------------------|----------------------------------------------|
//! | `stf`                   | COPIA de ethlambda, solo cambian los `use`   |
//! | `justified_slots_ops`   | COPIA de ethlambda, solo cambian los `use`   |
//! | `tipos`                 | definiciones de ethlambda, sin los derives   |
//! | `ssz`                   | NUESTRO: sustitutos de los contenedores SSZ  |
//! | `stubs`                 | NUESTRO: tracing y metrics sin efecto        |
//!
//! Lo copiado viene de lambdaclass/ethlambda (MIT):
//!   crates/blockchain/state_transition/src/lib.rs
//!   crates/blockchain/state_transition/src/justified_slots_ops.rs
//!   crates/common/types/src/{primitives,checkpoint,state,block,attestation}.rs
//!
//! Ver README.md por lo que se pierde al sustituir.

pub mod justified_slots_ops;
pub mod ssz;
pub mod stf;
pub mod stubs;
pub mod tipos;
