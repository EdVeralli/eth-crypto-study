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
//! | `stf`                   | de ethlambda; 8 de 12 funciones sin tocar    |
//! | `justified_slots_ops`   | COPIA de ethlambda, solo cambian los `use`   |
//! | `tipos`                 | definiciones de ethlambda, sin los derives   |
//! | `ssz`                   | NUESTRO: sustitutos de los contenedores SSZ  |
//! | `mapa`                  | NUESTRO: el mapa de votos como lista de pares|
//! | `stubs`                 | NUESTRO: tracing y metrics sin efecto        |
//!
//! Lo copiado viene de lambdaclass/ethlambda (MIT):
//!   crates/blockchain/state_transition/src/lib.rs
//!   crates/blockchain/state_transition/src/justified_slots_ops.rs
//!   crates/common/types/src/{primitives,checkpoint,state,block,attestation}.rs
//!
//! CUANTO SE TOCO DEL CODIGO DE ELLOS, medido contra el original
//! (commit 6168a0e, ignorando comentarios):
//!
//!   IDENTICAS, 8 de 12:  state_transition, process_slots, process_block,
//!                        is_valid_vote, attestation_data_matches_chain,
//!                        slot_is_justifiable_after, is_proposer,
//!                        current_proposer
//!
//!   CAMBIADAS, 4:        process_block_header       3 lineas
//!                        try_finalize              ~18 lineas
//!                        serialize_justifications  ~23 lineas
//!                        process_attestations      ~87 lineas
//!
//!   Mas 19 funciones auxiliares nuevas, que son nuestras.
//!
//! O sea que el pedido concreto es tocar cuatro funciones, unas 130 lineas de
//! logica. El resto queda tal cual.
//!
//! Ver README.md por lo que se pierde al sustituir.

pub mod justified_slots_ops;
pub mod mapa;
pub mod ssz;
pub mod stf;
pub mod stubs;
pub mod tipos;
