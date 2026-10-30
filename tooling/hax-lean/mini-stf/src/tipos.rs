//! Los tipos que la STF necesita, copiados de `ethlambda-types`.
//!
//! Las DEFINICIONES de los structs y sus campos son de ethlambda
//! (MIT, lambdaclass/ethlambda, crates/common/types/src/). Lo que se saco:
//!
//!   - los derives de serializacion (`Serialize`, `Deserialize`, `SszEncode`,
//!     `SszDecode`, `HashTreeRoot`) y sus helpers de serde,
//!   - los tipos que la STF no toca (`SignedBlock`, `MultiMessageAggregate`,
//!     `SingleMessageAggregate`, `Attestation`, `SignedAttestation`,
//!     `HashedAttestationData`, las firmas XMSS),
//!   - los tests.
//!
//! Se dejaron los derives de `std` (`Clone`, `Copy`, `Default`, `PartialEq`),
//! que Aeneas sabe traducir solo.

use crate::ssz::{SszBitlist, SszList};

// ---------------------------------------------------------------------------
// primitives
// ---------------------------------------------------------------------------

/// Hash de 256 bits: raiz de bloque, raiz de estado, etc.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct H256(pub [u8; 32]);

impl H256 {
    pub const ZERO: Self = Self([0u8; 32]);
}

impl std::fmt::Display for H256 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "0x")?;
        for byte in &self.0 {
            write!(f, "{:02x}", byte)?;
        }
        Ok(())
    }
}

/// Helper de display para raices truncadas. La STF lo usa en los logs.
pub struct ShortRoot<'a>(pub &'a [u8; 32]);

impl std::fmt::Display for ShortRoot<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for byte in &self.0[..4] {
            write!(f, "{:02x}", byte)?;
        }
        Ok(())
    }
}

/// Merkleizacion SSZ... o lo que hace falta de ella.
///
/// En ethlambda esto es `libssz_merkle::HashTreeRoot` con sha2, que vive en una
/// dependencia -- y Charon no trae las definiciones de las dependencias. Asi
/// que aca va un hash propio.
///
/// QUE ES Y QUE NO ES:
///
///   NO da los mismos valores que SSZ. No sirve para interoperar con otros
///   clientes, ni para calcular una raiz que alguien mas vaya a verificar.
///
///   SI cumple lo unico que la STF le pide: que estados distintos den raices
///   distintas. Es un hash polinomico (multiplicar por un primo y sumar),
///   determinista, escrito con loops de indice y aritmetica `wrapping` para
///   que la cadena de herramientas lo pueda traducir.
///
/// DEL LADO DE LEAN se trata aparte: ahi conviene declararlo OPACO y agregar
/// la inyectividad como hipotesis explicita en los teoremas que la necesiten
/// ("suponiendo que el hash no colisiona, vale ST-3"). Es la forma estandar de
/// modelar criptografia, y es lo que hace `fradamt/verified-consensus` con sus
/// tres axiomas delegados a ArkLib.
pub trait HashTreeRoot {
    fn hash_tree_root(&self) -> H256;
}

/// El primo de FNV-1a. Cualquier primo grande sirve.
const PRIMO: u64 = 1_099_511_628_211;

/// La semilla, tambien de FNV-1a.
const SEMILLA: u64 = 14_695_981_039_346_656_037;

/// Un paso del hash: acumulado por el primo, mas el valor nuevo.
fn mezclar(acc: u64, x: u64) -> u64 {
    acc.wrapping_mul(PRIMO).wrapping_add(x)
}

/// Mezcla los 32 bytes de una raiz.
fn mezclar_raiz(acc: u64, r: &H256) -> u64 {
    let mut h = acc;
    for i in 0..32 {
        h = mezclar(h, r.0[i] as u64);
    }
    h
}

/// Mezcla una clave publica de validador.
fn mezclar_pubkey(acc: u64, k: &ValidatorPubkeyBytes) -> u64 {
    let mut h = acc;
    for i in 0..PUBLIC_KEY_SIZE {
        h = mezclar(h, k[i] as u64);
    }
    h
}

/// Mezcla un checkpoint.
fn mezclar_checkpoint(acc: u64, c: &Checkpoint) -> u64 {
    mezclar(mezclar_raiz(acc, &c.root), c.slot)
}

/// Pone el acumulado de 64 bits en los primeros 8 bytes de una raiz.
/// Division y modulo en vez de desplazamientos, que traducen mas seguro.
fn a_raiz(v: u64) -> H256 {
    let mut bytes = [0u8; 32];
    let mut resto = v;
    for i in 0..8 {
        bytes[i] = (resto % 256) as u8;
        resto = resto / 256;
    }
    H256(bytes)
}

// ---------------------------------------------------------------------------
// checkpoint
// ---------------------------------------------------------------------------

/// Un punto de la historia de la cadena.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct Checkpoint {
    /// La raiz del bloque del checkpoint.
    pub root: H256,
    /// El slot del bloque del checkpoint.
    pub slot: u64,
}

// ---------------------------------------------------------------------------
// attestation
// ---------------------------------------------------------------------------

/// Lo que un validador afirma sobre la cadena que ve.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct AttestationData {
    /// El slot al que corresponde el voto.
    pub slot: u64,
    /// El checkpoint de la cabeza que ve el validador.
    pub head: Checkpoint,
    /// El checkpoint del target que ve el validador.
    pub target: Checkpoint,
    /// El checkpoint del source que ve el validador.
    pub source: Checkpoint,
}

impl HashTreeRoot for AttestationData {
    fn hash_tree_root(&self) -> H256 {
        let mut h = SEMILLA;
        h = mezclar(h, self.slot);
        h = mezclar_checkpoint(h, &self.head);
        h = mezclar_checkpoint(h, &self.target);
        h = mezclar_checkpoint(h, &self.source);
        a_raiz(h)
    }
}

impl AttestationData {
    /// Si este voto reemplaza a `other` como ultimo mensaje del validador.
    pub fn supersedes(&self, other: &AttestationData) -> bool {
        self.slot > other.slot
            || (self.slot == other.slot && self.hash_tree_root() > other.hash_tree_root())
    }
}

/// Bitlist de participacion de validadores.
pub type AggregationBits = SszBitlist<4096>;

/// Voto agregado: bits de participacion mas el contenido.
#[derive(Debug, Clone, PartialEq)]
pub struct AggregatedAttestation {
    /// Que validadores participaron.
    pub aggregation_bits: AggregationBits,
    /// El contenido del voto.
    pub data: AttestationData,
}

// ---------------------------------------------------------------------------
// block
// ---------------------------------------------------------------------------

/// Maximo de datos de attestation distintos por bloque.
pub const MAX_ATTESTATIONS_DATA: usize = 8;

/// Lista de votos agregados de un bloque.
pub type AggregatedAttestations = SszList<AggregatedAttestation, 4096>;

/// El encabezado de un bloque.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockHeader {
    /// En que slot se propuso.
    pub slot: u64,
    /// Quien lo propuso.
    pub proposer_index: u64,
    /// La raiz del bloque padre.
    pub parent_root: H256,
    /// La raiz del estado despues de aplicarlo.
    pub state_root: H256,
    /// La raiz del cuerpo del bloque.
    pub body_root: H256,
}

impl HashTreeRoot for BlockHeader {
    fn hash_tree_root(&self) -> H256 {
        let mut h = SEMILLA;
        h = mezclar(h, self.slot);
        h = mezclar(h, self.proposer_index);
        h = mezclar_raiz(h, &self.parent_root);
        h = mezclar_raiz(h, &self.state_root);
        h = mezclar_raiz(h, &self.body_root);
        a_raiz(h)
    }
}

/// El cuerpo de un bloque: hoy, los votos.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct BlockBody {
    /// Los votos que transporta el bloque.
    pub attestations: AggregatedAttestations,
}

impl HashTreeRoot for BlockBody {
    fn hash_tree_root(&self) -> H256 {
        let mut h = SEMILLA;
        h = mezclar(h, self.attestations.len() as u64);
        for i in 0..self.attestations.len() {
            match self.attestations.get(i) {
                Some(a) => {
                    h = mezclar(h, a.aggregation_bits.len() as u64);
                    for j in 0..a.aggregation_bits.len() {
                        let bit = match a.aggregation_bits.get(j) {
                            Some(true) => 1u64,
                            _ => 0u64,
                        };
                        h = mezclar(h, bit);
                    }
                    h = mezclar_raiz(h, &a.data.hash_tree_root());
                }
                None => {}
            }
        }
        a_raiz(h)
    }
}

/// Un bloque completo.
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    /// En que slot se propuso.
    pub slot: u64,
    /// Quien lo propuso.
    pub proposer_index: u64,
    /// La raiz del bloque padre.
    pub parent_root: H256,
    /// La raiz del estado despues de aplicarlo.
    pub state_root: H256,
    /// El contenido.
    pub body: BlockBody,
}

impl HashTreeRoot for Block {
    fn hash_tree_root(&self) -> H256 {
        let mut h = SEMILLA;
        h = mezclar(h, self.slot);
        h = mezclar(h, self.proposer_index);
        h = mezclar_raiz(h, &self.parent_root);
        h = mezclar_raiz(h, &self.state_root);
        h = mezclar_raiz(h, &self.body.hash_tree_root());
        a_raiz(h)
    }
}

impl Block {
    /// Extrae el encabezado, calculando la raiz del cuerpo.
    pub fn header(&self) -> BlockHeader {
        BlockHeader {
            slot: self.slot,
            proposer_index: self.proposer_index,
            parent_root: self.parent_root,
            state_root: self.state_root,
            body_root: self.body.hash_tree_root(),
        }
    }
}

// ---------------------------------------------------------------------------
// state
// ---------------------------------------------------------------------------

/// Maximo de raices historicas en el estado. 2**18.
pub const HISTORICAL_ROOTS_LIMIT: usize = 262_144;

/// Maximo de validadores en el registro.
pub const VALIDATOR_REGISTRY_LIMIT: usize = 4096;

/// Tamanio de una clave publica XMSS serializada.
pub const PUBLIC_KEY_SIZE: usize = 32;

pub type ValidatorPubkeyBytes = [u8; PUBLIC_KEY_SIZE];

/// Lista de raices de bloques historicos.
pub type HistoricalBlockHashes = SszList<H256, HISTORICAL_ROOTS_LIMIT>;

/// Bitlist de que slots quedaron justificados.
pub type JustifiedSlots = SszBitlist<HISTORICAL_ROOTS_LIMIT>;

/// Lista de raices de bloques justificados.
pub type JustificationRoots = SszList<H256, HISTORICAL_ROOTS_LIMIT>;

/// Bitlist de quien voto por cada raiz en juego.
pub type JustificationValidators =
    SszBitlist<{ HISTORICAL_ROOTS_LIMIT * VALIDATOR_REGISTRY_LIMIT }>;

/// Metadata de un validador.
#[derive(Debug, Clone, PartialEq)]
pub struct Validator {
    /// Clave publica para firmar votos.
    pub attestation_pubkey: ValidatorPubkeyBytes,
    /// Clave publica para firmar propuestas.
    pub proposal_pubkey: ValidatorPubkeyBytes,
    /// Indice en el registro.
    pub index: u64,
}

/// Los parametros de genesis que viven adentro del estado.
#[derive(Debug, Clone, PartialEq)]
pub struct StateConfig {
    pub genesis_time: u64,
}

/// El objeto de estado del consenso.
#[derive(Debug, Clone, PartialEq)]
pub struct State {
    /// Parametros de genesis.
    pub config: StateConfig,
    /// El slot actual.
    pub slot: u64,
    /// El encabezado del ultimo bloque.
    pub latest_block_header: BlockHeader,
    /// El ultimo checkpoint justificado.
    pub latest_justified: Checkpoint,
    /// El ultimo checkpoint finalizado.
    pub latest_finalized: Checkpoint,
    /// Raices de bloques historicos.
    pub historical_block_hashes: HistoricalBlockHashes,
    /// Que slots historicos quedaron justificados.
    pub justified_slots: JustifiedSlots,
    /// El registro de validadores.
    pub validators: SszList<Validator, VALIDATOR_REGISTRY_LIMIT>,
    /// Raices de los bloques que estan juntando votos.
    pub justifications_roots: JustificationRoots,
    /// Quien voto por cada una de esas raices.
    pub justifications_validators: JustificationValidators,
}

impl HashTreeRoot for State {
    fn hash_tree_root(&self) -> H256 {
        let mut h = SEMILLA;
        h = mezclar(h, self.config.genesis_time);
        h = mezclar(h, self.slot);
        h = mezclar_raiz(h, &self.latest_block_header.hash_tree_root());
        h = mezclar_checkpoint(h, &self.latest_justified);
        h = mezclar_checkpoint(h, &self.latest_finalized);

        h = mezclar(h, self.historical_block_hashes.len() as u64);
        for i in 0..self.historical_block_hashes.len() {
            match self.historical_block_hashes.get(i) {
                Some(r) => h = mezclar_raiz(h, r),
                None => {}
            }
        }

        h = mezclar(h, self.justified_slots.len() as u64);
        for i in 0..self.justified_slots.len() {
            let bit = match self.justified_slots.get(i) {
                Some(true) => 1u64,
                _ => 0u64,
            };
            h = mezclar(h, bit);
        }

        h = mezclar(h, self.validators.len() as u64);
        for i in 0..self.validators.len() {
            match self.validators.get(i) {
                Some(v) => {
                    h = mezclar(h, v.index);
                    h = mezclar_pubkey(h, &v.attestation_pubkey);
                    h = mezclar_pubkey(h, &v.proposal_pubkey);
                }
                None => {}
            }
        }

        h = mezclar(h, self.justifications_roots.len() as u64);
        for i in 0..self.justifications_roots.len() {
            match self.justifications_roots.get(i) {
                Some(r) => h = mezclar_raiz(h, r),
                None => {}
            }
        }

        h = mezclar(h, self.justifications_validators.len() as u64);
        for i in 0..self.justifications_validators.len() {
            let bit = match self.justifications_validators.get(i) {
                Some(true) => 1u64,
                _ => 0u64,
            };
            h = mezclar(h, bit);
        }

        a_raiz(h)
    }
}
