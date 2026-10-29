//! Sustitutos de los contenedores SSZ de `libssz-types`.
//!
//! ESTO NO ES CODIGO DE ETHLAMBDA. Lo escribimos nosotros.
//!
//! El original (`libssz_types::SszList` y `SszBitlist`) arrastra la biblioteca
//! de serializacion entera: derives, merkleizacion, sha2. Para traducir a Lean
//! solo necesitamos el comportamiento de coleccion, asi que estos son
//! envoltorios de `Vec` con el mismo API que usa la STF, y nada mas.
//!
//! Lo que se pierde: la codificacion SSZ y la raiz de Merkle. La STF no las
//! calcula por su cuenta -- las pide via `hash_tree_root()`, que en este crate
//! es un stub (ver `tipos.rs`).

/// Error de capacidad. El original distingue varios casos; aca alcanza con uno.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FueraDeCapacidad;

/// Lista de largo variable con tope `N`, equivalente a `libssz_types::SszList`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SszList<T, const N: usize> {
    items: Vec<T>,
}

impl<T, const N: usize> SszList<T, N> {
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn get(&self, i: usize) -> Option<&T> {
        self.items.get(i)
    }

    pub fn iter(&self) -> core::slice::Iter<'_, T> {
        self.items.iter()
    }

    /// Devuelve el `Vec` de adentro. La STF lo usa para reconstruir la lista
    /// de hashes historicos.
    pub fn into_inner(self) -> Vec<T> {
        self.items
    }
}

impl<T, const N: usize> Default for SszList<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

/// La STF pasa la lista donde se espera un `&[T]`. El original lo permite
/// via `Deref`; aca igual.
impl<T, const N: usize> core::ops::Deref for SszList<T, N> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.items
    }
}

/// Y tambien la recorre con `for x in &lista`.
impl<'a, T, const N: usize> IntoIterator for &'a SszList<T, N> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.iter()
    }
}

impl<T, const N: usize> TryFrom<Vec<T>> for SszList<T, N> {
    type Error = FueraDeCapacidad;

    fn try_from(items: Vec<T>) -> Result<Self, Self::Error> {
        if items.len() > N {
            return Err(FueraDeCapacidad);
        }
        Ok(Self { items })
    }
}

/// Bitlist de largo variable con tope `N`, equivalente a
/// `libssz_types::SszBitlist`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SszBitlist<const N: usize> {
    bits: Vec<bool>,
}

impl<const N: usize> SszBitlist<N> {
    pub fn new() -> Self {
        Self { bits: Vec::new() }
    }

    /// Bitlist de `largo` posiciones, todas en false.
    pub fn with_length(largo: usize) -> Result<Self, FueraDeCapacidad> {
        if largo > N {
            return Err(FueraDeCapacidad);
        }
        Ok(Self {
            bits: vec![false; largo],
        })
    }

    pub fn len(&self) -> usize {
        self.bits.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bits.is_empty()
    }

    pub fn get(&self, i: usize) -> Option<bool> {
        // Sin `.copied()`: eso genera `core.option.OptionShared0T.copied`,
        // que CoreModels no modela.
        if i < self.bits.len() {
            Some(self.bits[i])
        } else {
            None
        }
    }

    pub fn set(&mut self, i: usize, valor: bool) -> Result<(), FueraDeCapacidad> {
        match self.bits.get_mut(i) {
            Some(b) => {
                *b = valor;
                Ok(())
            }
            None => Err(FueraDeCapacidad),
        }
    }

    pub fn count_ones(&self) -> usize {
        let mut n = 0;
        for i in 0..self.bits.len() {
            if self.bits[i] {
                n += 1;
            }
        }
        n
    }
}

impl<const N: usize> Default for SszBitlist<N> {
    fn default() -> Self {
        Self::new()
    }
}
