//! `MapaVotos`: el mapa de votos como lista de pares.
//!
//! ESTO NO ES CODIGO DE ETHLAMBDA, y es el cambio mas grande que la propuesta
//! les pide.
//!
//! POR QUE. En el original, `justifications` es un `HashMap<H256, Vec<bool>>`.
//! La STF lo RECORRE en tres lugares (`retain`, `keys`, indexacion), y recorrer
//! un `HashMap` necesita un iterador -- que es justo lo que Aeneas no traduce.
//! Con indices no se puede: un `HashMap` no tiene orden.
//!
//! QUE CUESTA. La busqueda pasa de constante a lineal. En la practica este mapa
//! tiene las raices esperando finalizacion, que son pocas; pero el tipo de
//! `justifications_roots` permite hasta HISTORICAL_ROOTS_LIMIT entradas, asi
//! que en el peor caso --finalizacion trabada mucho tiempo-- es una regresion
//! de rendimiento real. Es un costo que la propuesta declara, no esconde.
//!
//! QUE NO CAMBIA. `root_to_slot` sigue siendo un `HashMap`: se construye con
//! hasta 262.144 entradas y solo se consulta con `get`, nunca se recorre. Ahi
//! una lista de pares seria cuadratica y no se justifica. Del lado de Lean
//! alcanza con modelar `new`, `insert` y `get`, que no llevan closures.

use crate::tipos::H256;

/// Mapa de raiz a lista de votos, como dos vectores paralelos.
///
/// Paralelos y no un `Vec<(H256, Vec<bool>)>` a proposito: menos destructuracion
/// de tuplas, que es una cosa menos que la cadena de herramientas tiene que
/// digerir.
#[derive(Clone, PartialEq)]
pub struct MapaVotos {
    claves: Vec<H256>,
    valores: Vec<Vec<bool>>,
}

impl MapaVotos {
    pub fn nuevo() -> Self {
        Self {
            claves: Vec::new(),
            valores: Vec::new(),
        }
    }

    pub fn largo(&self) -> usize {
        self.claves.len()
    }

    pub fn vacio(&self) -> bool {
        self.claves.is_empty()
    }

    /// La clave `i`, POR COPIA.
    ///
    /// Devuelve `H256` y no `&H256` a proposito. Ligar una referencia sacada
    /// de una coleccion adentro de un loop que ademas muta otra coleccion hace
    /// fallar a Aeneas con "Internal error". Por separado cada cosa pasa; las
    /// dos juntas no.
    pub fn clave(&self, i: usize) -> H256 {
        match self.claves.get(i) {
            Some(c) => *c,
            None => H256::ZERO,
        }
    }

    /// Los votos de la entrada `i`, por copia. Mismo motivo.
    pub fn votos(&self, i: usize) -> Vec<bool> {
        match self.valores.get(i) {
            Some(v) => v.clone(),
            None => Vec::new(),
        }
    }

    /// Busqueda lineal. Este es el costo del cambio.
    pub fn posicion(&self, k: &H256) -> Option<usize> {
        let mut i = 0;
        let mut encontrado: Option<usize> = None;
        while i < self.claves.len() {
            if encontrado.is_none() {
                match self.claves.get(i) {
                    Some(c) => {
                        if c == k {
                            encontrado = Some(i);
                        }
                    }
                    None => {}
                }
            }
            i += 1;
        }
        encontrado
    }

    /// Agrega la clave con esos votos si no estaba. Si estaba, no la toca.
    /// Devuelve su posicion.
    pub fn poner_si_falta(&mut self, k: H256, v: Vec<bool>) -> usize {
        match self.posicion(&k) {
            Some(p) => p,
            None => {
                self.claves.push(k);
                self.valores.push(v);
                self.claves.len() - 1
            }
        }
    }

    /// Marca que el validador `j` voto, en la entrada `p`.
    pub fn votar(&mut self, p: usize, j: usize) {
        match self.valores.get_mut(p) {
            Some(votos) => match votos.get_mut(j) {
                Some(b) => *b = true,
                None => {}
            },
            None => {}
        }
    }

    /// Cuantos votos tiene la entrada `p`.
    pub fn largo_votos(&self, p: usize) -> usize {
        match self.valores.get(p) {
            Some(votos) => votos.len(),
            None => 0,
        }
    }

    /// Si el validador `i` voto en la entrada `p`.
    ///
    /// Accede a traves de la coleccion cada vez, en vez de sacar una
    /// referencia y sostenerla: un borrow hacia adentro de una coleccion
    /// retenido a lo largo de un loop hace fallar a Aeneas.
    pub fn voto(&self, p: usize, i: usize) -> bool {
        match self.valores.get(p) {
            Some(votos) => match votos.get(i) {
                Some(true) => true,
                _ => false,
            },
            None => false,
        }
    }

    /// Cuantos votaron en la entrada `p`.
    pub fn cuenta_votos(&self, p: usize) -> usize {
        let mut n = 0;
        let largo = self.largo_votos(p);
        for i in 0..largo {
            if self.voto(p, i) {
                n += 1;
            }
        }
        n
    }

    /// Devuelve el mapa sin la clave `k`.
    ///
    /// Reconstruye en vez de usar `Vec::remove`, que no sabemos si traduce.
    pub fn sin(&self, k: &H256) -> MapaVotos {
        let mut m = MapaVotos::nuevo();
        for i in 0..self.claves.len() {
            let c = self.clave(i);
            if c != *k {
                m.claves.push(c);
                m.valores.push(self.votos(i));
            }
        }
        m
    }

    /// Devuelve el mapa quedandose solo con las posiciones marcadas en
    /// `conservar`.
    ///
    /// Reemplaza al `retain` con closure del original: el que llama decide
    /// afuera, con un loop, cuales se quedan.
    pub fn filtrado(&self, conservar: &[bool]) -> MapaVotos {
        let mut m = MapaVotos::nuevo();
        for i in 0..self.claves.len() {
            if bandera(conservar, i) {
                m.claves.push(self.clave(i));
                m.valores.push(self.votos(i));
            }
        }
        m
    }

    /// Las claves ordenadas, para que todos los nodos produzcan la misma
    /// representacion del estado.
    ///
    /// Ordenamiento por insercion escrito a mano: `Vec::sort` usa comparadores
    /// y no esta en los modelos de Aeneas.
    pub fn claves_ordenadas(&self) -> Vec<H256> {
        let mut salida: Vec<H256> = Vec::new();
        for i in 0..self.claves.len() {
            salida.push(self.clave(i));
        }
        // Insercion. El loop interno vive en `burbujear` para no anidar, y
        // todo va por copia para no ligar referencias.
        for i in 1..salida.len() {
            burbujear(&mut salida, i);
        }
        salida
    }
}

impl Default for MapaVotos {
    fn default() -> Self {
        Self::nuevo()
    }
}

/// Lee una bandera de un `&[bool]` por copia.
fn bandera(v: &[bool], i: usize) -> bool {
    match v.get(i) {
        Some(true) => true,
        _ => false,
    }
}

/// Lee una raiz de un `Vec<H256>` por copia.
fn raiz_de(v: &Vec<H256>, i: usize) -> H256 {
    match v.get(i) {
        Some(x) => *x,
        None => H256::ZERO,
    }
}

/// Baja el elemento `i` hasta su lugar. Es el loop interno del ordenamiento
/// por insercion, en funcion aparte porque un loop adentro de otro no traduce.
fn burbujear(v: &mut Vec<H256>, i: usize) {
    let mut j = i;
    let mut seguir = true;
    while seguir && j > 0 {
        let a = raiz_de(v, j - 1);
        let b = raiz_de(v, j);
        if b < a {
            match v.get_mut(j - 1) {
                Some(p) => *p = b,
                None => {}
            }
            match v.get_mut(j) {
                Some(p) => *p = a,
                None => {}
            }
            j -= 1;
        } else {
            seguir = false;
        }
    }
}
