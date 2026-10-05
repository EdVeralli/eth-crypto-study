# Notas de investigacion - ethereum/cryptography-specs

_Revisado 2026-10-05: rutas, orden de estudio y tabla de propiedades alineados con el README y el mapa completo._

## Estructura general

El repo tiene tres modulos criptograficos escritos en Lean 4:

- **BLS12-381** (`EthCryptographySpecs/Bls/`) - Curva eliptica, campos finitos, pairing, firmas
- **KZG** (`EthCryptographySpecs/Kzg/`) - Compromisos polinomiales para blobs (EIP-4844)
- **XMSS** (`EthCryptographySpecs/Xmss/`) - Firmas hash-based post-quantum (en desarrollo)

KZG depende de BLS. XMSS usa BLAKE2s como hash.

## Specs vs Proofs

El repo separa deliberadamente el codigo ejecutable de los teoremas:

### Spec (ejecutable)
- Definiciones con `def` y `structure`
- Se compila a C via Lean compiler
- Se linkea en la extension Python (`bindings/`)
- `precompileModules := true` en lakefile.lean
- Prioriza claridad, no performance

### Proofs (verificacion)
- Teoremas con `theorem`
- Solo genera `.olean` (type-checking)
- No se linkea en Python
- `precompileModules := false` en lakefile.lean
- Depende de Mathlib v4.29.1

## Como se enlazan spec y proof

El teorema importa la spec y referencia sus funciones por nombre. Si la spec cambia, el teorema deja de compilar.

### Ejemplo concreto: Fp.sqrt

**Spec** (`Bls/Fp.lean:79`):
```lean
def sqrt (a : Fp) : Except BlsError Fp :=
  let cand := powNat a ((modulus + 1) / 4)
  if (cand * cand).beq a then .ok cand else .error .notASquare
```

**Proof** (`Proofs/Bls/Compress.lean:32`):
```lean
theorem sqrt_ok {a c : Fp} (h : Fp.sqrt a = .ok c) :
    (c : ZMod Fp.modulus) * c = a := by
  rw [Fp.sqrt] at h    -- despliega la definicion de sqrt
  split at h
  · rename_i hbeq
    cases h
    exact beq_iff'.mp hbeq
  · cases h
```

El mecanismo de enlace:
1. **`import`** - el archivo de teoremas importa `EthCryptographySpecs.Bls.Compress`
2. **`namespace`** - se ubica en el mismo namespace que la spec
3. **`rw [Fp.sqrt]`** - Lean despliega la definicion de sqrt dentro de la hipotesis para razonar sobre su estructura

`rw` no modifica la spec. Es una operacion dentro de la demostracion que le dice a Lean "mira adentro de esa funcion".

## Por que spec-first (y no proof-first)

```
Estandar (RFC/EIP) --> Spec (codigo) --> Proof (verificacion)
```

Las specs criptograficas de Ethereum ya estan publicadas y otras implementaciones las siguen al pie de la letra. Si el codigo se derivara de un teorema (como en Coq extraction), podria ser matematicamente correcto pero producir resultados distintos a los de otros clientes, rompiendo la interoperabilidad de la red.

La alternativa (proof-first / extraction):
```
Teorema --> extraccion --> Codigo
```
El codigo es correcto por construccion, pero puede no coincidir con el estandar externo.

## Propiedades demostradas

| Propiedad | Archivo | Estado |
|---|---|---|
| Compresion G1 round-trip | Proofs/Bls/Compress | Probado** |
| Fp.sqrt soundness & completeness | Proofs/Bls/Compress | Probado |
| MSM correctness | Proofs/Bls/G1Msm | Probado |
| G1 orden del subgrupo | Proofs/Bls/G1Order | Probado |
| FFT / iFFT round-trip | Proofs/Kzg/FftInverse | Probado |
| Ceremony pairing checks (soundness) | Proofs/Kzg/CeremonyChecks | Parcial* |
| Bit-reversal involucion | Proofs/Kzg/BitReversal | Probado |
| BLAKE2s tweak hash | Proofs/Xmss/TweakHash | Probado |

*CeremonyChecks asume `ConcreteBlsLaws` (bilinealidad, no-degeneracion, fidelidad de mul escalar) que aun no estan probadas para la implementacion ejecutable. Es el hueco mas importante del repo.

**Probado, pero depende de *native axioms*: pasos verificados por codigo compilado (`bv_decide`, `native_decide`) en vez del kernel. 10 de los 492 teoremas los tienen, todos en `Proofs/Bls/Compress.lean` y `Proofs/Xmss/Blake2s.lean`; ninguno en KZG. Lista y explicacion: `docs/native_axioms.lean` y el mapa completo, "Donde la separacion no es perfecta". No hay ningun `sorry` en el repo.

## Orden de estudio

El orden vive en un solo lugar: la tabla de pisos del README ("Empeza por
aca") y el mapa completo. Resumen: Fp -> G1 -> Compress -> Kzg/Fft y Core ->
Proofs/Kzg/CeremonyChecks, cada piso con su archivo de spec y sus teoremas.

---

## Estado del build y ejecucion desde Python

_Actualizado 2026-09-25: el build se completo y BLS ya corre desde Python._

### Compilacion (completa)

```
lake build  ->  Build completed successfully (3444 jobs)
```

Exit code 0, sin errores ni warnings. De esos 3444 jobs, la gran mayoria es
Mathlib v4.29.1; los ultimos son los modulos propios del repo
(`EthCryptographySpecs.Proofs.Xmss.Blake2s`, `...TweakHash`, etc.).

El build dejo 35 archivos `.c.o.export` en `.lake/build/ir/` y ~2900 `.olean`.
Los `.c.o.export` son los que se linkean en la extension Python; los `.olean`
de `Proofs/` solo existen para el type-checking y no se linkean.

### Bindings de Python (instalados)

```bash
cd ~/eth-crypto-study
python3 -m venv .venv                 # Python 3.11.7
.venv/bin/pip install -e '.[test]'
```

Que hace ese `pip install -e` por dentro (`setup.py`):

1. Corre `lake build` de nuevo (idempotente si ya esta compilado)
2. Junta los 35 `.c.o.export` con `glob`
3. Los linkea dentro de la extension `eth_cryptography_specs._native`
   junto con `bindings/python/{module,kzg,bls}.c`
4. Enlaza **dinamicamente** contra `libleanshared` del toolchain activo, y
   **estaticamente** contra `libgmp.a` / `libuv.a`
5. En macOS arrastra `libc++` (porque `libleancpp` es C++); en Linux seria
   `stdc++` + `pthread` + `dl` + `m`
6. Configura `runtime_library_dirs` (RPATH) para que en desarrollo local
   encuentre `libleanshared` sin necesidad de auditwheel/delocate

O sea: el codigo criptografico que corre desde Python **es el compilado desde
Lean**, no una reimplementacion. Por eso hace falta el toolchain de Lean para
un build local (una wheel distribuida no, porque trae el runtime adentro).

### Verificacion end-to-end de BLS

Script en `docs/bls_smoke.py`. Usa `py_ecc.bls.G2ProofOfPossession` como
implementacion de referencia independiente para generar claves y firmas, y
compara contra el spec de Lean:

```
BYTES_PER_PUBKEY   : 48
BYTES_PER_SIGNATURE: 96

eth_aggregate_pubkeys -> a095608b35495ca05002b7b5966729dd...48fca969
py_ecc  _AggregatePKs -> a095608b35495ca05002b7b5966729dd...48fca969
match: True

eth_fast_aggregate_verify (valid sig)   : True
eth_fast_aggregate_verify (wrong msg)   : False
eth_fast_aggregate_verify ([], inf sig) : True
```

La agregacion de pubkeys coincide **byte a byte** con py_ecc. La verificacion
acepta la firma agregada valida y rechaza el mensaje alterado. El tercer caso
es la regla especial de la spec de consenso: lista de pubkeys vacia con la
firma en el punto al infinito de G2 (`0xc0` + 95 ceros) se considera valida.

### Superficie expuesta a Python

```python
>>> from eth_cryptography_specs import bls
>>> [n for n in dir(bls) if not n.startswith('_')]
['BYTES_PER_PUBKEY', 'BYTES_PER_SIGNATURE',
 'eth_aggregate_pubkeys', 'eth_fast_aggregate_verify']
```

Es una superficie deliberadamente chica. **No expone firmado** (`Sign`) ni
derivacion de claves (`SkToPk`) — son operaciones con clave privada que no le
hacen falta a un cliente de consenso, que solo verifica. Para generar material
de prueba hay que usar py_ecc.

### La suite de tests no es una suite de tests

`pytest` en este repo es un **generador de vectores de prueba**. Cada test
llama al spec de Lean y escribe el resultado a
`tests/<spec>/<handler>/<case>/data.yaml` via `bindings/python/tests/dumper.py`.

Hay 364 de esos `data.yaml`, **todos trackeados en git**. Corriendo la suite
se regeneran en el lugar, asi que `git status` limpio despues de correrla es
justamente la señal de que el spec de Lean sigue produciendo los mismos bytes
que cuando se commitearon los vectores. Es un test de regresion invertido.

**Resultado (2026-09-28): la suite completa paso.**

```
364 passed in 10670.43s (2:57:50)
exit code 0
git status: limpio, diff en tests/ vacio
```

Los 364 vectores se regeneraron **byte a byte identicos** a los commiteados,
en los 14 handlers de BLS y KZG:

| Handler | Casos |
|---|---|
| `bls/eth_aggregate_pubkeys` | 8 |
| `bls/eth_fast_aggregate_verify` | 12 |
| `kzg/blob_to_kzg_commitment` | 11 |
| `kzg/compute_blob_kzg_proof` | 15 |
| `kzg/compute_cells` | 11 |
| `kzg/compute_cells_and_kzg_proofs` | 11 |
| `kzg/compute_challenge` | 9 |
| `kzg/compute_kzg_proof` | 52 |
| `kzg/compute_verify_cell_kzg_proof_batch_challenge` | 10 |
| `kzg/recover_cells_and_kzg_proofs` | 18 |
| `kzg/verify_blob_kzg_proof` | 29 |
| `kzg/verify_blob_kzg_proof_batch` | 24 |
| `kzg/verify_cell_kzg_proof_batch` | 32 |
| `kzg/verify_kzg_proof` | 122 |
| **Total** | **364** |

### Dos lecciones sobre el costo de correrla

**1. La Mac dormia, no era lentitud.** Durante dos dias y medio la suite
avanzo 2 vectores. El diagnostico no era KZG lento sino gestion de energia:
`kern.waketime` y `pmset -g log` mostraban ciclos de 'Maintenance Sleep' cada
~15 min a bateria. La prueba numerica: el proceso acumulaba **65 min de CPU en
63 horas de reloj** (1.7%). La solucion, sin perder el trabajo hecho:

```bash
caffeinate -i -s -w <PID>   # candado atado al proceso; se suelta cuando termina
```

Con eso el mismo proceso paso a 97-99% de CPU sostenido y las ~2h30 de computo
restantes salieron en 97 minutos de reloj. Importa estar enchufado: `-s` solo
tiene efecto con AC. Y `caffeinate` **no** impide el clamshell sleep — hay que
dejar la tapa abierta.

**2. La `lru_cache` domina el ritmo, y arruina cualquier extrapolacion.**
Los fixtures de KZG estan cacheados (`cached_cells_and_proofs`,
`cached_commitment`, `cached_kzg_proof`, `cached_blob_kzg_proof`). Como los
handlers comparten los mismos blobs, **los primeros casos de cada handler
pagan todo el computo y el resto viaja gratis**. Medido:

| Handler | Primeros casos | Casos restantes |
|---|---|---|
| `recover_cells_and_kzg_proofs` | 3 casos en ~30 min | los 15 restantes en ~4 min |
| `verify_cell_kzg_proof_batch` | 5 casos en ~20 min | los 27 restantes en ~4 min |

Conclusion practica: un promedio medido al principio de un handler
sobreestima el total por uno o dos ordenes de magnitud. No sirve extrapolar
linealmente en este repo.

El costo real de fondo sigue siendo el que anticipaba la seccion
"Specs vs Proofs": KZG evaluado en Lean sin optimizaciones, porque la spec
prioriza claridad sobre performance.

### Como correr solo una parte

Regenerar un handler suelto, sin las 3 horas completas:

```bash
cd ~/eth-crypto-study
caffeinate -i -s .venv/bin/python -m pytest bindings/python/tests/kzg -k verify_kzg_proof
```

Los handlers baratos (`verify_kzg_proof`, `compute_challenge`) tardan minutos.
Los caros son los tres que tocan celdas: `compute_cells_and_kzg_proofs`,
`recover_cells_and_kzg_proofs`, `verify_cell_kzg_proof_batch`.

### Repos

- **Repo original (solo lectura):** `~/cryptography-specs` — clon de `ethereum/cryptography-specs`
- **Tu repo personal:** `~/eth-crypto-study` — copia independiente en `github.com/EdVeralli/eth-crypto-study`
- **Docs generados:** `~/eth-crypto-study/docs/` — mapa interactivo + estas notas
