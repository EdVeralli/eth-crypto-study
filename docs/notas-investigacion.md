# Notas de investigacion - ethereum/cryptography-specs

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

La proof importa la spec y referencia sus funciones por nombre. Si la spec cambia, la proof deja de compilar.

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
  · exact beq_iff'.mp hbeq
  · cases h
```

El mecanismo de enlace:
1. **`import`** - la proof importa `EthCryptographySpecs.Bls.Compress`
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
| Compresion G1 round-trip | Proofs/Bls/Compress | Probado |
| Fp.sqrt soundness & completeness | Proofs/Bls/Compress | Probado |
| MSM correctness | Proofs/Bls/G1Msm | Probado |
| G1 orden del subgrupo | Proofs/Bls/G1Order | Probado |
| FFT / iFFT round-trip | Proofs/Kzg/Fft | Probado |
| Ceremony pairing checks (soundness) | Proofs/Kzg/CeremonyChecks | Parcial* |
| Bit-reversal involucion | Proofs/Kzg/BitReversal | Probado |
| BLAKE2s tweak hash | Proofs/Xmss/TweakHash | Probado |

*CeremonyChecks asume `ConcreteBlsLaws` (bilinealidad, no-degeneracion, fidelidad de mul escalar) que aun no estan probadas para la implementacion ejecutable.

## Orden de lectura sugerido

1. `Bls/Fp.lean` - como se modela un campo finito con `Fin p`
2. `Bls/G1.lean` - aritmetica de curva (add, double, msm) en Jacobiana
3. `Bls/Compress.lean` - serializacion y round-trip
4. `Kzg/Fft.lean` - Cooley-Tukey sobre Fr
5. `Kzg/Core.lean` - la superficie publica: commit, prove, verify
6. `Proofs/Bls/Compress.lean` - ejemplo de como se prueba un round-trip
7. `Proofs/Kzg/CeremonyChecks.lean` - el teorema mas ambicioso del repo

---

## Estado del build y proximos pasos

### Compilacion (pendiente)

El proyecto necesita compilarse antes de poder usar los Python bindings.
La compilacion parcial avanzo (34 archivos .c.o.export generados) pero
no completo. Pasos para retomar despues del reinicio:

```bash
cd ~/cryptography-specs
lake exe cache get        # solo si se borro .lake/
lake build                # continua desde donde quedo
```

El build puede tardar 10-20 minutos la primera vez (compila ~60 archivos
Lean contra Mathlib v4.29.1). Una vez completado:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e '.[test]'
```

Despues se puede llamar BLS desde Python:

```python
from eth_cryptography_specs import bls
# Ejemplo: verificar firma, comprimir punto G1, etc.
```

### Repos

- **Repo original (solo lectura):** `~/cryptography-specs` — clon de `ethereum/cryptography-specs`
- **Tu repo personal:** `~/eth-crypto-study` — copia independiente en `github.com/EdVeralli/eth-crypto-study`
- **Docs generados:** `~/eth-crypto-study/docs/` — mapa interactivo + estas notas
