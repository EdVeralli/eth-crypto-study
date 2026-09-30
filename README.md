# eth-crypto-study

Copia de estudio de [`ethereum/cryptography-specs`](https://github.com/ethereum/cryptography-specs),
las especificaciones de criptografía de Ethereum escritas en Lean 4.

Este repo es **mío** (`github.com/EdVeralli/eth-crypto-study`) y es el único al
que se commitea y se pushea. El clon del repo original vive en
`~/cryptography-specs` y es **solo lectura**: su `origin` apunta a
`ethereum/cryptography-specs`, así que ahí no se pushea nada.

Base: upstream `09deaff` (23 sept 2026). El README original del proyecto quedó
en [`docs/README-upstream.md`](docs/README-upstream.md).

## Qué estamos haciendo

Entender cómo Ethereum especifica su criptografía en Lean 4 —y comprobar que
esa spec realmente corre y reproduce los vectores oficiales— en tres frentes:

- **BLS12-381** (`EthCryptographySpecs/Bls/`) — campos, curva, pairing, firmas
- **KZG** (`EthCryptographySpecs/Kzg/`) — compromisos polinomiales para blobs (EIP-4844)
- **XMSS** (`EthCryptographySpecs/Xmss/`) — firmas hash-based post-cuánticas, en desarrollo upstream

El repo separa a propósito la **spec** ejecutable (se compila a C y se linkea en
una extensión de Python) de las **proofs** (teoremas sobre Mathlib que solo se
type-checkean). El detalle de cómo se enlazan está en
[`docs/notas-investigacion.md`](docs/notas-investigacion.md).

## Estado: lo que ya está cerrado

| Paso | Estado |
|---|---|
| `lake build` | Completo — 3444 jobs, exit 0, sin errores ni warnings |
| `pip install -e '.[test]'` | Completo — extensión C compilada y enlazada |
| BLS desde Python | Funciona (`from eth_cryptography_specs import bls`) |
| Verificación cruzada contra `py_ecc` | Pasa — agregación coincide byte a byte (`docs/bls_smoke.py`) |
| Suite completa de 364 vectores | **Pasó — 0 diferencias contra git** (2:57:50) |
| Documentación del repo | Notas + mapa interactivo en `docs/` |

El `git status` limpio después de correr la suite es el resultado importante:
`pytest` acá no testea, **regenera** los 364 `tests/**/data.yaml` commiteados,
así que reproducirlos byte a byte es la señal de que la spec sigue dando los
mismos bytes. Es un test de regresión invertido.

La etapa de infraestructura está terminada: no queda nada de "hacerlo andar".

## Qué falta

Todo lo que sigue es estudio y verificación, en orden sugerido:

1. **Leer los `.lean` en orden** — la secuencia de 7 archivos al final de
   `docs/notas-investigacion.md` (de `Bls/Fp.lean` hasta
   `Proofs/Kzg/CeremonyChecks.lean`).
2. **`Proofs/Kzg/CeremonyChecks.lean`** — el teorema más ambicioso del repo y el
   único hueco conocido: asume la estructura `ConcreteBlsLaws` (bilinealidad,
   no-degeneración, fidelidad del mul escalar) que todavía **no** está probada
   para la implementación ejecutable. Entender qué haría falta para cerrarla.
3. **Los `native_decide` que quedan** — no hay ningún `sorry` en el repo, pero sí
   pruebas delegadas al evaluador compilado, fuera del kernel:
   `Proofs/Bls/Compress.lean:319` (uncompress del punto al infinito) y 7 en
   `Proofs/Xmss/Blake2s.lean`. Upstream lo tiene abierto como issue #28.
4. **Superficie de KZG desde Python** — ya exploramos BLS (solo expone
   `eth_aggregate_pubkeys` y `eth_fast_aggregate_verify`, sin firmado); falta
   hacer lo mismo con `eth_cryptography_specs.kzg` y sus 12 handlers.
5. **Seguirle el paso a XMSS upstream** — al 29 sept 2026 upstream ya mergeó el
   encoding target-sum (#33), su prueba (#35) y la firma Winternitz (#37), y
   tiene en review el árbol de Merkle (#38) y la verificación (#40). Pendientes
   allá: keygen + firma (#20), sign-then-verify (#21), SSZ (#22/#23), vectores
   (#25), exports C/Python (#24) y CI (#11/#30).
6. **Re-sincronizar esta copia** si queremos estudiar XMSS completo: esta copia
   está en `09deaff` y upstream ya va por `02e5e78`. Traer los commits nuevos
   acá (merge desde el clon de lectura), nunca al revés.

## Entorno

El venv y el build ya existen, no hay que recrearlos. Viven en el clon de
lectura, `~/cryptography-specs`:

```bash
cd ~/cryptography-specs
.venv/bin/python -c "from eth_cryptography_specs import bls; print(dir(bls))"
.venv/bin/python ~/eth-crypto-study/docs/bls_smoke.py
```

Si se borra `.lake/`: `lake exe cache get && lake build`.
Si se borra `.venv/`: `pip install -e '.[test]'` (dispara `lake build` vía `setup.py`).

Para correr la suite de vectores, dos cosas aprendidas a golpes —enchufada, con
la tapa abierta y con `caffeinate`, o la Mac duerme y no avanza; y no extrapolar
el ritmo, porque la `lru_cache` de los fixtures hace que los primeros casos de
cada handler paguen todo el cómputo:

```bash
cd ~/cryptography-specs
caffeinate -i -s .venv/bin/python -m pytest -q     # completa, ~3 h
caffeinate -i -s -w <PID>                          # si ya está corriendo
```

## Cómo retomar (incluido desde la app de Claude para Mac)

1. Abrir la carpeta `~/eth-crypto-study`.
2. Leer [`docs/RETOMAR.md`](docs/RETOMAR.md) — el estado detallado y los comandos.
3. Elegir una de las tareas de **Qué falta** de acá arriba.
4. Recordar las dos reglas: se commitea y pushea **solo** en este repo, y
   `~/cryptography-specs` se usa únicamente para leer y compilar.

## Documentación generada

- [`docs/RETOMAR.md`](docs/RETOMAR.md) — dónde quedamos y cómo volver a arrancar
- [`docs/notas-investigacion.md`](docs/notas-investigacion.md) — todo lo aprendido del repo
- [`docs/architecture-map.html`](docs/architecture-map.html) — mapa interactivo de módulos
- [`docs/bls_smoke.py`](docs/bls_smoke.py) — verificación end-to-end de BLS contra `py_ecc`
- [`docs/README-upstream.md`](docs/README-upstream.md) — README original del proyecto
