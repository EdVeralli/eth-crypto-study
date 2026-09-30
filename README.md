# eth-crypto-study

Estudio de cómo Ethereum especifica su criptografía (BLS12-381, KZG, XMSS)
en Lean 4: una parte es código que **se ejecuta** y otra son **teoremas** que
demuestran que ese código es correcto.

> **Repo original:** [`ethereum/cryptography-specs`](https://github.com/ethereum/cryptography-specs),
> las especificaciones oficiales de criptografía de Ethereum escritas en Lean 4.
> Este repo es una copia de estudio tomada del commit `09deaff` (23 sept 2026),
> a la que le agregamos mapas, guías y notas de estudio.

## Empezá por acá

Antes de mirar código, abrí estas tres páginas en este orden:

1. **[Mapa completo](docs/mapa-completo.html)**: el big picture. Muestra cómo
   una llamada desde Python baja por el binding C hasta la spec en Lean, qué
   partes se ejecutan (verde) y cuáles son teoremas (violeta), archivo por
   archivo.
2. **[Mapa de arquitectura](docs/architecture-map.html)**: los módulos por
   dentro. Cubre BLS, KZG y XMSS archivo por archivo (se despliegan con un
   clic), por qué el repo escribe primero la spec y después la prueba
   (spec-first) y un ejemplo de cómo una prueba se engancha con el código.
3. **[Fp.lean paso a paso](docs/fp-paso-a-paso.html)**: la primera guía de
   estudio. Explica el campo finito, que es la base de todo, línea por línea
   y con sus pruebas.

El mapa es la vista de arriba y cada guía baja a un archivo. Se estudian de
abajo hacia arriba, porque cada piso usa al anterior:

| Piso | Archivo | Guía |
|---|---|---|
| 1 | `Bls/Fp.lean` + `Proofs/Bls/FpZMod.lean` | ✅ [fp-paso-a-paso](docs/fp-paso-a-paso.html) |
| 2 | `Bls/G1.lean` + `G1Group` / `G1Order` / `G1Msm` | próxima |
| 3 | `Bls/Compress.lean` | pendiente |
| 4 | `Kzg/Fft.lean`, `Kzg/Core.lean` | pendiente |
| 5 | `Proofs/Kzg/CeremonyChecks.lean` | pendiente |

### Cómo ver las páginas

Son archivos HTML. Si los abrís desde la web de GitHub vas a ver el código
fuente y no la página, así que hay que bajar el repo y abrirlos con un
navegador:

```bash
git clone https://github.com/EdVeralli/eth-crypto-study.git
cd eth-crypto-study
open docs/mapa-completo.html        # macOS
# xdg-open docs/mapa-completo.html  # Linux
# start docs\mapa-completo.html     # Windows
```

También podés hacer doble clic en el archivo desde el explorador. Hace falta
conexión a internet: los diagramas se dibujan con Mermaid y las tipografías se
cargan desde la web.

---

## Sobre este repo

Copia de estudio de [`ethereum/cryptography-specs`](https://github.com/ethereum/cryptography-specs),
las especificaciones de criptografía de Ethereum escritas en Lean 4.

Este repo es **mío** (`github.com/EdVeralli/eth-crypto-study`) y es el único al
que se commitea y se pushea. Es **autocontenido**: tiene las fuentes Lean, el
build, los bindings de Python y los 364 vectores, así que es la única carpeta de
trabajo necesaria.

El clon del repo original vive en `~/cryptography-specs` y es **solo lectura**:
su `origin` apunta a `ethereum/cryptography-specs`, así que ahí no se pushea
nada. Solo se usa para traer commits nuevos de upstream.

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

1. **Estudiar los `.lean` piso por piso**: seguir la tabla de
   [Empezá por acá](#empezá-por-acá), con una guía HTML por piso. El piso 1
   (`Bls/Fp.lean`) ya está hecho y el próximo es `Bls/G1.lean`.
2. **`Proofs/Kzg/CeremonyChecks.lean`** — el teorema más ambicioso del repo y el
   único hueco conocido: asume la estructura `ConcreteBlsLaws` (bilinealidad,
   no-degeneración, fidelidad del mul escalar) que todavía **no** está probada
   para la implementación ejecutable. Entender qué haría falta para cerrarla.
3. **Los `native_decide` que quedan** — no hay ningún `sorry` en el repo, pero sí
   pruebas delegadas al evaluador compilado, fuera del kernel:
   `Proofs/Bls/Compress.lean:319` (uncompress del punto al infinito) y 7 en
   `Proofs/Xmss/Blake2s.lean`. Upstream lo tiene abierto como issue #28.
4. **Ejercitar KZG desde Python** — la superficie ya está a la vista: 12
   funciones (`blob_to_kzg_commitment`, `compute_kzg_proof`,
   `verify_blob_kzg_proof_batch`, `recover_cells_and_kzg_proofs`, …) y 8
   constantes. Falta un smoke test propio al estilo de `docs/bls_smoke.py`,
   idealmente con blob → commitment → proof → verify de punta a punta.
5. **Seguirle el paso a XMSS upstream** — al 29 sept 2026 upstream ya mergeó el
   encoding target-sum (#33), su prueba (#35) y la firma Winternitz (#37), y
   tiene en review el árbol de Merkle (#38) y la verificación (#40). Pendientes
   allá: keygen + firma (#20), sign-then-verify (#21), SSZ (#22/#23), vectores
   (#25), exports C/Python (#24) y CI (#11/#30).
6. **Re-sincronizar esta copia** si queremos estudiar XMSS completo: esta copia
   está en `09deaff` y upstream ya va por `02e5e78`. Traer los commits nuevos
   acá (merge desde el clon de lectura), nunca al revés.

## Entorno

Todo vive en esta carpeta y ya está construido — no hay que recrear nada:

```bash
cd ~/eth-crypto-study
lake build                                          # verde: 3444 jobs
.venv/bin/python docs/bls_smoke.py                  # ALL CHECKS PASSED
.venv/bin/python -c "from eth_cryptography_specs import bls, kzg"
```

Si se borra `.lake/`: `lake exe cache get && lake build`.
Si se borra `.venv/`: `python3 -m venv .venv && .venv/bin/pip install -e '.[test]'`
(dispara `lake build` vía `setup.py`; con el build hecho tarda ~1 min).

Para correr la suite de vectores, dos cosas aprendidas a golpes —enchufada, con
la tapa abierta y con `caffeinate`, o la Mac duerme y no avanza; y no extrapolar
el ritmo, porque la `lru_cache` de los fixtures hace que los primeros casos de
cada handler paguen todo el cómputo:

```bash
cd ~/eth-crypto-study
caffeinate -i -s .venv/bin/python -m pytest -q      # completa, ~3 h
caffeinate -i -s .venv/bin/python -m pytest bindings/python/tests/kzg -k compute_challenge
caffeinate -i -s -w <PID>                           # si ya está corriendo
```

## Cómo retomar (incluido desde la app de Claude para Mac)

1. Pasarle **`/Users/eduardoveralli/eth-crypto-study`** como carpeta de trabajo.
   Es la única que hace falta: acá están las fuentes, el build, el venv y los
   vectores. No hace falta agregar `~/cryptography-specs`.
2. Leer [`docs/RETOMAR.md`](docs/RETOMAR.md) — el estado detallado y los comandos.
3. Elegir una de las tareas de **Qué falta** de acá arriba.
4. Recordar la regla: se commitea y pushea **solo** en este repo. Nunca a
   `ethereum/cryptography-specs`.

## Documentación generada

- [`docs/mapa-completo.html`](docs/mapa-completo.html): big picture, spec ejecutable vs teoremas, pisos de estudio
- [`docs/fp-paso-a-paso.html`](docs/fp-paso-a-paso.html): guía del piso 1, `Bls/Fp.lean` y sus pruebas
- [`docs/RETOMAR.md`](docs/RETOMAR.md) — dónde quedamos y cómo volver a arrancar
- [`docs/notas-investigacion.md`](docs/notas-investigacion.md) — todo lo aprendido del repo
- [`docs/architecture-map.html`](docs/architecture-map.html) — mapa de arquitectura: módulos por dentro y por qué spec-first
- [`docs/bls_smoke.py`](docs/bls_smoke.py) — verificación end-to-end de BLS contra `py_ecc`
- [`docs/README-upstream.md`](docs/README-upstream.md) — README original del proyecto
