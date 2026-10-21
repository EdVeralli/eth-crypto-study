# eth-crypto-study

Estudio de cómo Ethereum especifica su criptografía (BLS12-381, KZG, XMSS)
en Lean 4: una parte es código que **se ejecuta** y otra son **teoremas** que
demuestran que ese código es correcto.

> **Repo original:** [`ethereum/cryptography-specs`](https://github.com/ethereum/cryptography-specs),
> las especificaciones oficiales de criptografía de Ethereum escritas en Lean 4.
> Este repo es una copia de estudio tomada del commit `09deaff` (23 sept 2026),
> a la que le agregamos mapas, guías y notas de estudio.

## Empezá por acá

Antes de mirar código, abrí estas páginas en este orden:

0. **[La propuesta y su FODA](docs/propuesta-foda.html)**: qué proponen los
   autores del repo original, por qué, cómo lo implementan y cómo esperan que
   se use, con un análisis de fortalezas, oportunidades, debilidades y
   amenazas, y las preguntas abiertas con lo que encontramos al investigarlas.
   Cada afirmación dice de dónde sale.
1. **[Mapa completo](docs/mapa-completo.html)**: el big picture. Muestra cómo
   una llamada desde Python baja por el binding C hasta la spec en Lean, qué
   partes se ejecutan (verde) y cuáles son teoremas (violeta), archivo por
   archivo.
2. **[Mapa de arquitectura](docs/architecture-map.html)**: los módulos por
   dentro. Cubre BLS, KZG y XMSS archivo por archivo (se despliegan con un
   clic), por qué el repo escribe primero la spec y después los teoremas
   (spec-first) y un ejemplo de cómo un teorema se engancha con el código.
3. **[Fp.lean paso a paso](docs/fp-paso-a-paso.html)**: la primera guía de
   estudio. Explica el campo finito, que es la base de todo, línea por línea
   y con sus teoremas.

Y para ubicar este repo en el ecosistema: otros dos proyectos de la Ethereum
Foundation que usan Lean 4 para lo mismo, en otras capas. Cada página analiza
un repo distinto de los que leímos.

4. **[leanerSTFSpec](docs/leaner-stf-spec.html)** — analiza
   [`alexanderlhicks/leanerSTFSpec`](https://github.com/alexanderlhicks/leanerSTFSpec):
   el EVM y la transición de estado especificados en Lean, para validación
   *stateless* dentro de un zkVM. Resuelve de otra forma los dos problemas que
   más nos costaron: prohíbe los *native axioms* por regla verificada por
   máquina, y ata la spec al código que corre con un teorema de refinamiento en
   vez de compilarla. Nuestro repo es su referencia para curvas y pairings.
5. **[Verified zkEVM y el puente Rust ↔ Lean](docs/verified-zkevm.html)** —
   analiza [`github.com/verified-zkevm`](https://github.com/Verified-zkEVM), la
   organización paraguas de la Ethereum Foundation (meta 2027, catorce repos en
   tres frentes) y, adentro, cómo se conecta código Rust de producción con
   teoremas en Lean ([`hax`](https://github.com/cryspen/hax),
   [Aeneas](https://github.com/AeneasVerif/aeneas)), con ejemplos reales de
   traducción y del teorema que hay que escribir después.
6. **[gasper-lean4](docs/gasper-lean4.html)** — analiza
   [`NyxFoundation/gasper-lean4`](https://github.com/NyxFoundation/gasper-lean4):
   el **consenso** (Casper FFG: finalidad, quórums, slashing) demostrado en Lean,
   con el rigor más alto de todos (ni `Classical.choice`). Y los otros dos repos
   de la misma fundación:
   [`formal-leanSpec`](https://github.com/NyxFoundation/formal-leanSpec), donde el
   Lean **encontró dos bugs críticos** en la spec del consenso nuevo, y
   [`verity`](https://github.com/NyxFoundation/verity), un cliente que corre en
   devnet junto a ethlambda y ream.
7. **[verified-consensus](docs/verified-consensus.html)** — analiza
   [`fradamt/verified-consensus`](https://github.com/fradamt/verified-consensus):
   el **protocolo de consenso candidato** (*decoupled consensus*) formalizado entero
   por Francesco D'Amato. 334.092 líneas de Lean y 8.384 teoremas, pero sólo 6.897
   líneas que un humano tiene que leer. Es el único de los cinco que **ya trae
   escrito el enunciado** de qué significa que un consenso sea correcto — la pieza
   cara, si alguna vez queremos atar un cliente Rust a teoremas. El paper que
   formaliza es el que estudiamos en
   [`decoupled-consensus-apuntes`](https://github.com/EdVeralli/decoupled-consensus-apuntes).

Las ocho páginas responden las mismas tres preguntas en un bloque "Dónde se usa
Lean acá": si el Lean se compila, si se traduce código entre Lean y otro
lenguaje, y si algo de Lean está en el entorno de ejecución. Sirve para comparar
un repo con otro de un vistazo.

Y si querés los cinco comparados en un solo lugar, sin abrir página por página:
**[cuadro sinóptico de los repos](docs/repos-comparados.md)** — tabla maestra,
rigor comparado, dónde se usa Lean en cada uno, el hueco de cada uno, lo que se
repite en todos y una lista de qué no confundir con qué. Arranca por la sección 0,
que es la que le interesa a Pablo: cómo convive Lean con los otros lenguajes en
cada repo.

El mapa es la vista de arriba y cada guía baja a un archivo. Se estudian de
abajo hacia arriba, porque cada piso usa al anterior:

| Piso | Archivo | Guía |
|---|---|---|
| 1 | `Bls/Fp.lean` + `Proofs/Bls/FpZMod.lean` | ✅ [fp-paso-a-paso](docs/fp-paso-a-paso.html) |
| 2 | `Bls/G1.lean` + `G1Group` / `G1Order` / `G1Msm` | próxima |
| 3 | `Bls/Compress.lean` + `Proofs/Bls/Compress` | pendiente |
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
- **XMSS** (`EthCryptographySpecs/Xmss/`) — firmas hash-based post-cuánticas; en esta copia solo el hash y los tipos, upstream ya lo completó (ver [Qué falta](#qué-falta), punto 5)

El repo separa a propósito la **spec** ejecutable (se compila a C y se linkea en
una extensión de Python) de los **teoremas** (demostraciones que Lean solo
revisa, nunca ejecuta; se apoyan en Mathlib, la biblioteca matemática de Lean). El detalle de cómo se enlazan está en
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
   hueco más importante: asume la estructura `ConcreteBlsLaws` (leyes del pairing: bilinealidad,
   no-degeneración, fidelidad del mul escalar) que todavía **no** está probada
   para la implementación ejecutable. Entender qué haría falta para cerrarla.
3. **Los *native axioms* que quedan** — no hay ningún `sorry` en el repo, pero
   10 de los 492 teoremas (todos en `Proofs/Bls/Compress.lean` y
   `Proofs/Xmss/Blake2s.lean`) dependen de pasos verificados por código
   compilado en vez del kernel, el revisor central de Lean (`native_decide` y
   `bv_decide`). Uno es
   central: `uncompress_compress`. Mathlib no acepta teoremas así; upstream
   tiene abierto el issue #28 para sacar los dos `bv_decide` de Blake2s.
   Lista completa: `lake env lean docs/native_axioms.lean` (ver el mapa
   completo, "Dónde la separación no es perfecta").
4. **Ejercitar KZG desde Python** — la superficie ya está a la vista: 12
   funciones (`blob_to_kzg_commitment`, `compute_kzg_proof`,
   `verify_blob_kzg_proof_batch`, `recover_cells_and_kzg_proofs`, …) y 8
   constantes. Falta un smoke test propio al estilo de `docs/bls_smoke.py`,
   idealmente con blob → commitment → proof → verify de punta a punta.
5. **Seguirle el paso a XMSS upstream** — al 7 oct 2026 upstream (`d1331f0`, del 6 oct)
   ya tiene XMSS de punta a punta: encoding target-sum (#33, #35), firma
   Winternitz WOTS+C (#37), árbol de Merkle (#38), verificación (#40) y keygen +
   firma (#42), con el teorema de corrección `verify_keyGen_sign`
   (`Proofs/Xmss/Correctness.lean`). Cada PR trajo la spec y sus teoremas
   juntos. Ojo: sumó 4 `native_decide` nuevos (en `Proofs/Xmss/KeyGen.lean`,
   `Sign.lean` y `Verify.lean`) y sigue sin `@[export]` para XMSS, así que desde
   Python todavía no se puede llamar. El 6 oct sumó dos teoremas más: el tweak
   encoding es inyectivo (#43) y el tamaño del código target-sum (#44,
   `Proofs/Xmss/CodeSize.lean`); el número grande de ese último lo verifica el
   kernel con `decide +kernel`, no con `native_decide`. Pendientes allá: SSZ
   (#22/#23), vectores (#25), exports C/Python (#24) y CI (#11/#30). Nada de
   BLS, KZG, el binding ni el build cambió.
6. **Re-sincronizar esta copia** si queremos estudiar XMSS completo: esta copia
   está en `09deaff` y upstream ya va por `d1331f0` (8 commits, todos de XMSS:
   +6 archivos de spec, +8 de teoremas, unos 425 teoremas escritos a mano en
   vez de 357). Traer los commits nuevos acá (merge desde el clon de lectura), nunca
   al revés. Al hacerlo hay que recompilar y volver a correr
   `docs/native_axioms.lean`, porque los conteos de esta documentación son de
   `09deaff`.

## Entorno

Todo vive en esta carpeta y ya está construido — no hay que recrear nada:

```bash
cd ~/eth-crypto-study
lake build                                          # verde: 3444 jobs
.venv/bin/python docs/bls_smoke.py                  # ALL CHECKS PASSED
.venv/bin/python -c "from eth_cryptography_specs import bls, kzg"
lake env lean docs/native_axioms.lean               # qué teoremas dependen de native axioms (~3 min)
```

Si se borra `.lake/`: `lake exe cache get && lake build` (lo primero baja
Mathlib ya compilado; sin eso, compilarlo lleva horas).
Si se borra `.venv/`: `python3 -m venv .venv && .venv/bin/pip install -e '.[test]'`
(dispara `lake build` vía `setup.py`; con el build hecho tarda ~1 min).

Para correr la suite de vectores, dos cosas aprendidas a golpes —enchufada, con
la tapa abierta y con `caffeinate`, o la Mac duerme y no avanza; y no extrapolar
el ritmo, porque los datos de prueba se comparten en una caché (`lru_cache`) y
los primeros casos de
cada handler pagan todo el cómputo:

```bash
cd ~/eth-crypto-study
caffeinate -i -s .venv/bin/python -m pytest -q      # completa, ~3 h
caffeinate -i -s .venv/bin/python -m pytest bindings/python/tests/kzg -k compute_challenge
caffeinate -i -s -w <PID>                           # si ya está corriendo
```

## Cómo retomar

### En la Mac (incluido desde la app de Claude)

1. Pasarle **`/Users/eduardoveralli/eth-crypto-study`** como carpeta de trabajo.
   Es la única que hace falta: acá están las fuentes, el build, el venv y los
   vectores. No hace falta agregar `~/cryptography-specs`.
2. Leer [`docs/RETOMAR.md`](docs/RETOMAR.md) — el estado detallado y los comandos.
3. Elegir una de las tareas de **Qué falta** de acá arriba.
4. Recordar la regla: se commitea y pushea **solo** en este repo. Nunca a
   `ethereum/cryptography-specs`.

### En otra computadora

**Para leer y editar la documentación no hace falta instalar nada.** Se clona por
HTTPS (la clave SSH está en la Mac y no viaja) y los HTML se abren con doble clic:

```
git clone https://github.com/EdVeralli/eth-crypto-study.git
```

El clon trae las fuentes Lean, los 364 vectores, el binding y los `docs/` — unos
100 MB. Lo que **no** trae, porque está en el `.gitignore`, es `.lake/` (7,1 GB, el
build de Lean) ni `.venv/` (los bindings de Python compilados). Sin eso no se puede
compilar ni correr la suite; para rehacerlos hay que instalar `elan` y después
`lake exe cache get && lake build`. El toolchain fijado es `leanprover/lean4:v4.29.1`.

Los pasos detallados, incluido cómo pushear desde una máquina nueva, están en
[`docs/RETOMAR.md`](docs/RETOMAR.md).

## Documentación generada

- [`docs/propuesta-foda.html`](docs/propuesta-foda.html): la propuesta, cómo se implementa, FODA y preguntas abiertas
- [`docs/leaner-stf-spec.html`](docs/leaner-stf-spec.html): el EVM en Lean (`leanerSTFSpec`), los cinco lenguajes que encadena y la regla que prohíbe los native axioms
- [`docs/verified-zkevm.html`](docs/verified-zkevm.html): el paraguas Verified zkEVM y el puente Rust ↔ Lean (`hax`, Aeneas), con ejemplos reales
- [`docs/gasper-lean4.html`](docs/gasper-lean4.html): Casper FFG demostrado en Lean, los tres repos de Nyx Foundation y los dos bugs críticos que el Lean encontró en la spec
- [`docs/verified-consensus.html`](docs/verified-consensus.html): el protocolo de consenso candidato (*decoupled consensus*) formalizado entero, el 2% del repo que lee un humano, los testigos contra el teorema vacío y las tres vías para atarlo a un cliente Rust
- [`docs/repos-comparados.md`](docs/repos-comparados.md): cuadro sinóptico de los cinco repos en una sola página
- [`docs/mapa-completo.html`](docs/mapa-completo.html): big picture, spec ejecutable vs teoremas, pisos de estudio
- [`docs/fp-paso-a-paso.html`](docs/fp-paso-a-paso.html): guía del piso 1, `Bls/Fp.lean` y sus teoremas
- [`docs/RETOMAR.md`](docs/RETOMAR.md) — dónde quedamos y cómo volver a arrancar
- [`docs/notas-investigacion.md`](docs/notas-investigacion.md) — todo lo aprendido del repo
- [`docs/architecture-map.html`](docs/architecture-map.html) — mapa de arquitectura: módulos por dentro y por qué spec-first
- [`docs/bls_smoke.py`](docs/bls_smoke.py) — verificación end-to-end de BLS contra `py_ecc`
- [`docs/native_axioms.lean`](docs/native_axioms.lean) — lista los teoremas que dependen de native axioms
- [`docs/README-upstream.md`](docs/README-upstream.md) — README original del proyecto
