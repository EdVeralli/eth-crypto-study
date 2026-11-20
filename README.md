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

Y para ubicar este repo en el ecosistema: otros cuatro proyectos del ecosistema
de Ethereum que usan Lean 4 para lo mismo, en otras capas. Cada página analiza
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

Y la pregunta que sigue —**qué hacemos nosotros con todo esto**— tiene su propio
documento: **[por dónde empezar a aplicar Rust → Lean en ethlambda](docs/ethlambda-por-donde-empezar.md)**.
Mide qué partes del cliente son puras (resulta que el núcleo de la transición de
estado ya lo es), propone un archivo concreto de 89 líneas como primer candidato
con cuatro teoremas para demostrar, y dice qué costaría y qué no.

Y lo que salió de ahí está en **[`tooling/hax-lean/mini-stf/`](tooling/hax-lean/mini-stf/)**:
la transición de estado (STF) de ethlambda pasada por la cadena de herramientas
hax + Charon + Aeneas, de Rust a Lean. Se entra por
[`PROPUESTA.md`](tooling/hax-lean/mini-stf/PROPUESTA.md) (en castellano) o
[`PROPOSAL.md`](tooling/hax-lean/mini-stf/PROPOSAL.md) (en inglés).

Al 20 nov 2026 el paquete tiene las doce funciones de la STF traducidas sin
`sorry` y ciento dos resultados demostrados encima. Veinte son sobre la
ventana de slots justificados: los cuatro teoremas que se habían propuesto al
principio, el 22 de octubre, la demostración de que ese módulo no entra en
pánico, un comentario del código de ethlambda sobre esa ventana, verificado, el
invariante de dónde termina la ventana a lo largo de la transición, y que nunca
pasa de su capacidad. Catorce dicen que las doce funciones de la
transición no entran en pánico, siete de ellas con hipótesis escritas, tres más
que la comparación de raíces devuelve y que el ordenamiento y el filtrado del
mapa terminan, tres que el mapa de votos cumple una de esas hipótesis, diez que
las funciones auxiliares de `process_attestations` tampoco entran en pánico, y
uno que las operaciones del `HashMap` devuelven. Veintinueve llevan todo eso
a los estados alcanzables desde el génesis y cierran lo que la reescritura
dejaba abierto: el génesis y la conservación de las hipótesis, `ST-7` desde el
génesis, que el ordenamiento escrito a mano ordena, la cota de raíces como
invariante, y que `serialize_justifications` no depende del orden del mapa de
votos. Los demás cubren las siete
proposiciones de transición de estado del catálogo de `formal-leanSpec` (`ST-1`
a `ST-7`), con una salvedad que la propuesta detalla: sobre un estado
cualquiera `ST-7` vale bajo una hipótesis extra, que en los estados alcanzables
desde el génesis se cumple (demostrado el 19 nov). Esa hipótesis no es un
tecnicismo: al demostrar `ST-7` apareció que, cuando un voto justifica un target
en el mismo slot que el checkpoint justificado, **ethlambda y la especificación
eligen distinto** (`max_by_key` se queda con el target; leanSpec compara con `>`
estricto y se queda con el que estaba). Hay un test en Rust que lo muestra.

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

El clon del repo original vivía en `~/cryptography-specs` y era **solo lectura**:
su `origin` apuntaba a `ethereum/cryptography-specs`, así que ahí no se pusheaba
nada. Solo se usaba para traer commits nuevos de upstream. Desde el 12 nov 2026
ese clon ya no existe: si se quieren commits de upstream hay que volver a
clonarlo, siempre como solo lectura.

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
| Suite completa de 364 vectores | **Pasó — 0 diferencias contra git** (2:57:50 el 28 sep; 2:08:52 el 15 nov) |
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
   al revés. El clon de lectura `~/cryptography-specs` ya no existe: antes hay
   que volver a clonarlo. Al hacerlo hay que recompilar y volver a correr
   `docs/native_axioms.lean`, porque los conteos de esta documentación son de
   `09deaff`.
7. **Enviar el paquete `mini-stf` a LambdaClass**: el paquete de
   [`tooling/hax-lean/mini-stf/`](tooling/hax-lean/mini-stf/) está terminado
   (ver su [`PROPUESTA.md`](tooling/hax-lean/mini-stf/PROPUESTA.md)); lo único
   pendiente es mandarlo. Antes de mandarlo conviene releer la sección "El
   reemplazo de checkpoint, y dónde su código se aparta de la especificación":
   es la que les dice que su código y leanSpec difieren en un punto.
8. **Lo que el paquete ya vale "en todo estado alcanzable"**:
   desde el 19 nov el génesis está en el crate (`State::from_genesis`, copiada
   de ethlambda) y hay una noción de estado alcanzable. Sobre ella valen los
   dos invariantes, la cota de validadores, `ST-4` completa, la ausencia de
   pánico de la transición y, también desde el 19 nov, `ST-7`: su hipótesis
   del historial es falsa en el génesis, la establece el primer bloque
   aceptado, y eso ya está demostrado (teorema 24, namespace `G7`). De las
   propiedades del catálogo no queda ninguna sin subir a los estados
   alcanzables. Desde el 20 nov la ausencia de pánico ya no pide la cota de
   raíces por bloque (teorema 26, namespace `RZ`: sale de un invariante). Pide
   `usize` de 64 bits, que el hash devuelva, y que la lista de attestations
   del bloque respete la capacidad de su tipo (4096), que el Rust garantiza y
   la traducción a Lean no conserva.
9. **Lo que queda abierto del paquete**, después de la revisión del 20 nov.
   Una sola cosa, que no es de la lista original: `MapaVotos` no está
   relacionado formalmente con el `HashMap` del original. Las otras dos que
   aparecieron en la revisión se cerraron ese mismo día: el test que faltaba
   para `process_block_header`, y la diferencia con el original ante una raíz
   repetida en `justifications_roots` (`construir_mapa_de_votos` ahora usa
   `poner`, que hace lo que `HashMap::insert`, y hay un test). Lo que sí se hizo:
   descargar hipótesis de la ausencia de pánico, que desde el 18 nov cubre las doce funciones de
   `stf.rs` (`state_transition` incluida). La comparación de `H256` y el
   `HashMap` ya están (19 nov: pasaron de firmas sin contenido a
   definiciones, y dejaron de ser hipótesis). También está que las tres
   hipótesis sobre el estado se conservan de un bloque al siguiente (19 nov).
   `ST-7` desde el génesis también está (19 nov), y que el ordenamiento de
   raíces ordena (19 nov, teorema 25: lo que queda en `justifications_roots`
   está ordenado y no depende del orden de inserción). Y la cota fina de
   raíces del mapa de votos (distintas y en el historial) en lugar de "raíces
   más attestations ≤ 262144" (20 nov, teorema 26). De la lista original no
   queda nada. Lo que apareció en el camino también está: que
   `serialize_justifications` no depende del orden del mapa de votos, para
   los dos campos que escribe (20 nov, teorema 27, namespace `CAN`). Lo que
   ya
   está, para no rehacerlo: las doce funciones (17 y 18 nov), la cota de las
   listas de votos del mapa, y los dos invariantes de la ventana de slots
   justificados (dónde termina y que no pasa de su capacidad).

## Entorno

Todo vive en esta carpeta. El build se rehízo el 12 nov 2026 con `elan` (Lean)
y `uv` (Python 3.12; el repo pide >= 3.10). `~/.elan/bin` y `~/.local/bin` no
están en el `PATH` por defecto.

```bash
cd ~/eth-crypto-study
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
lake build                                          # verde: 3444 jobs
.venv/bin/python docs/bls_smoke.py                  # ALL CHECKS PASSED
.venv/bin/python -c "from eth_cryptography_specs import bls, kzg"
lake env lean docs/native_axioms.lean               # qué teoremas dependen de native axioms (~3 min)
```

Si se borra `.lake/`: `lake exe cache get && lake build` (lo primero baja
Mathlib ya compilado; sin eso, compilarlo lleva horas).
Si se borra `.venv/` (el `python3 -m venv` de antes ya no sirve: hace falta
Python >= 3.10):

```bash
uv venv --python 3.12 .venv
uv pip install --python .venv "pytest==9.0.3" "ruamel.yaml==0.19.1" "py_ecc==8.0.0" "setuptools>=68" wheel
PATH="$HOME/.elan/bin:$PATH" uv pip install --python .venv --no-build-isolation -e .
```

El último paso dispara `lake build` vía `setup.py`.

Para correr la suite de vectores, dos cosas aprendidas a golpes —con
`caffeinate` y sin que el equipo se suspenda, o no avanza; y no extrapolar
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

1. Pasarle **`~/eth-crypto-study`** como carpeta de trabajo.
   Es la única que hace falta: acá están las fuentes, el build, el venv y los
   vectores. No hace falta agregar `~/cryptography-specs`.
2. Leer [`docs/RETOMAR.md`](docs/RETOMAR.md) — el estado detallado y los comandos.
3. Elegir una de las tareas de **Qué falta** de acá arriba.
4. Recordar la regla: se commitea y pushea **solo** en este repo. Nunca a
   `ethereum/cryptography-specs`.

## Documentación generada

- [`docs/propuesta-foda.html`](docs/propuesta-foda.html): la propuesta, cómo se implementa, FODA y preguntas abiertas
- [`docs/leaner-stf-spec.html`](docs/leaner-stf-spec.html): el EVM en Lean (`leanerSTFSpec`), los cinco lenguajes que encadena y la regla que prohíbe los native axioms
- [`docs/verified-zkevm.html`](docs/verified-zkevm.html): el paraguas Verified zkEVM y el puente Rust ↔ Lean (`hax`, Aeneas), con ejemplos reales
- [`docs/gasper-lean4.html`](docs/gasper-lean4.html): Casper FFG demostrado en Lean, los tres repos de Nyx Foundation y los dos bugs críticos que el Lean encontró en la spec
- [`docs/verified-consensus.html`](docs/verified-consensus.html): el protocolo de consenso candidato (*decoupled consensus*) formalizado entero, el 2% del repo que lee un humano, los testigos contra el teorema vacío y las tres vías para atarlo a un cliente Rust
- [`docs/ethlambda-por-donde-empezar.md`](docs/ethlambda-por-donde-empezar.md): **qué pedazo de ethlambda sería candidato a la vía Rust → Lean**. El mapa de pureza de los crates, el archivo de 89 líneas que propongo como primer experimento, sus cuatro teoremas, y la alternativa barata del oráculo
- [`docs/repos-comparados.md`](docs/repos-comparados.md): cuadro sinóptico de los cinco repos en una sola página
- [`docs/mapa-completo.html`](docs/mapa-completo.html): big picture, spec ejecutable vs teoremas, pisos de estudio
- [`docs/fp-paso-a-paso.html`](docs/fp-paso-a-paso.html): guía del piso 1, `Bls/Fp.lean` y sus teoremas
- [`docs/RETOMAR.md`](docs/RETOMAR.md) — dónde quedamos y cómo volver a arrancar
- [`docs/notas-investigacion.md`](docs/notas-investigacion.md) — todo lo aprendido del repo
- [`docs/architecture-map.html`](docs/architecture-map.html) — mapa de arquitectura: módulos por dentro y por qué spec-first
- [`docs/bls_smoke.py`](docs/bls_smoke.py) — verificación end-to-end de BLS contra `py_ecc`
- [`docs/native_axioms.lean`](docs/native_axioms.lean) — lista los teoremas que dependen de native axioms
- [`docs/README-upstream.md`](docs/README-upstream.md) — README original del proyecto
