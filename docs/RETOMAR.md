# Retomar trabajo

_Ultima actualizacion: 2026-10-19_

## Como retomar en otra computadora (Windows)

Para **leer y editar la documentacion no hace falta instalar nada**. Clonar y listo.

```powershell
cd $env:USERPROFILE
git clone https://github.com/EdVeralli/eth-crypto-study.git
cd eth-crypto-study
```

Clonar por **HTTPS**, no por SSH: la clave privada esta en la Mac y no viaja.

**Que viene en el clon** (~100 MB): las fuentes Lean (`EthCryptographySpecs/`), los
364 vectores de prueba (`tests/`), el binding de Python (`bindings/`) y toda la
documentacion (`docs/`). Los siete HTML se abren con doble clic; los `.md` con
cualquier editor.

**Que NO viene, porque esta en el `.gitignore`:**

| Carpeta | Peso en la Mac | Para que hace falta |
|---|---|---|
| `.lake/` | 7,1 GB | compilar Lean (`lake build`) |
| `.venv/` | 56 MB | llamar a Lean desde Python y correr la suite |

O sea que en la HP **no se puede compilar ni correr la suite sin reconstruir eso**.
Si en algun momento hiciera falta: instalar `elan` (el gestor de toolchains de Lean,
desde elan.lean-lang.org), despues `lake exe cache get` (baja Mathlib ya compilado;
sin eso son horas) y `lake build`. El toolchain fijado es `leanprover/lean4:v4.29.1`.

**El clon de solo lectura de `ethereum/cryptography-specs` tampoco esta**, y para la
documentacion no se necesita: solo servia para traer commits de upstream.

**Para pushear desde la HP** hace falta credencial propia: lo mas simple es HTTPS con
un personal access token de GitHub. Si se usa SSH y el `git push` falla con
`connect to host github.com port 22: Connection refused` (paso en la Mac, la red
bloquea el puerto 22), la solucion es agregar esto al `~/.ssh/config`:

```
Host github.com
  Hostname ssh.github.com
  Port 443
  User git
```

---

## Donde quedamos (19 oct 2026): los cinco repos de Pablo, comparados

Del 11 al 18 de octubre el trabajo se corrio de nuestro repo al **ecosistema**:
Pablo fue pasando repos y los analizamos uno por uno, siempre con la misma
pregunta de fondo, que es la que a el le importa: **como juegan Rust y Lean**.

El resultado esta en `docs/repos-comparados.md` (el cuadro sinoptico) y en una
pagina HTML por repo. La seccion 0 del cuadro es la que hay que leer primero: las
cuatro maneras distintas en que cada repo usa Lean con otros lenguajes.

| Repo | La jugada |
|---|---|
| `cryptography-specs` | Lean **es** el programa, y Python lo llama (Lean -> C -> .so) |
| `verified-zkevm` | el programa es Rust, y **genera** Lean para demostrar sobre el |
| `leanerSTFSpec` | Lean y Python corren **al lado** y se comparan las salidas |
| `gasper-lean4` | Lean solo: no hay programa que corra |
| `verified-consensus` | Lean solo, **pero ya trae escrito el enunciado** de que es un consenso correcto |

Hitos de esas dos semanas, por si hace falta rastrear algo:

- **13 oct** — se armo el cuadro sinoptico. Se agrego en todos los HTML el bloque
  "Donde se usa Lean aca" con las tres preguntas (se compila / se traduce codigo /
  hay Lean en el entorno de ejecucion).
- **13 oct** — se explico por que importan los axiomas, en el cuadro y en
  `mapa-completo.html`: la lista de axiomas es la lista de cosas que hay que creer
  sin demostracion, y que hace que uno sea o no permitido.
- **13 oct** — **correccion importante**: lo que el cuadro decia de `gasper-lean4`
  estaba mal. Si hay Lean que calcula (carpeta `Executable/`, 58 `#eval` sobre
  modelos de juguete). El `Fintype Hash` es un techo de escala, no un impedimento.
- **13 oct** — revision completa del cuadro con un agente de ojos frescos: 13
  correcciones de datos, citas y terminologia (ver el commit
  "revision - 13 correcciones").
- **18 oct** — quinto repo: `fradamt/verified-consensus`. Esta en el cuadro pero
  tiene pagina propia desde el 20 oct: `docs/verified-consensus.html`.

### Pendiente inmediato

1. ~~`docs/verified-consensus.html`~~ **HECHA** (20-21 oct). La pagina del quinto repo,
   con el bloque de las tres preguntas igual que las otras seis, y el chequeo de axiomas
   **corrido por nosotros**, no citado del README.

   Lo que se hizo el 21 oct: se clono `fradamt/verified-consensus` en `~/verified-consensus`
   (solo lectura), elan bajo Lean v4.34.1, `lake exe cache get` trajo 8908 archivos de
   Mathlib, `lake build` cerro en verde con **9972 jobs**, y despues
   `lake env lean scripts/ReviewAxioms.lean` confirmo que las **24 declaraciones** que
   componen el resultado dependen SOLO de `propext`, `Classical.choice` y `Quot.sound`.
   Ni `sorryAx`, ni un `_native`, ni axiomas propios. La salida esta commiteada en
   `docs/verified-consensus-axiomas.txt`.

   De paso se vio en el log del build el contraste que la pagina ahora muestra: el testigo
   del apagon SI arrastra native axioms (`leak_fairness_witness._native.native_decide.ax_1_1`
   y `ax_1_2`) mientras `outage_witness_core` no — tal como dice su README.

   **`~/verified-consensus/.lake` ya se puede borrar** para recuperar disco (la Mac estaba
   al 93%). Si alguna vez hace falta rehacerlo: `lake exe cache get && lake build`.

2. **El cruce con `decoupled-consensus-apuntes`** (repo aparte,
   `github.com/EdVeralli/decoupled-consensus-apuntes`): ese repo tiene el **paper**
   que `verified-consensus` formaliza, y que su README declara "not yet public".
   Vale cruzar que dice la formalizacion sobre el problema del ancla de la clase 7,
   y la diferencia `K >= 4` (paper) vs `K >= 5` (formalizacion). Ojo: nuestro PDF es
   del 28 de agosto y llega a §7; el `.tex` que formalizaron referencia ademas §8,
   §9 y §10, asi que es una version posterior.
3. **El experimento con ethlambda** (22 oct). Ya esta el analisis escrito en
   `docs/ethlambda-por-donde-empezar.md`: se clono `lambdaclass/ethlambda` de solo
   lectura y se midio que partes son puras. Hallazgo: **el nucleo de la transicion de
   estado ya es puro** (0 async, 0 locks, 0 unsafe); la suciedad esta en el actor.

   El candidato propuesto es
   `crates/blockchain/state_transition/src/justified_slots_ops.rs` — **89 lineas, cuatro
   funciones**, el bitlist de slots justificados con indice relativo al slot finalizado.
   Tiene cuatro teoremas listados en ese documento, tres `.expect()` que se vuelven
   obligaciones de demostracion, y lo unico a modelar a mano es un bitlist.

   **Lo que falta para arrancar**: chequear si la cadena hax/Aeneas se instala en el
   contenedor de la sesion (para no tocar la Mac) y correr el paso 1, que es traducir
   ese crate y mirar que queda en `FunsExternal_Template.lean`.
4. Lo de antes, que sigue abierto: la guia paso a paso de `accountable_safety` y la
   guia del piso 2 (`Bls/G1.lean`).

---

## Historial: donde quedabamos el 6 oct 2026 (FODA investigado, mapas repasados)

Cortamos el 6 oct con todo commiteado y pusheado (`2ad46ec`). Hecho hoy:
investigadas y respondidas (hasta donde hay informacion publica) las 5 preguntas
abiertas del FODA; ver detalle mas abajo. **Lo que sigue**: repasar
`fp-paso-a-paso.html` o arrancar la guia del piso 2 (`Bls/G1.lean`), a eleccion.
Para seguirle el paso a upstream: `git -C ~/cryptography-specs fetch` y comparar
contra `d1331f0` (ultimo chequeo, 7 oct).

Chequeo de upstream (5 oct 2026, `ethereum/cryptography-specs` master en
`8f811fc`): 6 commits despues de nuestro `09deaff`, todos de XMSS (#33, #35,
#37, #38, #40, #42). XMSS quedo completo alla con el teorema
`verify_keyGen_sign`; sumo 4 `native_decide` y sigue sin `@[export]`. BLS, KZG,
binding, build y workflows: sin cambios. Decision: NO re-sincronizar por ahora,
solo se ajustaron los textos (README punto 5 y 6, propuesta-foda, mapa-completo
columna XMSS, architecture-map modulo XMSS). Los conteos de la documentacion
siguen siendo los de `09deaff`.

Chequeo del 7 oct: upstream en `d1331f0` (6 oct), +2 commits, los dos teoremas
de XMSS: #43 tweak encoding inyectivo (`tweakInput_injective`) y #44 tamano del
codigo target-sum (`Proofs/Xmss/CodeSize.lean`, mismo titulo que el issue #27). El numero grande
de #44 se verifica con `decide +kernel` (lo calcula el kernel, no codigo
compilado): contraste util con los native axioms. `native_decide` y `bv_decide`
sin cambios, sigue sin `@[export]` XMSS. Solo se actualizaron hash y fecha en
README y aca.

6 oct 2026: investigadas las 5 preguntas abiertas del FODA (seccion 4 de
`propuesta-foda.html`); cada una tiene su renglon "Lo que encontramos". Todas
siguen abiertas y sin plan publico: consensus-specs no depende del paquete
(usa `py_arkworks_bls12381` + `ckzg`), nadie pinea los vectores, no hay issue
para `ConcreteBlsLaws`, no hay mecanismo de paridad con estandares, el binding
C sigue sin verificar. Fuente nueva (6): metadatos de PyPI via `pip download`.

La infraestructura esta cerrada (ver mas abajo). Desde el 29 sept estamos
armando y repasando la **documentacion de estudio** en `docs/`, para que
alguien que llega (Pablo, por ejemplo) entienda el repo sin haber estado en
las sesiones. Son siete paginas HTML que se abren con el navegador, mas el
cuadro sinoptico en markdown:

0. `docs/propuesta-foda.html` — la propuesta, como se implementa y FODA (5 oct)
0b. `docs/leaner-stf-spec.html` — el EVM en Lean, repo de Alexander Hicks (11 oct)
0c. `docs/verified-zkevm.html` — el paraguas de la EF y el puente Rust/Lean (11 oct)
0d. `docs/gasper-lean4.html` — el consenso (Casper FFG) demostrado, y los tres repos de Nyx (12 oct)
0e. `docs/repos-comparados.md` — cuadro sinoptico de los 5 repos en un solo lugar (13 oct; 5to repo agregado el 18 oct)
0f. `docs/verified-consensus.html` — el quinto repo: decoupled consensus formalizado entero (20 oct)
1. `docs/mapa-completo.html` — el big picture
2. `docs/architecture-map.html` — los modulos por dentro y por que spec-first
3. `docs/fp-paso-a-paso.html` — guia del piso 1 (`Bls/Fp.lean`)

### Estado del repaso de `mapa-completo.html`

| Seccion | Estado |
|---|---|
| Encabezado e intro ("Que corre y que se demuestra") | Repasado: sin "upstream"; la bajada explica spec vs teoremas |
| Leyenda de colores (las dos filas) | Repasado: mismos nombres que el diagrama 1 (spec / teoremas / binding, con su mundo) |
| Bloque de pisos de estudio ("El mapa es la vista de arriba...") | Repasado: explica que es un piso; "en el repo" en vez de "en tu Mac" |
| Diagrama 1: las capas | Repasado: cada caja dice en que mundo esta (Python, C, Lean); nota del lakefile en criollo |
| Diagrama 2: build y verificaciones | Repasado: "teoremas" en vez de "pruebas"; verificaciones numeradas 1-2-3 |
| Que es un vector de prueba | Nueva: dos `data.yaml` reales (valido vs adulterado) y el test invertido |
| Mapa archivo por archivo | Repasado: explicacion de como leerlo y ejemplo con `G1Group` |
| Donde la separacion no es perfecta | Repasado (5 oct): datos verificados con `#print axioms`: 10 de 492 teoremas dependen de *native axioms* (`native_decide` + `bv_decide`), 3 son reglas generales (`uncompress_compress` entre ellas). Desplegable con la tabla y como comprobarlo. Se agrego `docs/native_axioms.lean` |
| Tres verificaciones, las tres en verde | Repasado: se deja como esta |
| Glosario | Repasado: 6 terminos nuevos (.so, marshalling, simbolo C, lakefile, sorry, native axioms) |

**El repaso de `mapa-completo.html` esta terminado.** El 5 oct se hizo ademas una
revision cruzada de todos los docs contra el codigo (agente con ojos frescos).
Correcciones aplicadas: los teoremas escritos a mano son **357**, no 212 (el
conteo viejo ignoraba `private`/`protected`/`@[simp]`); Lean cuenta 492 con
los autogenerados. XMSS exporta 9 constantes (no funciones). Hay 33 `@[export]`
en total: 14 funciones + 19 constantes. `notas-investigacion.md` actualizado
(rutas, orden, tabla). Terminologia "teoremas" unificada en README, mapa de
arquitectura y guia Fp. Glosario: + kernel, rw, SAT solver, generador/orden,
MSM, trusted setup.

### Pendiente

- ~~Repasar `architecture-map.html`~~ Hecho el 5 oct: glosas en linea para toda
  la jerga de los modulos y archivos (Jacobianas, optimal Ate, twist, SSWU,
  NTT, DAS, OTS...), cada una verificada contra el archivo .lean; terminologia
  "teoremas"; encabezado igual al del mapa completo.
- ~~Investigar las preguntas abiertas del FODA~~ Hecho el 6 oct: las 5 tienen
  su renglon "Lo que encontramos" en `propuesta-foda.html`; la de XMSS quedo
  respondida a favor el 5 oct. Las guias por piso quedaron postergadas mientras
  entendiamos la propuesta; ya se puede volver a ellas.
- Repasar `fp-paso-a-paso.html`.
- Escribir la guia del piso 2: `Bls/G1.lean` + `G1Group` / `G1Order` / `G1Msm`.

### Criterios que fuimos acordando para los mapas

- Explicar en criollo, con analogias, y con **ejemplos reales del repo**.
- Cada caja dice en que lenguaje ("mundo") estamos: Python, C o Lean.
- "Teoremas" para las demostraciones de Lean; "proof KZG" para los 48 bytes
  criptograficos de KZG. Nunca "pruebas" a secas.
- Compacto: si algo es largo, va en un desplegable.
- Decir **native axioms** (no "atajos") para `native_decide` / `bv_decide`.
- Antes de afirmar algo sobre los teoremas, verificarlo con Lean (`#print axioms`,
  `docs/native_axioms.lean`), no suponerlo. El 1 oct el mapa decia "8
  native_decide en ejemplos concretos" y era incompleto.
- Las paginas de `docs/` se enlazan entre si con links relativos.

## Estado de la infraestructura (cerrado el 28 sept)

**Todo cerrado.** El build de Lean esta completo, BLS12-381 y KZG corren desde
Python, y la suite completa de 364 vectores de prueba paso sin una sola
diferencia. No hay nada pendiente de la etapa de "hacerlo funcionar".

```
lake build   ->  Build completed successfully (3444 jobs), exit 0
pytest       ->  364 passed in 10670.43s (2:57:50), exit 0
git status   ->  limpio, diff en tests/ vacio
```

Ese `git status` limpio es el resultado importante: el spec de Lean regenero
los 364 vectores commiteados **byte a byte**. Ver `notas-investigacion.md`
para el desglose por handler y las dos lecciones sobre el costo de correrla.

## Repos

- **Tu repo (todo vive aca):** `~/eth-crypto-study` — `github.com/EdVeralli/eth-crypto-study`.
  Autocontenido desde el 29 sept 2026: fuentes Lean, `lake build` en verde,
  `.venv` con los bindings compilados, los 364 vectores y los docs.
- **Repo original (solo lectura):** `~/cryptography-specs` — clon de
  `ethereum/cryptography-specs`, solo para traer commits de upstream. Solo existe
  en la Mac; en otra maquina no hace falta.
- **Los otros repos del ecosistema**, clonados de solo lectura cuando los
  analizamos (no viven en la Mac, se vuelven a clonar cuando hagan falta):
  `alexanderlhicks/leanerSTFSpec`, `github.com/verified-zkevm`,
  `NyxFoundation/gasper-lean4` y `fradamt/verified-consensus`. Lo que escribimos
  sobre ellos esta en `docs/` de este repo. **Nunca se pushea ahi.**
- **Repo hermano, aparte:** `github.com/EdVeralli/decoupled-consensus-apuntes` —
  apuntes del paper "Decoupled consensus", que es justo el que formaliza
  `verified-consensus`. Tiene el PDF del paper.
- **Docs generados:** `~/eth-crypto-study/docs/` — mapa interactivo + notas de investigacion

## Estado actual

| Paso | Estado |
|---|---|
| `lake build` | Completo — 3444 jobs, exit 0, sin errores ni warnings |
| venv + `pip install -e '.[test]'` | Completo — extension C compilada y enlazada |
| `from eth_cryptography_specs import bls` | Funciona |
| Verificacion cruzada contra `py_ecc` | Pasa (`docs/bls_smoke.py`) |
| Suite completa de 364 vectores | **Paso — 0 diferencias contra git** |

## Como volver a usarlo

El venv ya existe en tu propio repo, no hay que recrearlo:

```bash
cd ~/eth-crypto-study
.venv/bin/python -c "from eth_cryptography_specs import bls, kzg; print(dir(kzg))"
.venv/bin/python docs/bls_smoke.py
```

Si se borra `.lake/`, rehacer el build (`lake exe cache get` y `lake build`).
Si se borra `.venv/`, rehacer solo el paso de pip — pero ojo: `pip install -e`
dispara `lake build` de nuevo via `setup.py`.

## Si vas a correr la suite de nuevo

Dos cosas aprendidas a golpes (detalle en `notas-investigacion.md`):

1. **Enchufada y con la tapa abierta.** Sin eso la Mac duerme y la suite no
   avanza: medimos 2 vectores en dos dias y medio. Con `caffeinate` salio en
   97 minutos.
2. **No extrapoles el ritmo.** La `lru_cache` de los fixtures hace que los
   primeros casos de cada handler pagan todo y el resto vuele.

```bash
cd ~/eth-crypto-study
caffeinate -i -s .venv/bin/python -m pytest -q          # completa, ~3 h de CPU
caffeinate -i -s .venv/bin/python -m pytest bindings/python/tests/kzg -k verify_kzg_proof   # un handler
```

Si ya hay un pytest corriendo y solo querés que no duerma, sin perder la
cache en memoria:

```bash
caffeinate -i -s -w <PID>    # el candado se suelta cuando el proceso termina
```

## Superficie de BLS expuesta a Python

La API es acotada — solo dos funciones y dos constantes:

```python
from eth_cryptography_specs import bls

bls.BYTES_PER_PUBKEY          # 48
bls.BYTES_PER_SIGNATURE       # 96
bls.eth_aggregate_pubkeys(pubkeys)                  # -> bytes (48)
bls.eth_fast_aggregate_verify(pubkeys, msg, sig)    # -> bool
```

**No hay firmado expuesto.** Para generar claves y firmas hay que usar
`py_ecc.bls.G2ProofOfPossession` (ya instalado como dependencia de test); el
spec en Lean solo cubre agregacion y verificacion, que es lo que necesita un
cliente de consenso.

## Proximos pasos posibles

La lista al dia esta arriba, en **"Pendiente inmediato"** (seccion del 19 oct).
En dos palabras: la pagina de `verified-consensus`, el cruce con el repo de
apuntes del paper, y las dos guias de estudio que vienen de antes
(`accountable_safety` y el piso 2, `Bls/G1.lean`).

De infraestructura y de repaso de mapas no queda nada, salvo repasar
`fp-paso-a-paso.html`.

## Documentacion generada

- `docs/propuesta-foda.html` — la propuesta, como se implementa, FODA y preguntas abiertas investigadas
- `docs/leaner-stf-spec.html` — leanerSTFSpec: el EVM/STF en Lean, 5 lenguajes encadenados, regla D21 (prohibe native axioms), testing diferencial
- `docs/verified-zkevm.html` — Verified zkEVM (org de la EF, meta 2027) y la via Rust -> Lean: hax, Aeneas/Charon, ejemplos reales, costo de confianza
- `docs/ethlambda-por-donde-empezar.md` — que pedazo de ethlambda seria candidato a la via Rust -> Lean: mapa de pureza por crate, el archivo de 89 lineas propuesto, sus cuatro teoremas, y la alternativa del oraculo
- `docs/gasper-lean4.html` — Casper FFG en Lean (NyxFoundation): justificacion/finalidad, S1/S2, los 3 teoremas, el rigor maximo (solo propext + Quot.sound), y los repos hermanos formal-leanSpec (2 bugs criticos encontrados en la spec) y verity (cliente en devnet con ethlambda y ream)

Las 8 paginas de docs/ llevan el mismo bloque "Donde se usa Lean aca" con tres
preguntas: si se compila, si se traduce codigo entre Lean y otro lenguaje, y si
hay Lean en
el entorno de ejecucion. Resumen: solo cryptography-specs tiene Lean compilado
invocable (y nadie lo consume); en el resto, en produccion corre Rust/C/Go.
- `docs/mapa-completo.html` — big picture: spec vs teoremas, vectores, pisos de estudio
- `docs/architecture-map.html` — modulos por dentro y por que spec-first
- `docs/fp-paso-a-paso.html` — guia del piso 1, `Bls/Fp.lean` y sus teoremas
- `docs/notas-investigacion.md` — todo lo que aprendimos sobre el repo
- `docs/bls_smoke.py` — verificacion end-to-end de BLS contra py_ecc
- `docs/README-upstream.md` — README original del repo de Ethereum
