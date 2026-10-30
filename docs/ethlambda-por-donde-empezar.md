# Aplicar Rust → Lean a ethlambda: por dónde empezar

Los cinco repos que estudiamos responden *qué se puede hacer*. Este documento responde la
otra pregunta, que es la nuestra: **qué pedazo de ethlambda sería candidato, y por qué.**

Todo lo que sigue está medido sobre un clon de solo lectura de
[`lambdaclass/ethlambda`](https://github.com/lambdaclass/ethlambda), commit `22d1a72`
(22 oct 2026). Como con los demás repos del ecosistema: **se lee, no se pushea**.

---

## 1. El límite, para no perder tiempo

> **Esta sección se corrigió el 23 de octubre**, después de instalar la cadena de herramientas y correrla
> sobre este código. Decía que el obstáculo era la biblioteca estándar. **No lo es.** El
> log completo está en la [sección 7](#7-el-experimento-lo-que-pas%C3%B3-de-verdad).

La cadena de herramientas Rust → Lean (Charon + Aeneas, disparada por
`cargo hax into lean`) tiene **dos límites**, y ninguno de los dos es `std`:

**Primero, el cierre de dependencias.** El filtro `-i` de hax **no llega a Charon ni a
Aeneas**: ellos procesan el crate entero *y todo lo que importa*. Un solo `dyn` en una
dependencia transitiva dispara *"Dynamic trait types are not supported yet"*, detrás viene
un *"Mixed declaration groups are not supported yet"*, y de ahí cientos de errores en
cascada **sin que se escriba un solo archivo**. Apuntar a un módulo adentro de un crate
grande no sirve: el objetivo tiene que **ser su propio crate**.

**Segundo, los closures de iterador sobre colecciones prestadas.** Un `max_by_key` sobre
una colección por referencia hace fallar a Aeneas con *"Can't end abstraction N as it is
set as non-endable"* — su maquinaria de *borrows* dándose por vencida. La firma sale
completa y el cuerpo sale como `sorry`.

**Lo que sí pasa, aunque use `std`:** `for i in 0..n`, indexación, aritmética con
`checked_*`, el operador `?`. `HashMap`, `Vec` y `Option` se traducen solos; Aeneas trae
sus propios modelos. En las dos pruebas que corrimos, la plantilla de cosas a modelar a
mano salió **vacía**.

Consecuencia directa: **un cliente de consenso entero no pasa.** ethlambda son 145.508
líneas de Rust con actores, tokio, libp2p y RocksDB — pero el motivo es el `dyn`, el async
y los locks, no `std`. Buscar "traducir ethlambda" es buscar un no.

Lo que sí pasa es un **núcleo de cómputo puro, en su propio crate**. Así que la pregunta
útil es: ¿dónde está ese núcleo?

---

## 2. El mapa de pureza

Medido sobre los crates del workspace (quince miembros declarados en el `Cargo.toml`
raíz), contando sobre `src/`:

| Crate | Líneas | `async` | `unsafe` | locks / tokio | deps |
|---|---|---|---|---|---|
| `blockchain/state_transition` | 29 054 | **0** | 1 *(es un comentario)* | 16 | 10 |
| **`blockchain/fork_choice`** | **136** | **0** | **0** | **0** | **1** |
| `common/ssz-tree` | 2 534 | 0 | 0 | 15 | 6 |
| `common/crypto` | 1 476 | 0 | 0 | 0 | 8 |
| `common/types` | 13 099 | 0 | 0 | 2 | 18 |

**El hallazgo que más importa: el núcleo de la transición de estado ya es puro.** La
suciedad —los `Arc`, los `RwLock`, el tokio— vive en el actor, el pool de atestaciones y
el caché de claves públicas, no en las reglas del protocolo.

Y una aclaración sobre el nombre: el crate `state_transition` tiene **dos cadenas
adentro**. `src/beacon/` es la Beacon Chain de hoy (el seguidor de mainnet); la STF de
*lean* —la cadena que ethlambda realmente es— está en `src/lib.rs` y
`src/justified_slots_ops.rs`. Las dos dan **0 async, 0 locks, 0 unsafe**.

---

## 3. El candidato: `justified_slots_ops.rs`

**89 líneas. Cuatro funciones. Cero `async`, cero locks, cero `unsafe`, cero `HashMap`.**

### Qué hace

Lleva la cuenta de qué slots están justificados, en un bitlist **con índice relativo al
slot finalizado**:

```text
índice 0  =  finalized_slot + 1
slots ≤ finalized_slot  →  justificados implícitamente, no ocupan lugar
```

Cuando la finalidad avanza, la ventana se corre y los bits de abajo se tiran. Las cuatro
funciones son `is_slot_justified`, `set_justified`, `extend_to_slot` y `shift_window`.

### Por qué es el candidato

- **Es aritmética con `checked_sub` y off-by-ones por todos lados**, y dos loops que
  reconstruyen el bitlist copiando bits de una posición a otra.
- **Si eso se corre un lugar, el nodo cree que un slot está justificado cuando no lo
  está.** Es el tipo de bug que no rompe ningún test unitario y parte la cadena en
  producción.
- **Lo que hay que modelar a mano es una sola cosa**: `JustifiedSlots`, que es un bitlist
  de SSZ. Se modela como una lista de booleanos y listo. Es el escenario ideal — lo que
  entra como supuesto es chico y obviamente correcto.
- **Y ya lo probamos: traduce.** 19 definiciones, cero `sorry`, cero errores, plantilla
  vacía. Es el único de los tres candidatos que pasó. Detalle en la sección 7.
- **Hay tres `.expect()`** en esas 89 líneas. En Lean cada uno se convierte en una
  obligación de demostración: hay que probar que el índice está adentro.

### Los teoremas, en orden de dificultad

| # | Enunciado | Por qué importa |
|---|---|---|
| 1 | **`extend_to_slot` no pierde bits**: todo bit en `true` antes sigue en `true` después, en la misma posición | es un loop de copia; es donde vive el off-by-one |
| 2 | **Ida y vuelta**: después de `set_justified(s)`, `is_slot_justified(s)` devuelve `true` | la propiedad mínima que uno espera y nadie verifica |
| 3 | **`shift_window` corre sin deformar**: el bit en `i + delta` antes es el bit en `i` después | el segundo loop de copia, y el que corre al finalizar |
| 4 | **El compuesto**: cuando la finalidad avanza, todo slot que estaba justificado y sigue por encima del nuevo límite se sigue reportando justificado | **involucra tres funciones y dos sistemas de índices a la vez.** Un humano no lo verifica leyendo |

El 4 es el que justifica todo el ejercicio.

---

## 4. Las otras dos opciones, para tenerlas sobre la mesa

### `src/beacon/stf/epoch/justification.rs` — 253 líneas, 100% puro

La justificación y finalización de **Casper FFG**: el bitfield de 4 bits que envejece una
época por vez, y las cuatro reglas de finalización.

- **A favor**: [`gasper-lean4`](gasper-lean4.html) **ya tiene esos teoremas escritos en
  Lean** — justificación, finalización, accountable safety. Tendrías contra qué comparar
  en vez de inventar el enunciado.
- **En contra**: es el seguidor de mainnet, no la cadena que ethlambda es.

### `blockchain/fork_choice` — 136 líneas, una sola dependencia

El LMD-GHOST que elige la cabeza. Dos funciones, y el comentario del código dice
*"This is the same implementation from leanSpec"*, o sea que es una transcripción de la
spec — justo el caso donde un teorema de equivalencia tiene sentido.

- **A favor**: es **el archivo donde vive uno de los dos bugs críticos** que el Lean de
  `formal-leanSpec` encontró: *"la cabeza no es función pura del store"* — dos nodos
  honestos con los mismos bloques en distinto orden eligiendo cabezas distintas.
- **En contra, y esto lo medimos**: no traduce. El `HashMap` no es el problema —se traduce
  solo, y aparece tal cual como `std.collections.hash.map.HashMap` en la firma generada—
  pero **el `max_by_key` sí**: Aeneas falla con *"Can't end abstraction"* en esa línea
  exacta. La firma sale completa y el cuerpo sale `sorry`.

> **Observación al leer el código, sin demostrar:** acá parece que lo resolvieron bien. El
> desempate es `max_by_key(|root| (peso, *root))`, y como los roots son únicos no hay
> empates posibles, así que el máximo no depende del orden. **Convertir esa observación en
> demostración sería el teorema.**
>
> Con una ironía que vale anotar: **ese mismo `max_by_key` es el que rompe la traducción
> automática.** La línea donde vive la pregunta interesante es la línea que Aeneas no sabe
> pasar. Para demostrarlo habría que reescribirla como un loop con índices — y entonces lo
> demostrado sería sobre la reescritura, no sobre el código que corre.

---

## 5. Las cinco opciones, y cuál conviene

Lo de abajo reemplaza el plan que había acá antes, que quedó viejo: los tres primeros
pasos ya están hechos (entorno instalado, traducción corriendo, `lake build` en verde).
La pregunta ahora es a qué apuntar.

### La medición que decide

El obstáculo de los closures sobre colecciones prestadas **no está repartido por `lib.rs`:
está concentrado en una función.** Medido función por función, sobre las 654 líneas de
código del archivo (los tests arrancan en la 655):

| Función | Líneas | Iteradores | Toca `State`/SSZ |
|---|---|---|---|
| `process_attestations` | 181 | **15** | sí |
| `try_finalize` | 60 | **1** | sí |
| `serialize_justifications` | 41 | **5** | sí |
| `process_block_header` | 102 | 0 | sí |
| `is_valid_vote` | 49 | 0 | sí |
| `state_transition` | 40 | 0 | sí |
| `attestation_data_matches_chain` | 39 | 0 | sí |
| `process_slots` | 19 | 0 | sí |
| `process_block` | 10 | 0 | sí |
| `slot_is_justifiable_after` | 26 | 0 | **no** |
| `is_proposer` | 6 | 0 | **no** |
| `current_proposer` | 7 | 0 | **no** |

Ocho de las doce no tienen un solo iterador. Y tres no tocan ni `State` ni SSZ, o sea que
no arrastran nada.

### Las opciones

**A. El crate entero.** Probado, muerto: 413 errores, cero archivos escritos. El
`dyn Error` de `ethlambda-storage` más 47.000 líneas de Beacon Chain que no queremos.
Descartada por evidencia, no por opinión.

**B. Sacar `lib.rs` a un crate propio, con los tipos reales.** Te saca de encima storage y
el módulo beacon de un saque, porque `lib.rs` no los importa — sus únicos `use` son
`std::collections`, `ethlambda_types` y `tracing`. Pero arrastra `ethlambda-types`:
**16.022 líneas con 9 dependencias**, con los derives de SSZ y el merkleizador adentro. Es
apostar a que ese cierre pasa. Y aun ganando la apuesta, `process_attestations` sale en
`sorry`.

**C. Sacar `lib.rs` con tipos sustitutos escritos a mano.** El mismo movimiento que con
`JustifiedSlots`, pero en grande: escribir a mano `State`, `Block`, `AttestationData`,
`Checkpoint`, `H256`, y `hash_tree_root` como función opaca. Trabajo acotado pero real,
varios días. Traducirían ocho de las doce funciones. El costo conceptual: los teoremas
hablarían de *nuestro* `State`, no del de ellos — la lógica y la aritmética siguen siendo
suyas, la estructura de datos no.

**D. La isla aritmética.** Las tres funciones que no tocan `State` ni SSZ
(`slot_is_justifiable_after`, `current_proposer`, `is_proposer`) más
`justified_slots_ops.rs`, que ya sabemos que anda. Cero tipos que sustituir, cero
dependencias que arrastrar.

**E. Reescribir `process_attestations` con loops de índice.** No. Demostrarías propiedades
de tu reescritura, y no hay forma de conectarla con el original, porque el original no
traduce. El teorema sería verdadero y mudo. Es la misma trampa que el `max_by_key` del
fork choice, y vale anotarla para no caer.

### La recomendación: la D, y no como premio consuelo

Mirá qué es `slot_is_justifiable_after`, que decide qué slots se pueden justificar:

```rust
delta <= 5                                   // los primeros 5 siempre
|| delta.isqrt().pow(2) == delta             // distancias cuadrado perfecto
|| (4*delta + 1) es cuadrado perfecto impar  // pronics: n(n+1)
```

El comentario del código **afirma una identidad matemática** —que `4·n(n+1)+1 = (2n+1)²`—
y la usa para detectar pronics sin factorizar. Eso es un teorema de verdad, chico y no
trivial, con dos lugares donde puede haber un bug: el `checked_mul(4)`, que puede desbordar
con slots grandes, y el comportamiento de `isqrt` en los bordes. Es el perfil exacto que
buscábamos: algo que un humano no verifica leyendo y una máquina sí.

Y encaja con lo que ya tenemos. `justified_slots_ops` lleva la cuenta de qué slots **están**
justificados; `slot_is_justifiable_after` dice cuáles **pueden** estarlo. Juntas son la
aritmética completa de la justificación, que es el corazón del protocolo. No es un rincón
arbitrario del cliente: es la parte que los apuntes explican.

### La medición que decidía entre B y C: hecha, y da que sí

La condición para elegir entre B y C era saber si `ethlambda-types` pasa el cierre de
dependencias. **Medido el 26 de octubre: pasa.**

El crate de prueba está en [`tooling/hax-lean/prueba-types/`](../tooling/hax-lean/prueba-types/):
cuatro funciones que no hacen nada útil, cuyo único trabajo es tocar `State` y `Block` para
obligar a la extracción a traerlos. `cargo hax into lean` corrió **sin un solo error** y
escribió los catorce archivos.

Y entra con todo su equipaje: `sha2`, `sha2-asm` (sí, con ensamblador), `serde`, y las tres
bibliotecas de SSZ (`libssz`, `libssz-merkle`, `libssz-types`) más `ethlambda-ssz-tree`.
La predicción razonable era que `sha2` lo iba a trabar. No lo trabó.

> ⚠️ **Lo que todavía no verificamos**: que los cuerpos no salgan en `sorry` y que `State`
> tenga sus diez campos de verdad. Que la extracción corra sin errores y que lo extraído
> sirva son dos cosas distintas — la misma distinción que nos ordenó el experimento
> anterior. Es un chequeo de cinco minutos sobre `Types.lean` y `Funs.lean`.

Con la salvedad de arriba: **la B deja de ser una apuesta a ciegas**. El refactor de
empaquetado —sacar la STF de lean a su propio crate, sin `ethlambda-storage` ni la Beacon
Chain— apunta a algo que sabemos que la herramienta puede digerir. La C queda como plan de
contingencia, no como camino principal.

**Si sale la D**, tenés una propiedad demostrada sobre código de producción. **Si no sale**,
sabés exactamente dónde se traba y por qué — que para Pablo también es un resultado, y
mejor que una opinión.

---

## 6. Y la alternativa barata, que no demuestra nada pero encuentra cosas

Antes de traducir nada: **el oráculo**. Correr una spec en Lean al lado del cliente sobre
los mismos inputs y comparar salidas. Es lo que hace
[`leanerSTFSpec`](leaner-stf-spec.html) contra el Python de EELS.

No demuestra nada —comparar salidas prueba que coincidieron *en los casos que probaste*,
no en todos— pero cuesta muchísimo menos y encuentra discrepancias desde el primer día.
Para eso sirve que el modelo de [`verified-consensus`](verified-consensus.html) **sea
computable**: lo único que le falta para poder llamarse desde afuera son los `@[export]`.

---

## 7. El experimento: lo que pasó de verdad

Instalamos la cadena de herramientas y la corrimos. `cargo-hax 0.4.2`, `charon nightly-2026.09.02`,
`aeneas build-183e4f0`, sobre Ubuntu 24.04 x86_64, el 23 de octubre de 2026. Tres intentos,
en orden de ambición:

| Intento | Qué apuntamos | Resultado |
|---|---|---|
| 1 | `state_transition` entero | **nada.** Un `dyn Error` en `ethlambda-storage` (dependencia) → *"Dynamic trait types are not supported yet"* → *"Mixed declaration groups"* → 413 errores internos, cero archivos escritos |
| 2 | `fork_choice` (crate propio, 1 dep) | **a medias.** Escribió `Funs.lean` y `Types.lean`. Firmas completas, `HashMap` incluido. Pero el `max_by_key` de `lib.rs:48` → *"Can't end abstraction 5 as it is set as non-endable"*. Cuerpos en `sorry` |
| 3 | `justified_slots_ops.rs` en crate propio | **limpio.** 19 definiciones, **cero `sorry`, cero errores**, plantilla de modelado vacía — y **`lake build` pasa**: 1737 jobs, sin un solo error de tipos |

El crate del intento 3 quedó guardado: está en
[`tooling/hax-lean/ejemplo-jsops/`](../tooling/hax-lean/ejemplo-jsops/), con el archivo
original de ethlambda copiado tal cual (atribución MIT en el encabezado) y sustitutos
locales para `JustifiedSlots` y `Error`, para que el crate se sostenga solo.

### Qué son esas 19 definiciones, sin inflar el número

Conviene desarmarlo, porque la cifra grande se presta a vender más de lo que hay:

| De dónde sale | Cuántas |
|---|---|
| El tipo sustituto `JustifiedSlots` que escribimos nosotros para que el crate se sostenga solo | **8** |
| El closure de `relative_index` | **2** |
| **Código real de ethlambda** | **9** |

O sea: **nueve definiciones de ellos**, no diecinueve. Las otras diez son andamiaje nuestro
y maquinaria de Aeneas.

### Y una corrección a la regla del límite

**El closure de `relative_index` se tradujo perfecto.** Es el de un `.map()` sobre un
`Option` de números, que no presta nada. Así que la regla fina no es *"los closures no
pasan"* sino **"los closures que se quedan con una referencia hacia adentro de una
colección no pasan"**. Esa es exactamente la diferencia entre ese `.map()` inofensivo y el
`max_by_key` del fork choice.

**Lo que el intento 3 nos enseñó sobre la forma del Lean generado.** Cada `for` de Rust no
sale como un loop: sale como **tres definiciones** — `<funcion>_loop.body`,
`<funcion>_loop` y `<funcion>`. El cuerpo, el loop y quien lo llama. Eso importa para los
teoremas 1 y 3 del cuadro de arriba: demostrar algo sobre `extend_to_slot` va a ser
demostrar primero un invariante sobre `extend_to_slot_loop.body` y después subir por
inducción. Es más trabajo del que sugiere la tabla. Todo viene envuelto en `RustM`, que es el `Result`
de Aeneas con otro nombre: cada paso contempla el caso de falla, porque en Lean toda
función tiene que ser total y una función Rust puede entrar en pánico. Así se ve una de las
19, con el `checked_sub` y el `?` traducidos:

```lean
def relative_index (target_slot : Std.U64) (finalized_slot : Std.U64) :
  RustM (core.option.Option Std.Usize) := do
  let o ← core.num.U64.checked_sub target_slot finalized_slot
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | ControlFlow.Continue val => ...
  | ControlFlow.Break residual => ...
```

### El build, que es la mitad que faltaba

Generar Lean sin `sorry` y que Lean lo acepte son dos cosas distintas. `lake build` cerró
con **1737 jobs y cero errores**, con `Jsops.Extraction.Funs` entre ellos. Tres cosas para
quien lo repita:

- **Mathlib es dependencia** del proyecto que arma Aeneas, con todo su séquito (`aesop`,
  `batteries`, `proofwidgets`). Pero no hay que compilarla: lake se baja los artefactos ya
  compilados solo (*"Using cache (Azure)"*, 8542 archivos). Son unos **7,7 GB** que caen en
  `proofs/lean/.lake` — borrables apenas terminás.
- **`Jsops/Verification/ProofObligations.lean` viene vacío.** Es un placeholder con un
  comentario; hax lo crea una vez y no lo vuelve a tocar. No hay obligaciones automáticas
  derivadas de los `.expect()`: ese archivo es donde **vos** escribís los enunciados. Es la
  confirmación más literal de lo que dice el cuadro comparativo — la traducción da
  definiciones, los teoremas los pone un humano.
- **Las dos plantillas tienen 27 y 25 líneas, y son todas preámbulo** (imports, `open`s,
  opciones de linter). Cero declaraciones. Entre los imports está `CoreModels`: justamente
  la librería con los modelos que Aeneas trae de las colecciones de `std`, que es *por qué*
  la plantilla queda en blanco.

**Y la moraleja que más caro habría salido no aprender:** con la regla vieja —"el obstáculo
es `std`"— habríamos descartado `justified_slots_ops` por usar `Vec`, que es el único de los
tres que anduvo. La regla útil no es sobre qué biblioteca usás, es sobre **qué hacés con las
referencias**.

---

## 8. El MVP, cerrado el 28 de octubre

**La STF de ethlambda existe en Lean y Lean la acepta.** `lake build` en verde,
1736 jobs, cero errores. El crate está en
[`tooling/hax-lean/mini-stf/`](../tooling/hax-lean/mini-stf/README.md), con el
detalle completo.

Nueve de las doce funciones traducidas con cero `sorry`, entre ellas
`state_transition`, `process_slots`, `process_block`, `process_block_header`,
`is_valid_vote` y `slot_is_justifiable_after`. Y los tipos salieron como
estructuras de verdad: `structure tipos.State`, `tipos.Block`,
`tipos.Checkpoint`.

### Cómo se llegó, que es lo que importa para la próxima

La opción que terminó funcionando no era ninguna de las cinco de la sección 5.
Fue **la C** —tipos escritos a mano— pero con un ingrediente que no teníamos:
`--charon-args="--opaque ..."`. Con eso se le dice a la herramienta que no mire
el cuerpo de una función y emita sólo su firma, lo que permite dejar afuera las
tres funciones problemáticas **sin tocar el código de las otras nueve**.

Seis vueltas, y **ningún obstáculo era predecible leyendo el código**. Cada uno
apareció al correr:

| # | Síntoma | Causa |
|---|---|---|
| 1 | 413 errores, cero archivos | un `dyn Error` en `ethlambda-storage` |
| 2 | *"Early returns inside of loops"* | **dos** `return` adentro de un `for` |
| 3 | error interno de Aeneas, cero archivos | `Iter::find`, **dentro de `core`** |
| 4 | `[Error] Unreachable` en cada derive | `Debug` y `Display` |
| 5 | `Unknown identifier HashMap`, `isqrt`, `mem::take` | **`CoreModels` no cubre todo `core`/`std`** |
| 6 | `repeat_n`, `Vec::extend`, `Option::copied` | lo mismo |

### La corrección que más vale, y es la tercera sobre el mismo tema

Veníamos escribiendo que *"la biblioteca estándar no es el muro"*, porque
`HashMap` aparecía traducido en las firmas. **Eso estaba mal, y el error era de
método**: la extracción saliendo limpia no dice nada sobre si `std` está
cubierto. Aeneas nombra lo que necesita de `core` sin chistar y escribe los
archivos; los nombres que no existen recién aparecen en `lake build`:

```
error: Unknown identifier `std.collections.hash.map.HashMap`
error: Unknown identifier `core.num.U64.isqrt`
```

**La única prueba de que algo está cubierto es que el proyecto Lean compile.**
Dos veces esta semana dimos por bueno un resultado sin llegar hasta ahí.

La formulación correcta, entonces: Aeneas trae modelos escritos a mano de una
parte de `core` y `alloc` en su librería `CoreModels`. Lo que cae fuera de esa
parte hay que modelarlo uno — y no hay forma de saber qué falta sin compilar.

### Los supuestos, con nombre y apellido

24 axiomas, de los cuales **17 son `fmt`** y no los va a tocar ningún teorema.
Los que importan son tres funciones opacas (`process_attestations`,
`serialize_justifications`, `try_finalize`) y cinco funciones de `core` sin
modelo.

⚠️ Entre esas cinco está **`isqrt`**, que es exactamente lo que usa
`slot_is_justifiable_after` para detectar cuadrados perfectos. O sea que **el
teorema que esta misma nota recomendaba como primer objetivo está bloqueado**
hasta reemplazar ese axioma por una definición sobre `Nat.sqrt`. Es el primer
supuesto a cerrar.

### La auditoría de axiomas, hecha el 30 de octubre

`#print axioms` sobre cada función. Salida completa en
[`tooling/hax-lean/mini-stf/axiomas.txt`](../tooling/hax-lean/mini-stf/axiomas.txt).

**Tres funciones salen con los tres axiomas estándar de Lean y nada más.** Están
demostrablemente limpias, y son las mejores candidatas para el primer teorema:

```
mini_stf.stf.process_slots
mini_stf.stf.attestation_data_matches_chain
mini_stf.justified_slots_ops.is_slot_justified
```

**`isqrt` bloquea exactamente dos**: `slot_is_justifiable_after` y `is_valid_vote`. Y hay
que ser preciso con qué significa: un axioma sin definición es una función de la que no se
sabe *nada*, ni siquiera que es determinista sobre un mismo argumento. El teorema de los
números pronic que recomendaba la sección 5 no es difícil de demostrar — es **imposible**
hasta reemplazar ese axioma por una definición sobre `Nat.sqrt`.

**Y apareció lo que no esperábamos: cuatro `_native.decide.ax_*`.** Son *native axioms*,
donde el resultado lo calcula el compilador de Lean y el kernel no revisa nada. Nadie los
pidió: los metió Aeneas solo. Es un caso distinto de los cuatro repos del cuadro, donde el
atajo siempre es rastreable hasta una línea que escribió un humano. Está desarrollado en
[`repos-comparados.md`](repos-comparados.md), sección "El quinto caso".

La base de confianza, entonces:

| Categoría | Qué hay | Gravedad |
|---|---|---|
| Estándar de Lean | `propext`, `Classical.choice`, `Quot.sound` | ninguna |
| Agujero elegido | `stf.process_attestations` | conocida |
| `core` sin modelo | `isqrt`, `mem.take`, `bool.then` | **`isqrt` bloquea** |
| Formateo | `FueraDeCapacidad…fmt` | ruido |
| **Nativos** | 4 × `_native.decide.ax_*` | **el kernel no los verificó** |

### Y una línea de ethlambda que sí cambiamos

En `process_slots`, `historical_block_hashes.extend(std::iter::repeat_n(...))`
pasó a ser un `for` con `push`. `repeat_n` y `Vec::extend` no están en
`CoreModels`. Es el único cambio al cuerpo del código de ellos, y queda anotado
como cambio, no como copia.

---

## 9. El primer teorema, 30 de octubre

Dos cosas pasaron después de la auditoría de la sección 8.

**`isqrt` dejó de ser un axioma.** Se reemplazó por una definición sobre
`Nat.sqrt`, que ya está en el núcleo de Lean con sus lemas demostrados en
Mathlib. La cota que pedía el constructor —que la raíz entre en 64 bits— sale de
`Nat.sqrt_le_self`. Con eso, **`slot_is_justifiable_after` e `is_valid_vote`
pasaron a depender sólo de los tres axiomas estándar**, y las funciones limpias
son cinco en vez de tres.

El supuesto no desapareció, cambió de forma: seguimos creyendo que el
`u64::isqrt` de Rust calcula lo mismo que `Nat.sqrt`. La documentación de Rust
dice "raíz cuadrada entera truncada", que es exactamente eso. Antes era un
agujero mudo; ahora es una afirmación escrita, con su cita al lado.

**Y con eso se pudo escribir el primer teorema.** El comentario del código de
ethlambda afirma que detectar números pronic preguntando si `4·delta + 1` es un
cuadrado perfecto es correcto. Eso ahora está demostrado:

```lean
theorem pronic_iff_cuadrado (n : ℕ) :
    (∃ m, m * m = 4 * n + 1) ↔ (∃ k, n = k * (k + 1))
```

Y depende **sólo de `propext`, `Classical.choice` y `Quot.sound`**. Ni native
axioms ni agujeros nuestros.

### Lo que encontró: un chequeo que sobra

El código pregunta dos cosas sobre `m = 4·delta + 1`: que sea cuadrado perfecto
**y** que sea impar. La segunda nunca puede fallar si la primera pasa, porque
`4·delta + 1` es impar siempre y entonces su raíz también. Está demostrado en
`chequeo_de_paridad_redundante`.

No es un bug, el resultado es correcto. Pero es una condición que siempre se
cumple, y **apareció al escribir el enunciado** — que es exactamente para lo que
sirve este ejercicio. Un humano leyendo el código ve dos chequeos y asume que
los dos hacen algo.

### Lo que todavía no está demostrado

Los dos teoremas son sobre `ℕ`: demuestran **el contenido matemático del
comentario**, no una propiedad de la función generada. Falta el puente que diga
qué devuelve `slot_is_justifiable_after` para cada entrada.

Y ahí va a aparecer algo que ya se ve leyendo el Lean generado: `checked_mul
delta 4` falla cuando `delta ≥ 2^62`, así que la función devuelve `false` para
deltas pronic muy grandes. Inalcanzable en la práctica, pero el enunciado tiene
que decirlo — y una condición de borde que nadie había escrito es justo el tipo
de resultado que justifica todo esto.

---

*Medido el 22 de octubre de 2026 sobre `lambdaclass/ethlambda` en el commit `22d1a72`,
clon de solo lectura. Los conteos de `async`/`unsafe`/locks son sobre `src/` de cada
crate, con `grep`; el `unsafe` que aparece en `state_transition` es una palabra dentro de
un comentario que cita la spec, no código.*
