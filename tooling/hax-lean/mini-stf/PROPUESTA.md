# La transición de estado de ethlambda, en Lean

Este crate es una demostración funcionando. Contiene la función de transición
de estado de `crates/blockchain/state_transition`, y al correrle la cadena de
herramientas de Rust a Lean produce un proyecto Lean que chequea: las doce
funciones traducidas, cero `sorry`.

No es un fork ni una reimplementación. Ocho de las doce funciones están sin
cambios salvo comentarios; las otras cuatro se reescribieron, y este documento
dice exactamente qué necesitó cada una y por qué.

Trae además teoremas, porque una traducción que chequea es sólo la mitad de la
pregunta — la otra mitad es si se puede demostrar algo sobre lo que sale. No son
un reclamo de cobertura contra ningún catálogo. Lo que sí cubren es la propiedad
que la suite de ustedes afirma por ejemplo después del congelamiento del devnet
en el slot 27984.

Cada número de acá salió de una corrida.

## Contra qué versión está

`lambdaclass/ethlambda`, MIT. El archivo se copió el 28 oct 2026 de
`crates/blockchain/state_transition/src/lib.rs`, en `35c074b` *(feat: add
Beacon Chain support, #661, 2026-10-20)* — el commit que lo tocó por última
vez, no lo que `main` tuviera en ese momento.

Chequeado de nuevo el 6 nov 2026: el archivo en `main` es byte a byte idéntico
al de `35c074b`. Comparamos contenidos en vez de rastrear commits, porque el
contenido es de lo que dependen los números. El mismo chequeo, para que no
tengan que creernos:

```bash
P=crates/blockchain/state_transition/src/lib.rs
curl -sS https://raw.githubusercontent.com/lambdaclass/ethlambda/35c074b/$P | sha256sum
curl -sS https://raw.githubusercontent.com/lambdaclass/ethlambda/main/$P | sha256sum
```

Si esos hashes difieren, toda cifra de abajo está vieja y el diff hay que
rehacerlo.

Cadena de herramientas: `cargo-hax 0.4.2`, `charon nightly-2026.09.02`,
`aeneas build-183e4f0`, y `elan` para Lean. Corrimos todo en x86-64 Linux; la
cadena no soporta macOS Intel, así que usamos un contenedor `linux/amd64`.

## Háganle el diff ustedes

El crate está en `tooling/hax-lean/mini-stf/` en
[`EdVeralli/eth-crypto-study`](https://github.com/EdVeralli/eth-crypto-study).
Comparen `src/stf.rs` contra su `lib.rs`:

```bash
diff -u ethlambda/crates/blockchain/state_transition/src/lib.rs \
        mini-stf/src/stf.rs
```

De ahí salen cuatro clases de diferencia:

1. el bloque de `use` — nuestros tipos vienen de este crate y no del de ustedes;
2. diecinueve funciones auxiliares, nuevas y nuestras, que las funciones
   reescritas llaman;
3. las cuatro funciones de la tabla de **Qué cambió de su código**;
4. dos tests nuestros agregados a su módulo de tests, que vive en este archivo.

Los comentarios difieren en todo el archivo, así que para chequear
específicamente la afirmación de "ocho de doce sin cambios", saquen primero
comentarios y líneas en blanco:

```bash
plain() { sed 's://.*::' "$1" | grep -v '^[[:space:]]*$'; }
diff -u <(plain ethlambda/.../lib.rs) <(plain mini-stf/src/stf.rs)
```

Es un instrumento tosco — también cortaría un `//` dentro de un literal de
cadena, aunque no hay ninguno en ninguno de los dos archivos. Sirve para leer,
no para CI.

## Cómo correrlo

### El entorno

La cadena de herramientas no tiene build para macOS Intel, así que la corrimos
en un contenedor. El `Dockerfile` está un nivel arriba de este crate, en
`tooling/hax-lean/`, y fija `cargo-hax` en **0.4.2** — la versión contra la que
se midió cada número de este documento.

Ese pin importa más de lo que parece: `0.5.0` ya está publicada, así que un
build sin versión fija hoy la instalaría y no reproduciría este entorno. Las
versiones de Charon y de Aeneas se desprenden de la de hax, que las baja sola;
la de Lean la fija el `lean-toolchain` de cada proyecto, que sí está en control
de versiones.

```bash
cd tooling/hax-lean
docker build --platform linux/amd64 -t hax-lean .
docker run --platform linux/amd64 -it \
  -v "$PWD/mini-stf:/work" \
  -v hax-cargo:/root/.cargo/registry \
  -v hax-cache:/root/.cache/hax \
  -v hax-elan:/root/.elan \
  hax-lean bash
```

El primer build tarda: compila `cargo-hax` y después precalienta Charon, Aeneas
y la nightly de Rust que Charon pide — varios GB en total. Los volúmenes con
nombre hacen que las corridas siguientes no bajen nada. Si ya tienen las tres
herramientas en esas versiones, saltéenlo y vayan derecho al comando de abajo.

### Un comando

Desde la raíz del crate:

```bash
bash regenerar.sh
```

Hace tres cosas en orden, y **la del medio no es opcional**:

1. extraer — `cargo hax into lean`, con los dos flags de abajo;
2. restaurar el Lean escrito a mano;
3. `lake build`.

El paso 2 existe porque `proofs/` es salida generada y no está en control de
versiones, mientras el Lean que escribimos a mano sí. En un checkout limpio hax
siembra `Assumptions/` desde sus propias plantillas — esqueletos, no nuestros
modelos de `HashMap::get`, `U64::isqrt`, `mem::take` y el resto — así que la
extracción seguida directo de `lake build` falla con identificadores
desconocidos. Lo mismo pasa después de cualquier extracción fallida, que borra
esos archivos. Las tres copias que importan están versionadas:

```
supuestos/TypesExternal.lean    →  proofs/lean/MiniStf/Assumptions/
supuestos/FunsExternal.lean     →  proofs/lean/MiniStf/Assumptions/
teoremas/ProofObligations.lean  →  proofs/lean/MiniStf/Verification/
```

A mano, los mismos tres pasos son:

```bash
cargo hax into lean \
  --charon-args="--opaque '{impl core::fmt::Debug for _}' \
                 --opaque '{impl core::fmt::Display for _}'"
cp supuestos/TypesExternal.lean supuestos/FunsExternal.lean \
   proofs/lean/MiniStf/Assumptions/
cp teoremas/ProofObligations.lean proofs/lean/MiniStf/Verification/
cd proofs/lean && lake build
```

Los dos `--opaque` son imprescindibles: sin ellos cada `#[derive(Debug)]` falla
con `[Error] Unreachable`, y sacar el derive no es salida porque `.expect()` lo
necesita. El primer `lake build` compila además Aeneas, `CoreModels` y la
biblioteca de tácticas de hax, lo que tarda un rato; los siguientes no.

Una corrida exitosa termina en `Build completed successfully (1742 jobs)`, sin
`sorry` y con las doce funciones presentes como `def` en
`proofs/lean/MiniStf/Extraction/Funs.lean`.

Los tests — sus seis más dos nuestros:

```bash
cargo test
```

Pasan ocho.

## Qué contiene el crate

Todo, con las líneas tal como se entrega.

| Archivo | Líneas | Origen |
|---|---|---|
| `src/stf.rs` | 1484 | **de ustedes** — `state_transition/src/lib.rs`: ocho de doce funciones sin cambios, cuatro reescritas, diecinueve auxiliares nuestras, y su módulo de tests de 437 líneas con dos tests agregados. |
| `src/justified_slots_ops.rs` | 90 | **de ustedes** — sin cambios salvo las líneas de `use`. |
| `src/tipos.rs` | 431 | **sus definiciones de tipos**, sin los derives de serialización, más nuestro `hash_tree_root` sustituto. |
| `src/ssz.rs` | 154 | nuestro — sustitutos de `SszList` y `SszBitlist`. |
| `src/mapa.rs` | 245 | nuestro — una lista de asociación que reemplaza un `HashMap`. |
| `src/stubs.rs` | 49 | nuestro — `tracing` y métricas que no hacen nada. |
| `src/lib.rs` | 51 | nuestro — cableado de módulos. |
| `Cargo.toml` | 10 | nuestro. |
| `Cargo.lock` | 65 | nuestro, y versionado a propósito — fija las versiones de las dependencias, la misma preocupación que el pin de `cargo-hax` en el Dockerfile. |
| `regenerar.sh` | 36 | nuestro — extraer, restaurar, compilar. |
| `supuestos/TypesExternal.lean` | 49 | **nuestro, imprescindible** — modelos de `HashMap` y `RandomState`. |
| `supuestos/FunsExternal.lean` | 309 | **nuestro, imprescindible** — modelos de las operaciones de `core`/`std` que `CoreModels` no cubre, más diecisiete firmas de `fmt` corregidas a mano. |
| `supuestos/RevisarAxiomas.lean` | 25 | nuestro — imprime la base de confianza de cada teorema. |
| `teoremas/ProofObligations.lean` | 686 | nuestro — los teoremas. |
| `axiomas.txt` | 112 | nuestro — la salida de `#print axioms`, para poder leer la base de confianza sin compilar. |
| `r2.log`, `r3.log`, `r4.log`, `resultado.log` | 16 KB | nuestros — salida cruda de los primeros intentos de extracción, guardada para el registro. Las reglas que salieron de ahí están escritas en el `README.md`. |
| `README.md` | 604 | nuestro — la bitácora: cada obstáculo en el orden en que lo encontramos. |
| `PROPUESTA.md` | — | nuestro — este documento. |
| `PROPOSAL.md` | — | nuestro — el mismo documento en inglés; los dos se mantienen al día juntos. |

Los dos archivos marcados **imprescindible** no son extras opcionales; ver
**Cómo correrlo**.

## Qué cambió de su código

Contado sobre las doce funciones, sin comentarios ni líneas en blanco;
*quitadas* y *agregadas* salen de un diff unificado por función contra
`35c074b`.

| Función | Suyas | Nuestras | Quitadas | Agregadas |
|---|---|---|---|---|
| `state_transition` | 13 | 13 | — | — |
| `process_slots` | 16 | 16 | — | — |
| `process_block` | 6 | 6 | — | — |
| `is_valid_vote` | 28 | 28 | — | — |
| `attestation_data_matches_chain` | 23 | 23 | — | — |
| `slot_is_justifiable_after` | 11 | 11 | — | — |
| `is_proposer` | 3 | 3 | — | — |
| `current_proposer` | 3 | 3 | — | — |
| `process_block_header` | 68 | 70 | 1 | 3 |
| `try_finalize` | 43 | 48 | 15 | 20 |
| `serialize_justifications` | 28 | 20 | 16 | 8 |
| `process_attestations` | 110 | 96 | 79 | 65 |
| **total** | **352** | **337** | **111** | **96** |

Más diecinueve funciones auxiliares nuestras, 179 líneas en total.

### Las reglas detrás de cada cambio

Ninguna de éstas está en el manual de hax. Cada una costó una corrida.

**Los closures de iteradores no traducen.** Cualquier cosa con `.iter().map()`,
`.filter()`, `.any()`, `.find()`, `.enumerate()` o `.retain()` pasa a ser un
loop con índices. `.find()` es el peor de todos: falla *adentro de `core`*, con
un error de lifetimes que aborta la extracción entera y no escribe ningún
archivo.

**`return` adentro de un `for` no está soportado.** `process_attestations` tenía
dos `return Err(...)` literales adentro del loop, más el `?` de `is_valid_vote`,
que propaga de la misma forma. Convertirlos en `break` tampoco alcanza: un loop
con cuatro salidas —el final normal más tres breaks— falla con "Could not match
the contexts". El loop ahora tiene una sola salida y lleva el error en una
bandera.

**Un loop adentro de otro loop no traduce**, pero el mismo loop movido a su
propia función sí. De ahí que haya tantas funciones auxiliares chicas.

**Un loop que muta una colección no puede atar una referencia tomada de otra.**
Cualquiera de las dos por separado está bien; juntas producen "Internal error".
De ahí que cada lectura pase por una auxiliar que devuelve una copia.

**`HashMap` no se puede iterar.** `justifications` se lee con `.retain()`,
`.keys()` e indexando, y un `HashMap` no tiene orden por el cual indexar, así
que pasó a ser una lista de asociación (`src/mapa.rs`). `root_to_slot` sigue
siendo un `HashMap`: se construye con hasta `HISTORICAL_ROOTS_LIMIT` entradas y
sólo se consulta con `get`, nunca se itera.

**`std::iter::repeat_n` y `Vec::extend` no tienen modelo**, que es lo que
explica el cambio chico de `process_block_header`.

### Un bug que la reescritura introdujo, y cómo lo encontramos

Sus seis tests pasan antes y después de cada cambio de arriba. Ésa es la
evidencia que tenemos, y es más débil de lo que parece.

`process_attestations` tiene tres salidas de error adentro de su loop: el `?` de
`is_valid_vote`, `EmptyAggregationBits` y `AggregationBitsOutOfBounds`. Como
Aeneas rechaza los early returns adentro de loops, la nuestra junta el error en
una bandera — y la primera versión de esa reescritura llenaba la bandera y nunca
la leía. Devolvía `Ok(())` sobre un bloque que su código rechaza, y llamaba a
`serialize_justifications`, al que su código nunca llega cuando corta. Dos
divergencias.

Los seis tests pasaron igual. Los dos que chequean errores
(`rejects_justification_votes_length_mismatch`,
`rejects_empty_validator_registry`) cubren las salidas de **antes** del loop;
ninguno cubre las tres de adentro. Así que agregamos dos que sí:

| Test | Qué fuerza |
|---|---|
| `process_attestations_rejects_empty_aggregation_bits` | el voto válido de su test de regresión, sin ningún bit prendido → `EmptyAggregationBits` |
| `process_attestations_rejects_an_out_of_range_bit` | bits de largo 6 con el índice 5 prendido sobre 4 validadores → `AggregationBitsOutOfBounds { index: 5, validator_count: 4 }` |

Los dos se chequearon contra el defecto: sacando el arreglo, sus seis pasan y
estos dos fallan.

## Qué recibe

`teoremas/ProofObligations.lean` tiene siete resultados con nombre:

| Resultado | Qué es |
|---|---|
| `pronic_iff_cuadrado` | la identidad que afirma su propio comentario |
| `chequeo_de_paridad_redundante` | su corolario: el chequeo de paridad de al lado nunca puede fallar |
| `try_finalize_no_retrocede` | la finalidad no retrocede |
| `try_finalize_no_toca_justified` | `try_finalize` no toca `latest_justified` |
| `ST3.process_attestations_loop_no_retrocede` | la justificación no retrocede, sobre una vuelta del loop |
| `ST3.process_attestations_no_retrocede` | lo mismo, sobre la función entera |
| `bind_da_ok` | una herramienta: abre un bind de `RustM` |

No se eligieron por cantidad. Entre todos cubren aritmética, ramificación y
actualización de registros, inducción sobre un loop, y composición a lo largo de
una función entera con salidas tempranas y un `match`.

### La aritmética

Su comentario en `slot_is_justifiable_after` afirma una identidad:

```rust
// Mathematical insight: For pronic delta = n(n+1), we have:
//   4*delta + 1 = 4n(n+1) + 1 = (2n+1)^2
```

Ahora es un teorema, apoyado en los tres axiomas estándar de Lean y nada más:

```lean
theorem pronic_iff_cuadrado (n : ℕ) :
    (∃ m, m * m = 4 * n + 1) ↔ (∃ k, n = k * (k + 1))
```

Escribirlo destapó algo chico: el chequeo de paridad de al lado (`m % 2 == 1`)
**nunca puede fallar**, porque `4·delta + 1` siempre es impar y su raíz también.
No es un bug, pero es una condición que no hace nada.

### La finalidad no retrocede

```lean
theorem try_finalize_no_retrocede
    (state state' : tipos.State) (source target : tipos.Checkpoint) ... :
    stf.try_finalize state source target j rts = ok (state', j') →
    state.latest_finalized.slot ≤ state'.latest_finalized.slot
```

La demostración es corta porque su guarda **es** la propiedad:

```rust
if source.slot <= state.latest_finalized.slot { return; }
...
state.latest_finalized = source;
```

Va acompañado de un resultado que la otra mitad necesita:

```lean
theorem try_finalize_no_toca_justified
    ... :
    stf.try_finalize state source target j rts = ok (state', j') →
    state'.latest_justified = state.latest_justified
```

`try_finalize` se llama desde adentro del loop que mueve `latest_justified`, así
que demostrar que ese campo no retrocede ahí exige saber que esta función no lo
toca.

### La justificación no retrocede

`latest_justified` se mueve adentro del loop, así que éste necesitó inducción
sobre el loop. Está demostrado no sólo sobre el loop sino sobre la función que
ustedes llaman:

```lean
theorem ST3.process_attestations_no_retrocede
    (state state' : tipos.State) (atts : ...) (res : ...) :
    stf.process_attestations state atts = ok (res, state') →
    state.latest_justified.slot ≤ state'.latest_justified.slot
```

Atención a la hipótesis: estos enunciados son **condicionales a que la llamada
devuelva `ok`**. No dicen nada sobre las entradas en las que la transición
falla — y ésa es la forma correcta y no una debilitada, porque una transición
que falla rechaza el bloque y no deja estado nuevo del cual afirmar algo.

Ésta es la propiedad que su propio test afirma por ejemplo, en
`latest_justified_does_not_regress_within_block`. Su comentario dice por qué
existe: en el devnet, en el slot 27984, un bloque llevó tres attestations con
supermayoría apuntando a los slots 27978, 27981 y 27974 en ese orden, la
asignación sin guarda se quedó con la última, y la cadena se congeló. El test
cubre ese escenario; el teorema cubre toda entrada que la transición acepte.

### Qué es esto contra el catálogo, dicho exacto

`ST-3` en
[`NyxFoundation/formal-leanSpec`](https://github.com/NyxFoundation/formal-leanSpec)
está enunciada sobre `State.transition` — la transición de un bloque entera — y
acota los dos slots de checkpoint a la vez. Lo que está demostrado acá es cada
una de sus dos mitades sobre el componente donde ese campo efectivamente se
mueve: la justificación sobre `process_attestations`, la finalidad sobre
`try_finalize`. **Eso no es la proposición del catálogo, y no estamos afirmando
que lo sea.**

Subir las dos a `state_transition` es el paso que la convertiría en eso, y
necesita tres lemas que no escribimos: que `process_slots` no toque los
checkpoints, que `process_block_header` no los baje, y la mitad de finalidad
subida por el loop de attestations. Hay un reparo que el catálogo ya avisa y
vale pasarlo: el anclaje de génesis del primer bloque fuerza los checkpoints a
slot 0, lo que hace **falso** el enunciado desnudo para estados adversarios, y
la formalización carga una hipótesis extra `AnchorWF` justamente por eso. Un
lift que la ignore no cierra.

Ninguna de las dos mitades se eligió porque pareciera demostrable. `ST-3` es una
de treinta y cinco proposiciones de ese catálogo — siete sobre la transición de
estado, el resto sobre fork choice, SSZ, el validador, red, storage y sync. El
enunciado es anterior a nuestro trabajo sobre él, y eso importa: elegir las
propias propiedades vuelve el ejercicio circular.

### La base de confianza

`#print axioms` sobre cada resultado, con la salida en `axiomas.txt`:

| Resultado | Total | De Lean | Nativos | Declaraciones |
|---|---|---|---|---|
| los dos de aritmética | 3 | 3 | — | — |
| `bind_da_ok` | 1 | 1 | — | — |
| los dos de `try_finalize` | 13 | 3 | 3 | 7 |
| el del loop | 14 | 3 | 4 | 7 |
| `process_attestations` | 20 | 3 | 7 | 10 |

Tres categorías, con tres pesos distintos.

**Los tres de Lean** — `propext`, `Classical.choice`, `Quot.sound` — son el piso
de cualquier demostración clásica y no dicen nada sobre este código.

**Los nativos** son los `_native.decide.ax_*`: hechos que el núcleo de Lean no
chequeó, computados por el compilador. Aparecen siete distintos en todo el
build. No son nuestros ni de ustedes. Definir una función en Lean puede exigir
demostraciones —un literal escalar carga la prueba de que entra en su tipo,
indexar carga la de que el índice está en rango— y Aeneas genera esas
obligaciones al traducir, y después descarga las de cotas con `native_decide`.
La elección está en su biblioteca de tácticas
(`Tactic/Simproc/BvSimprocs.lean`, `Tactic/Step/StepArraySpec.lean`), y no hay
flag que la apague. Los nombres llevan **sus** funciones adelante porque es
donde apareció cada uno, no porque alguien lo haya puesto ahí.

Llegan con las **definiciones traducidas**, antes de que exista un teorema:

```
#print axioms mini_stf.stf.try_finalize   -- un `def`, sin teorema de por medio
```

devuelve los mismos trece axiomas que nuestro teorema sobre `try_finalize`, uno
por uno. Traduzcan la STF con esta cadena de herramientas y no demuestren nada,
y ya los tienen; demostrar encima no ensancha la base de confianza en una sola
entrada. Lo que no hicimos fue abrir cada uno de los siete para nombrar el hecho
que descarga.

**Las declaraciones** son nuestras, en `supuestos/FunsExternal.lean`:
veintiocho axiomas que son firma y nada más — el `get`, `insert` y `new` de
`HashMap`, los tipos de trait `Borrow` y `BuildHasher`, el `cmp` y `hash` de
`[T; N]`, `mem::take`, `bool::then`, y diecisiete stubs de `Debug::fmt`. Existen
para que el Lean generado compile: `try_finalize` llama a `root_to_slot.get(…)`,
Aeneas nombra `HashMap::get` en la salida, `CoreModels` no tiene modelo para él,
y sin la declaración el módulo muere con `Unknown identifier` y no compila nada.

Es un agujero más leve que los axiomas nativos. Un axioma que no afirma nada no
rinde nada: no se puede derivar algo falso de él porque no se puede derivar
nada. Lo que cuesta es alcance — cualquier propiedad que dependa de cómo se
comporta el mapa queda fuera. Modelos **con** contenido comprarían esas
propiedades al precio de afirmar cosas que podrían estar mal, y declinamos ese
canje.

La única afirmación real que hacemos es `U64::isqrt`, modelado como `Nat.sqrt`.
Las dos son el piso de la raíz cuadrada, así que le creemos, pero es nuestra
afirmación y no algo que la cadena de herramientas verificó. `HashMap` también
recibe una representación en `TypesExternal.lean` —una lista de pares— pero
`get` e `insert` siguen opacos por encima, así que ahí no se afirma ningún
comportamiento.

Ninguna de las veintiocho carga peso en los teoremas de arriba: las propiedades
salen de las guardas y de las asignaciones, no de lo que haga el mapa, el hash o
el formateador. Eso es una afirmación sobre las demostraciones, leída de ellas.
`#print axioms` dice de qué depende un teorema, no si se apoya en el
comportamiento de esa dependencia, y esa distinción nos toca argumentarla a
nosotros y no medirla a la herramienta.

## Cómo demostrar sobre lo traducido

Estos teoremas no se escribieron a mano contra ecuaciones peladas. Hay un flujo
de trabajo para demostrar sobre el Lean que genera hax, aterriza en su `.lake`
en cuanto compilan, y de ahí salió la mayor parte de lo que necesitamos —
[hax.cryspen.com/manual/lean/](https://hax.cryspen.com/manual/lean/). Qué hizo
cada pieza acá:

| Pieza | De dónde | Qué hizo |
|---|---|---|
| `hax_mvcgen` | hax | el caballo de batalla. Parte un programa en condiciones de verificación —más de 250 para el loop de attestations— y atraviesa cada llamada que tenga un lema `@[spec]`. |
| ternas de Hoare y lemas `@[spec]` | hax, sobre `Std.Do` | el idioma: un lema por función, y la táctica nombra el que falta. |
| `Aeneas.Std.loop_spec` | **Aeneas, no hax** | inducción sobre loops. Ésta es la que hay que usar. |
| `Hax.loop_range_spec_unsigned` | hax | probada, descartada — abajo. |
| `--charon-args="--start-from f"` | hax | probada, descartada — ver **Cómo meterlo en su árbol**. |
| `triple_mayThrow_of`, `of_triple_mayThrow` | nuestros | puentes entre una ecuación y una terna de Hoare. |
| `bind_da_ok` | nuestro | abre un bind de `RustM`, para demostraciones hechas por ecuaciones. |

**Conviene el lema de loops de Aeneas antes que el de hax.**
`Hax.loop_range_spec_unsigned` enuncia su obligación del paso con `⇓`, que exige
que el cuerpo **no falle nunca**. Sobre `process_attestations` eso convierte "el
slot justificado no retrocede" en un teorema mucho más grande: ausencia de
pánico en las doce funciones que el cuerpo llama, seis de ellas con loops
propios. `Aeneas.Std.loop_spec` toma una postcondición completa, con ramas de
falla y de divergencia; elegir `PostCond.mayThrow` descarga esas solas, vuelve
irrelevante el desborde de `attestations_processed + 1` y —al tolerar la
divergencia— saca la necesidad de una medida de terminación. De ahí viene la
forma condicional al éxito de los enunciados.

**Dos puentes, y son la parte reutilizable.**

```lean
triple_mayThrow_of : (∀ v, x = ok v → P v) → ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄
of_triple_mayThrow : ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄ → x = ok v → P v
```

`triple_mayThrow_of` es el dual de `bind_da_ok`: convierte un teorema que ya se
tiene **como ecuación** en el lema `@[spec]` que la táctica consume, así un
resultado demostrado por el camino difícil queda usable sin rehacerlo. El otro
sentido devuelve una terna a ecuación, que es como están enunciados los
resultados de arriba. Veintitrés lemas `@[spec]` alimentan las dos
demostraciones del loop; todos menos dos tienen una postcondición trivialmente
verdadera, presentes sólo para que la táctica pueda atravesar una llamada que no
puede mover `latest_justified`.

**`hax_mvcgen` se detiene en silencio.** Decide si queda trabajo por la *forma*
del objetivo: `goalNeedsMvcgen` reconoce un `Triple`, un `entails` que lleva un
`wp`, o un `.down` que lleva un `PredTrans.apply`. Un `.down` que lleva un
`WP.wp` pelado no entra en ninguno de los tres, así que la táctica toma el
objetivo por condición de verificación terminada y reporta éxito — dejando el
cuerpo entero de la función envuelto en un solo `wp`. No reporta que falta un
spec, porque nunca lo intentó. Si un objetivo vuelve con un `wp` adentro, la
próxima jugada es suya.

Dos trampas menores de la misma clase. `core.option.Option.is_none` necesita su
propio lema `@[spec]` — es `let b ← is_some self; ok (b = false)`, y sin el lema
la táctica no lo puede atravesar; el loop de attestations encadena cuatro. Y el
spec del iterador está enunciado para la forma literal
`{ start := i, «end» := e }`, así que un `Range` que llega como variable hay que
desarmarlo antes o `mvcgen` no da el primer paso.

**Un axioma muerto puede pisar una definición real, y nada avisa.**
`Assumptions/FunsExternal.lean` todavía declaraba
`axiom stf.process_attestations` y `axiom stf.serialize_justifications` de
cuando las dos eran `--opaque`, con sus firmas viejas. No chocaban con las
definiciones generadas, porque ese archivo declara `stf.foo` mientras el código
generado declara `mini_stf.stf.foo` —dos nombres distintos— y con
`open mini_stf` el ambiguo `stf.foo` resuelve al axioma. Un teorema escrito así
compila, no prueba nada y parece correcto; sólo lo delata `#print axioms`. Los
dos axiomas ya no están, y ninguno aparece en la base de confianza de ningún
resultado de arriba.

El riesgo es estructural y no un descuido: hax siembra ese archivo una sola vez
y después no lo vuelve a mirar, así que al sacar un `--opaque` su axioma queda.
Cuando saquen un `--opaque`, saquen también su axioma.

## Qué les cuesta

**Una regresión de complejidad.** La búsqueda en `justifications` pasa de
constante a lineal. En la práctica ese mapa guarda las raíces esperando
finalización, que son pocas — pero el tipo permite hasta
`HISTORICAL_ROOTS_LIMIT` entradas, así que con la finalización estancada mucho
tiempo es una regresión real.

**Código menos idiomático.** Un `for` con índices donde había
`.iter().filter().count()` es más feo y más fácil de leer mal. Eso es costo de
mantenimiento, y es el precio del ejercicio.

## Cómo meterlo en su árbol

El crate funciona tal como se entrega: lo clonan, corren `bash regenerar.sh`, y
la STF está en Lean. Nada de él queda pendiente de nuestro lado.

Si lo meten en `ethlambda` es decisión suya, y hay dos cosas en el camino.
Ninguna es código; las dos son empaquetado.

**La clausura de dependencias tiene que estar libre de `dyn`.**
`state_transition` depende de `ethlambda-storage`, y un solo `dyn Error` en esa
dependencia aborta la extracción: 413 errores, cero archivos escritos. Charon
compila el crate *y todas sus dependencias*, pero Aeneas emite definiciones sólo
del crate local, así que se heredan las fallas de una dependencia sin heredar
sus definiciones.

**Los tipos tienen que vivir en el crate que se extrae.** Es la misma asimetría
vista del otro lado, y es la razón por la que `src/tipos.rs` es una copia de sus
definiciones y no un `use`. Chequeamos si la cadena de herramientas ofrece una
forma de evitar la copia, sobre un crate chico que no hacía más que tocar
`State` y `Block` de `ethlambda-types`. El manual de hax documenta
`--charon-args="--start-from <función>"`, que extrae una función *"along with
all its dependencies"* — y eso vale para la cadena de llamadas, no para los
tipos. La función salió traducida, el tipo no, y `TypesExternal_Template.lean`
salió vacío, así que la cadena ni siquiera pide el tipo como externo. El nombre
que cuelga aparece en el `lake build`, no en la extracción. `--start-from`
cambia qué ítems emite Charon, no de qué crate define Aeneas, así que la copia
no es un atajo que tomamos: es la única ruta que la cadena deja.

El costo de la copia es la deriva. Si `State` cambia, alguien tiene que
sincronizar `src/tipos.rs`. Los dos problemas desaparecen juntos si los tipos y
la STF terminan en un mismo crate, que es además lo que haría que el código
verificado **sea** el código de producción.

## Límites honestos

**El hash no es SSZ.** `hash_tree_root` acá es un hash polinomial escrito en el
subconjunto traducible. Da raíces distintas para estados distintos, que es todo
lo que la STF le pide, pero no es interoperable. Del lado de Lean el tratamiento
correcto es declararlo opaco y cargar la inyectividad como hipótesis explícita.

**`source.slot + 1` puede desbordar.** Enunciar el teorema de `try_finalize`
como terna de Hoare en vez de como ecuación destapó esto: con
`source.slot = u64::MAX`, el incremento que alimenta `slot_is_justifiable_after`
entra en pánico en un build de debug. La forma ecuacional lo esconde, porque
asume que la llamada devolvió `ok`. Ningún slot va a llegar ahí de manera
realista, y la guarda de arriba exige
`source.slot > state.latest_finalized.slot`, así que no es un bug vivo — pero es
una precondición no enunciada, y pueden preferir `checked_add` o una forma
saturante.

**La base de confianza no está vacía**, y lo que hay en ella está detallado en
**La base de confianza**, arriba: siete axiomas nativos que vienen con la
traducción, veintiocho declaraciones nuestras que no afirman nada, y una
afirmación de modelado que sí hacemos.
