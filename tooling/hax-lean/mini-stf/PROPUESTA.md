# La transición de estado de ethlambda, en Lean

Este crate es un ejemplo que funciona de punta a punta. Contiene la función de
transición de estado de `crates/blockchain/state_transition`, y al correrle la
cadena de herramientas de Rust a Lean produce un proyecto Lean que chequea: las
doce funciones traducidas, cero `sorry`.

No es un fork ni una reimplementación. Ocho de las doce funciones están sin
cambios salvo comentarios; las otras cuatro se reescribieron, y este documento
dice exactamente qué necesitó cada una y por qué.

Trae además teoremas, porque una traducción que chequea es sólo la mitad de la
pregunta — la otra mitad es si se puede demostrar algo sobre lo que sale. No son
un reclamo de cobertura contra ningún catálogo. Lo que sí cubren son las
proposiciones que ese catálogo tiene sobre la transición de estado, que son
siete de treinta y cinco. Dos van de punta a punta y son las que más dicen. Una:
ningún slot de checkpoint retrocede a lo largo de la transición de un bloque —
la propiedad que un test de ustedes afirma por ejemplo después del congelamiento
del devnet en el slot 27984. La otra: ningún checkpoint cambia de raíz sin subir
de slot — que sobre su código vale por un motivo distinto al de la
especificación y sólo bajo una hipótesis, porque ante un empate de slots su
código y la especificación eligen distinto. Esa hipótesis se cumple en todo
estado al que se llega desde el génesis, y está demostrado. De las otras cinco,
una no se enuncia porque es trivial; está dicho cuál.

Fuera del catálogo hay cuatro más, sobre la ventana de slots justificados: los
que nos propusimos al mirar su código por primera vez. El último dice que cuando
la finalidad avanza y la ventana se corre, ningún slot justificado se pierde.
Para ese módulo está además la condición exacta bajo la que una de sus
funciones aborta. Y un comentario de su código sobre esa ventana queda
verificado, con la hipótesis que le hacía falta.

Y hay un tercer resultado de punta a punta: la transición entera no entra en
pánico ni se cuelga, en ningún estado al que se llegue desde el génesis. Lo que
sigue pidiendo está escrito: `usize` de 64 bits, que la lista de attestations
del bloque respete la capacidad de su tipo, y algo que este paquete no puede
demostrar, que el hash devuelva.

Y dos resultados sobre un comentario de su código, el que explica por qué
`serialize_justifications` ordena las raíces. El ordenamiento escrito a mano
con que reemplazamos su `.sort()` ordena. Y lo que esa función escribe en el
estado no depende del orden en que el mapa de votos tenía sus entradas.

Cada número de acá salió de una corrida.

## Qué afirma este paquete y qué no

Hay dos cosas distintas, y conviene no mezclarlas.

**La traducción es completa.** Las doce funciones de la STF están en Lean, y
Lean las acepta sin `sorry`. Eso dice que el programa quedó escrito en Lean. No
dice que sea correcto.

**Las demostraciones son de propiedades puntuales.** Un programa no "se
demuestra": se demuestran afirmaciones sobre él. Acá hay ciento dos,
listadas en **Qué recibe**. Cada una dice una cosa precisa, con sus hipótesis a
la vista.

Lo que **no** está demostrado, dicho de una vez:

- **Que el código nunca entre en pánico, sin condiciones.** La ausencia de
  pánico está demostrada para las doce funciones de la transición (`stf.rs`) y
  para las cuatro de la ventana (`justified_slots_ops.rs`), y para la
  transición entera en todo estado alcanzable desde el génesis. Sigue habiendo
  hipótesis escritas. Una no se puede demostrar en este paquete y queda pedida:
  que el hash devuelva. Otra habla del bloque y es el límite de su tipo: que
  la lista de attestations no tenga más de 4096 elementos. En Rust el tipo lo
  garantiza; la traducción a Lean no lo conserva, y hay que pedirlo.
- **Que el código sea equivalente a la especificación.** Sobre estados
  arbitrarios no lo es: encontramos dos puntos donde se comportan distinto, y
  están contados más abajo.
- **Que `ST-7` valga sin condiciones.** Sobre los estados alcanzables desde el
  génesis vale a partir del primer bloque aceptado, que es como la enuncia el
  catálogo: en ese primer bloque la raíz cambia en el slot 0 a propósito. Sobre
  un estado cualquiera necesita además que el justificado esté en el historial,
  y sin eso es falsa sobre su código. Lo demás —los tres invariantes, la cota
  de validadores, `ST-4` y la ausencia de pánico— está demostrado sobre todo
  estado alcanzable, sin excepción.
- **Que el Lean sea fiel al Rust de ustedes.** Son dos eslabones. Que nuestras
  funciones reescritas hacen lo mismo que las originales lo respaldan los
  tests, que corren sobre este crate: los de ustedes cubren tres de las cuatro,
  y la cuarta, `process_block_header`, tiene un test nuestro. Y hay un punto
  donde sabemos que no hacen lo mismo, con una raíz pendiente repetida. Las dos
  cosas están en **Un bug que la reescritura introdujo**. Que la cadena de
  herramientas traduce bien se le cree a la cadena de herramientas.

"Cero `sorry`" quiere decir que no hay ningún hueco en lo que sí se afirma. No
quiere decir que esté todo afirmado.

## Contra qué versión está

`lambdaclass/ethlambda`, MIT. El archivo se copió el 28 oct 2026 de
`crates/blockchain/state_transition/src/lib.rs`, en `35c074b` *(feat: add
Beacon Chain support, #661, 2026-10-20)* — el commit que lo tocó por última
vez, no lo que `main` tuviera en ese momento.

Chequeado de nuevo el 20 nov 2026: el archivo en `main` es byte a byte idéntico
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
cadena de herramientas no soporta macOS Intel, así que usamos un contenedor `linux/amd64`.

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
4. cuatro tests nuestros agregados a su módulo de tests, que vive en este archivo.

Los comentarios difieren en todo el archivo, así que para chequear
específicamente la afirmación de "ocho de doce sin cambios", saquen primero
comentarios y líneas en blanco:

```bash
plain() { sed 's://.*::' "$1" | grep -v '^[[:space:]]*$'; }
diff -u <(plain ethlambda/.../lib.rs) <(plain mini-stf/src/stf.rs)
```

Es un instrumento tosco — también cortaría un `//` dentro de un literal de
texto, aunque no hay ninguno en ninguno de los dos archivos. Sirve para leer,
no para CI.

## Cómo correrlo

### De cero a los teoremas

Lo único que hay que tener instalado es **Docker** y `git`. Rust, Lean, hax,
Charon y Aeneas no se instalan en la máquina: van adentro de la imagen. La
secuencia completa, desde una terminal:

```bash
# 1. bajar el repo
git clone https://github.com/EdVeralli/eth-crypto-study.git
cd eth-crypto-study/tooling/hax-lean

# 2. armar la imagen (una sola vez; tarda y ocupa varios GB)
docker build --platform linux/amd64 -t hax-lean .

# 3. entrar al contenedor, con el crate montado en /work
docker run --platform linux/amd64 -it \
  -v "$PWD/mini-stf:/work" \
  -v hax-cargo:/root/.cargo/registry \
  -v hax-cache:/root/.cache/hax \
  -v hax-elan:/root/.elan \
  hax-lean bash
```

Adentro del contenedor el prompt pasa a `root@…` y ya quedan parados en `/work`,
que es la raíz del crate:

```bash
# 4. los tests de Rust
cargo test

# 5. traducir a Lean y compilar los teoremas
bash regenerar.sh 2>&1 | tee /tmp/build.log

# 6. contar lo que salió
grep -c "depends on axioms" /tmp/build.log
grep -c sorryAx /tmp/build.log
```

Qué tiene que dar cada paso:

| Paso | Resultado |
|---|---|
| 4 | `test result: ok. 12 passed` |
| 5 | `Build completed successfully (1742 jobs).` y después `=== listo ===` (1743 jobs la primera vez sobre un checkout limpio) |
| 6 | `102` — un bloque de axiomas por resultado — y `0` |

No hay un paso aparte de "correr las pruebas". Los teoremas están en
`teoremas/ProofObligations.lean`; el paso 5 copia ese archivo adentro del
proyecto Lean y `lake build` lo chequea entero. Si el build termina en verde,
Lean aceptó las ciento dos demostraciones. Al final imprime de qué axiomas
depende cada una, que es lo que cuenta el paso 6.

Para convencerse de que el chequeo es real, rompan un enunciado a mano. En
`proofs/lean/MiniStf/Verification/ProofObligations.lean`, dentro de
`ST3.state_transition_no_retrocede`, cambien el `≤` de `latest_justified.slot`
por un `<` y corran:

```bash
cd /work/proofs/lean && lake build
```

Falla con `Type mismatch` en ese teorema. `bash regenerar.sh` desde `/work`
vuelve a copiar el archivo bueno y deja todo en verde otra vez.

El resto de esta sección explica cada paso y qué hacer si ya tienen las
herramientas instaladas.

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

`regenerar.sh` copia además `supuestos/RevisarAxiomas.lean` al lado del
lakefile. Ese no es parte del build: es el script que imprime los axiomas de
cada función traducida, y se corre a mano con
`lake env lean RevisarAxiomas.lean`.

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

Una corrida exitosa termina en `Build completed successfully`, sin `sorry` y
con las doce funciones presentes como `def` en
`proofs/lean/MiniStf/Extraction/Funs.lean`. La cuenta de jobs es 1742; el primer
build sobre un checkout limpio da 1743, uno más que todos los que le siguen.

Los tests — sus seis más seis nuestros:

```bash
cargo test
```

Pasan doce.

## Qué contiene el crate

Todo, con las líneas tal como se entrega.

| Archivo | Líneas | Origen |
|---|---|---|
| `src/stf.rs` | 1671 | **de ustedes** — `state_transition/src/lib.rs`: ocho de doce funciones sin cambios, cuatro reescritas, diecinueve auxiliares nuestras, y su módulo de tests de 437 líneas con cuatro tests agregados. |
| `src/justified_slots_ops.rs` | 90 | **de ustedes** — sin cambios salvo las líneas de `use`. |
| `src/tipos.rs` | 510 | **sus definiciones de tipos**, sin los derives de serialización, más nuestro `hash_tree_root` sustituto y `State::from_genesis`, copiada sin cambios. |
| `src/ssz.rs` | 154 | nuestro — sustitutos de `SszList` y `SszBitlist`. |
| `src/mapa.rs` | 245 | nuestro — una lista de asociación que reemplaza un `HashMap`. |
| `src/stubs.rs` | 49 | nuestro — `tracing` y métricas que no hacen nada. |
| `src/lib.rs` | 51 | nuestro — cableado de módulos. |
| `Cargo.toml` | 10 | nuestro. |
| `Cargo.lock` | 65 | nuestro, y versionado a propósito — fija las versiones de las dependencias, la misma preocupación que el pin de `cargo-hax` en el Dockerfile. |
| `regenerar.sh` | 36 | nuestro — extraer, restaurar, compilar. |
| `supuestos/TypesExternal.lean` | 49 | **nuestro, imprescindible** — modelos de `HashMap` y `RandomState`. |
| `supuestos/FunsExternal.lean` | 413 | **nuestro, imprescindible** — modelos de las operaciones de `core`/`std` que `CoreModels` no cubre, más diecisiete firmas de `fmt` corregidas a mano. |
| `supuestos/RevisarAxiomas.lean` | 26 | nuestro — imprime los axiomas de los que depende cada función traducida, sin teorema de por medio. |
| `teoremas/ProofObligations.lean` | 11770 | nuestro — los teoremas. |
| `axiomas.txt` | 1668 | nuestro — la salida de `#print axioms`, para poder leer la base de confianza sin compilar. En los dos sentidos: cada teorema con los axiomas que utiliza, y cada axioma con los teoremas donde aparece. |
| `axiomas.py` | 204 | nuestro — arma `axiomas.txt` a partir del log del build. |
| `r2.log`, `r3.log`, `r4.log`, `resultado.log` | 16 KB | nuestros — salida cruda de los primeros intentos de extracción, guardada para el registro. Las reglas que salieron de ahí están escritas en el `README.md`. |
| `README.md` | 1745 | nuestro — la bitácora: cada obstáculo en el orden en que lo encontramos. |
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

Fuera de la STF hay una función más de ustedes: `State::from_genesis`, de
`crates/common/types/src/state.rs`, copiada sin cambios. Es el estado del que
la transición parte, y hace falta para enunciar los resultados "desde el
génesis". Se tradujo sin tocar nada.

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
(`process_attestations_rejects_justification_votes_length_mismatch`,
`process_attestations_rejects_empty_validator_registry`) cubren las salidas de **antes** del loop;
ninguno cubre las tres de adentro. Así que agregamos dos que sí:

| Test | Qué fuerza |
|---|---|
| `process_attestations_rejects_empty_aggregation_bits` | el voto válido de su test de regresión, sin ningún bit prendido → `EmptyAggregationBits` |
| `process_attestations_rejects_an_out_of_range_bit` | bits de largo 6 con el índice 5 prendido sobre 4 validadores → `AggregationBitsOutOfBounds { index: 5, validator_count: 4 }` |

Los dos se chequearon contra el defecto: sacando el arreglo, sus seis pasan y
estos dos fallan.

El tercer test nuestro es de otra clase: no cubre nuestra reescritura sino un
comportamiento del código de ustedes. Está en **El reemplazo de checkpoint**,
más abajo.

**La cuarta función reescrita no tenía test, y ahora tiene uno.** Sus seis
tests llaman a `process_attestations` o a `attestation_data_matches_chain`.
Eso cubre tres de las cuatro funciones reescritas, porque `try_finalize` y
`serialize_justifications` sólo se llaman desde `process_attestations`. La
cuarta es `process_block_header`, donde un loop con `push` reemplaza a
`extend(repeat_n(...))`, y ninguno la llama. Agregamos
`process_block_header_fills_empty_slots_with_zero_hashes`: un bloque dos slots
después del último header, y otro sin slots vacíos en el medio. El historial
tiene que quedar como estaba, más la raíz del padre, más un cero por cada slot
vacío.

Lo chequeamos contra el defecto de dos maneras: con el loop dando una vuelta de
menos, y con el loop agregando otra raíz en lugar del cero. En los dos casos
falla ese test y los otros once pasan.

Dos límites. El valor esperado sale de leer qué hace su `extend(repeat_n(...))`,
no de correrlo: el original no se puede ejecutar dentro de este crate. Y sigue
sin haber un test que llame a `state_transition`, a `process_block` o a
`process_slots`; esas tres están sin cambios salvo comentarios.

Sobre ese loop hay además dos teoremas: que sólo agrega al final del historial
y que deja exactamente el largo esperado. Que lo agregado son ceros no está
demostrado; es lo que mira el test.

**Una diferencia con su código que encontramos revisando, y que no
arreglamos.** Ustedes arman el mapa de votos con `.collect()` sobre los pares
(raíz, votos) del estado. Si `justifications_roots` trae una raíz repetida, un
`HashMap` armado así se queda con los votos de la **última** aparición.
`construir_mapa_de_votos`, la nuestra, usa `poner_si_falta` y se queda con los
de la **primera**. Con raíces sin repetir las dos hacen lo mismo, y en todo
estado alcanzable desde el génesis no se repiten: es `RZ.alcanzable_raices`,
demostrado sobre nuestro código. Pero ustedes tratan como entrada posible un
estado con invariantes rotas, y sobre un estado así nuestra reescritura y su
original divergen. Ningún test lo ejercita. Lo leímos de las dos fuentes; no lo
corrimos.

## Qué recibe

`teoremas/ProofObligations.lean` tiene ciento dos resultados con nombre:

| Resultado | Qué es |
|---|---|
| `pronic_iff_cuadrado` | la identidad que afirma su propio comentario |
| `chequeo_de_paridad_redundante` | su corolario: el chequeo de paridad de al lado nunca puede fallar |
| `try_finalize_no_retrocede` | la finalidad no retrocede |
| `try_finalize_no_toca_justified` | `try_finalize` no toca `latest_justified` |
| `ST3.process_attestations_loop_no_retrocede` | la justificación no retrocede, sobre el loop de attestations entero |
| `ST3.process_attestations_no_retrocede` | lo mismo, sobre la función entera |
| `ST3F.process_attestations_fin_no_retrocede` | la finalidad tampoco retrocede, sobre `process_attestations` entera |
| `ST3.process_slots_no_toca_checkpoints` | `process_slots` no toca ninguno de los dos checkpoints |
| `ST3H.process_block_header_no_mueve_slots` | `process_block_header` conserva los dos slots de checkpoint, anclaje de génesis incluido |
| `ST3T.process_block_no_retrocede` | ningún slot retrocede a lo largo de `process_block` |
| `ST3.state_transition_no_retrocede` | **ningún slot retrocede a lo largo de `state_transition`** — la transición de un bloque entera |
| `ST7.h256_eq_true` | la igualdad traducida de `H256` es la igualdad |
| `ST7.process_attestations_adelante` | ningún checkpoint cambia de raíz sin subir de slot, sobre `process_attestations` entera |
| `ST7.process_block_header_no_toca_checkpoints` | fuera del anclaje del génesis, `process_block_header` deja los dos checkpoints enteros y sólo agrega al final del historial |
| `ST7.state_transition_adelante` | **ningún checkpoint cambia de raíz sin subir de slot a lo largo de `state_transition`**, si el justificado está en el historial |
| `ST1.process_slots_avanza` | si `process_slots` acepta, el estado queda en el slot pedido |
| `ST1.process_slots_rechaza` | si el slot pedido no está en el futuro, rechaza sin tocar el estado |
| `ST2.process_block_header_slot` | si `process_block_header` acepta, el último header queda en el slot del bloque |
| `ST2.state_transition_conserva_no_genesis` | si el último header no era el del génesis, sigue sin serlo después de `state_transition` |
| `ST4.state_transition_justificado_ge_finalizado` | **si el slot finalizado no supera al justificado antes de `state_transition`, tampoco después** |
| `ST6.finalizacion_irreversible` | la finalización no retrocede a lo largo de `state_transition` — la mitad de `ST-3`, con nombre propio |
| `JS.set_luego_is_justified` | después de `set_justified(s)`, `is_slot_justified(s)` devuelve `Ok(true)` |
| `JS.extend_to_slot_no_pierde_bits` | `extend_to_slot` no cambia ningún bit de valor ni de lugar |
| `JS.extend_to_slot_conserva_respuestas` | lo que `is_slot_justified` respondía antes de extender, lo responde después |
| `JS.shift_window_corre` | tras `shift_window`, el bit en `i` es el que estaba en `i + delta` |
| `JS.finalizar_conserva_justificados` | **al avanzar la finalidad y correr la ventana, todo slot por encima del límite nuevo se reporta igual** |
| `NP.is_slot_justified_total` | `is_slot_justified` nunca entra en pánico |
| `NP.set_justified_total` | si `is_slot_justified` responde `Ok`, `set_justified` devuelve |
| `NP.set_justified_panico` | si responde `Err`, `set_justified` entra en pánico |
| `NP.set_justified_tras_voto_valido` | después de un voto válido, `set_justified` sobre su target devuelve |
| `NP.extend_to_slot_devuelve` | `extend_to_slot` devuelve, si el slot pedido no está a más de 262144 del finalizado |
| `NP.shift_window_devuelve` | `shift_window` devuelve, si la lista no pasa de 262144 bits |
| `NP.finalizar_conserva_justificados_total` | **el compuesto, sin condicional de pánico** |
| `VC.tras_header_cubre` | después de `process_block_header`, `is_slot_justified` responde `Ok` sobre todo slot anterior al del bloque |
| `VC.tras_header_rechaza` | y responde `Err` del slot del bloque en adelante, si la ventana de entrada no era más larga de lo debido |
| `VI.state_transition_conserva_ventana` | la transición conserva que la ventana no pasa del último slot materializado |
| `VI.state_transition_ventana_justa` | **tras un bloque aceptado, la ventana termina exactamente en el slot anterior al del bloque** |
| `VI.tras_header_rechaza_inv` | el "exactly" del comentario de `is_valid_vote`, con ese invariante en lugar de la hipótesis suelta |
| `HC.header_acepta_slot_acotado` | **`process_block_header` no acepta ningún bloque con slot mayor que 262144** |
| `HC.state_transition_conserva_acotado` | la transición conserva los dos invariantes: dónde termina la ventana, y un hash por slot con el slot acotado |
| `HC.shift_window_no_falla` | con esos invariantes, `shift_window` sobre la ventana del estado devuelve |
| `NP2.current_proposer_eq` | `current_proposer` devuelve siempre: `None` sin validadores, `Some(slot % n)` con validadores |
| `NP2.is_proposer_total` | `is_proposer` nunca entra en pánico |
| `NP2.slot_is_justifiable_total` | `slot_is_justifiable_after` nunca entra en pánico |
| `NP2.matches_chain_total` | `attestation_data_matches_chain` nunca entra en pánico |
| `NP2.is_valid_vote_total` | **`is_valid_vote` nunca entra en pánico, para cualquier estado y cualquier voto** |
| `NP3.process_slots_devuelve` | `process_slots` no entra en pánico, si el hash del estado devuelve |
| `NP3.process_block_header_devuelve` | **`process_block_header` no entra en pánico**, con un hash por slot en el historial y si sus dos hashes devuelven |
| `NP4.h256_cmp_devuelve` | la comparación de dos `H256` devuelve siempre |
| `NP4.claves_ordenadas_devuelve` | el ordenamiento de raíces escrito a mano termina y no cambia cuántas hay |
| `NP4.serialize_justifications_devuelve` | **`serialize_justifications` no entra en pánico**, con el mapa de votos dentro de los límites |
| `MV.construir_mapa_acotado` | el mapa de votos que se arma desde el estado no tiene listas más largas que `validator_count` |
| `MV.loop_conserva_acotado` | el loop de attestations conserva esa cota |
| `MV.serialize_tras_attestations_devuelve` | con el mapa que deja `process_attestations`, `serialize_justifications` devuelve con una hipótesis menos |
| `NP5.filtrado_devuelve` | `filtrado`, el reemplazo del `retain`, no entra en pánico |
| `NP5.try_finalize_devuelve` | **`try_finalize` no entra en pánico**, con el source anterior al target y la ventana en capacidad |
| `NP5.try_finalize_devuelve_inv` | lo mismo, con la capacidad de la ventana sacada de los invariantes de la transición |
| `NP6.contar_datos_devuelve` | contar los datos distintos de un bloque no entra en pánico |
| `NP6.hay_raiz_cero_devuelve` | buscar la raíz cero no entra en pánico |
| `NP6.primer_bit_devuelve` | buscar el primer bit fuera de rango no entra en pánico |
| `NP6.votos_vacios_devuelve` | `votos_vacios(n)` devuelve, y devuelve `n` votos |
| `NP6.poner_si_falta_devuelve` | agregar una raíz al mapa no entra en pánico si hay lugar, y agrega a lo sumo una |
| `NP6.marcar_votos_devuelve` | marcar los votos de una agregación no entra en pánico ni cambia cuántas entradas hay |
| `NP6.cuenta_votos_devuelve` | contar los votos de una raíz no entra en pánico |
| `NP6.sin_devuelve` | sacar una raíz del mapa no entra en pánico ni deja más entradas |
| `NP6.construir_mapa_devuelve` | armar el mapa de votos desde el estado no entra en pánico, si `raíces * validator_count` no desborda |
| `NP6.hashmap_devuelve` | las tres operaciones del `HashMap` de raíces a slots devuelven siempre |
| `NP6.construir_rts_devuelve` | armar el `HashMap` de raíces a slots no entra en pánico |
| `NP7.process_attestations_devuelve` | **`process_attestations` no entra en pánico**, con los límites de sus tipos |
| `NP7.process_attestations_devuelve_inv` | lo mismo, con la ventana y la finalidad sacadas de los invariantes de la transición |
| `NP8.process_block_devuelve` | `process_block` no entra en pánico, con las hipótesis juntas |
| `NP8.state_transition_devuelve` | **la transición de estado entera no entra en pánico**, bajo hipótesis escritas |
| `RV.state_transition_no_toca_validadores` | la transición no cambia los validadores, acepte el bloque o lo rechace |
| `RV.state_transition_conserva_hipotesis` | las tres hipótesis sobre el estado se conservan de un bloque al siguiente |
| `GEN.genesis_devuelve` | `from_genesis` devuelve si hay a lo sumo 4096 validadores, y devuelve el estado inicial |
| `GEN.genesis_exige_validadores` | al revés: si `from_genesis` devuelve, había a lo sumo 4096 validadores |
| `GEN.genesis_cumple_hipotesis` | el estado inicial cumple los dos invariantes, la cota de validadores y el caso base de `ST-4` |
| `GEN.alcanzable_cumple` | en todo estado alcanzable desde el génesis valen los dos invariantes, la cota de validadores y `ST-4` |
| `GEN.st4_alcanzable` | `ST-4`, completa: paso inductivo y caso base |
| `GEN.state_transition_devuelve_alcanzable` | **la transición no entra en pánico en ningún estado alcanzable desde el génesis** |
| `G7.aceptar_saca_del_genesis` | si `process_block_header` acepta, el último header deja de ser el del génesis |
| `G7.state_transition_conserva_inv7` | la transición conserva el invariante de `ST-7`: o no se aceptó ningún bloque todavía, o el justificado está en el historial |
| `G7.alcanzable_inv7` | ese invariante vale en todo estado alcanzable desde el génesis |
| `G7.justificado_en_el_historial` | la hipótesis que le faltaba a `ST-7`, establecida: pasado el anclaje, el justificado está en el historial |
| `G7.st7_alcanzable` | **`ST-7` sobre todo estado alcanzable desde el génesis**, con la hipótesis del catálogo y ninguna más sobre el estado |
| `ORD.comparacion_es_lexicografica` | el `<` traducido entre dos `H256` es el orden lexicográfico de sus bytes |
| `ORD.claves_ordenadas_ordena` | **el ordenamiento de raíces escrito a mano ordena**: devuelve las mismas raíces, en orden |
| `ORD.claves_ordenadas_canonica` | dos mapas con las mismas raíces, en cualquier orden, dan la misma lista ordenada |
| `ORD.serialize_escribe_ordenado` | lo que `serialize_justifications` deja en `justifications_roots` está ordenado y son las raíces del mapa |
| `ORD.serialize_raices_canonicas` | `justifications_roots` no depende del orden en que el mapa tenía las raíces |
| `RZ.h256_eq_iff` | la igualdad traducida de `H256` es la igualdad, en los dos sentidos |
| `RZ.poner_si_falta_no_repite` | `poner_si_falta` no repite claves |
| `RZ.state_transition_conserva_raices` | la transición conserva el invariante de las raíces pendientes: no se repiten y están en el historial |
| `RZ.alcanzable_raices` | ese invariante vale en todo estado alcanzable desde el génesis |
| `RZ.raices_pendientes_acotadas` | en todo estado alcanzable hay a lo sumo 262144 raíces pendientes |
| `RZ.process_attestations_devuelve_con_invariante` | `process_attestations` no entra en pánico, con ese invariante en lugar de la cota por bloque |
| `RZ.state_transition_devuelve_con_invariante` | lo mismo para la transición entera |
| `RZ.state_transition_devuelve_desde_genesis` | **la transición no entra en pánico en ningún estado alcanzable, y del bloque sólo se pide el límite de su tipo** |
| `CAN.volcar_votos_mismas` | volcar los votos de una raíz da lo mismo desde dos mapas con las mismas entradas |
| `CAN.serialize_no_depende_del_orden` | **`serialize_justifications` no depende del orden de las entradas del mapa**: es la misma cuenta |
| `CAN.serialize_canonica` | dos mapas con las mismas entradas, en cualquier orden, dejan el mismo estado |
| `bind_da_ok` | una herramienta: abre un bind de `RustM` |

No se eligieron por cantidad. Entre todos cubren aritmética, ramificación y
actualización de registros, inducción sobre un loop, composición a lo largo de
una función entera con salidas tempranas y un `match`, composición de cinco
funciones hasta el punto de entrada, una propiedad que depende del contenido
de una lista y no sólo de guardas y asignaciones, enunciados exactos sobre dos
loops de copia, corrección total —que la función devuelve, con terminación
incluida— para la transición entera, invariantes llevados desde el génesis, y
que un ordenamiento escrito a mano ordena.

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
devuelva `ok`** — y ese `ok` es el de la cadena de herramientas, no el de Rust.
Aeneas envuelve cada función traducida en `RustM`, que tiene tres resultados:
`ok`, `fail` (un pánico — un desborde aritmético, un índice fuera de rango) y
`div` (no terminación). `process_attestations` se traduce a
`RustM (Result<(), Error> × State)`, así que un bloque que el código de ustedes
rechaza es `ok (Err e, state')` y **está cubierto**: el slot justificado tampoco
retrocede por ese camino.

Lo que los enunciados dejan afuera son las corridas que entran en pánico o que
no terminan. Ése es un límite real y no una cuestión de forma: un pánico en la
STF no rechaza un bloque, tira el nodo. La ausencia de pánico es un teorema
aparte y mucho más grande. Está más abajo: para la ventana de slots
justificados en **La ventana no entra en pánico**, y para las doce funciones de
la transición en las secciones que siguen a ésa, hasta **La transición entera
no entra en pánico**.

Ésta es la propiedad que su propio test afirma por ejemplo, en
`latest_justified_does_not_regress_within_block`. Su comentario dice por qué
existe: en el devnet, en el slot 27984, un bloque llevó tres attestations con
supermayoría apuntando a los slots 27978, 27981 y 27974 en ese orden, la
asignación sin guarda se quedó con la última, y la cadena de bloques se congeló.
El test cubre ese escenario; el teorema cubre toda entrada con la que la
función devuelve algo, acepte el bloque o lo rechace.

### La transición entera

Las dos mitades de arriba hablan cada una del componente donde se mueve un
campo. Tres lemas más las suben a la función que ustedes llaman por bloque:

- `process_slots` no toca ninguno de los dos checkpoints;
- `process_block_header` conserva los dos **slots** de checkpoint;
- la finalidad, demostrada arriba para `try_finalize` suelta, llevada a través
  del loop de attestations y del resto de `process_attestations`.

Compuestos a través de `process_block`, dan:

```lean
theorem ST3.state_transition_no_retrocede
    (state state' : tipos.State) (block : tipos.Block) (res : ...) :
    stf.state_transition state block = ok (res, state') →
    state.latest_justified.slot ≤ state'.latest_justified.slot ∧
    state.latest_finalized.slot ≤ state'.latest_finalized.slot
```

Vale el mismo condicional: el `ok` es el de `RustM`, así que los bloques
rechazados están cubiertos y los pánicos no.

El lema del header es el que traía una trampa. En el primer bloque después del
génesis el código de ustedes ancla los checkpoints:

```rust
state.latest_justified.root = parent_root;
state.latest_finalized.root = parent_root;
```

Escribe la **raíz** y deja el slot como está, así que el enunciado sobre los
slots vale para cualquier estado, sin hipótesis de estado bien formado. Lo que
no vale es la igualdad del checkpoint entero, y Lean lo dice: como control
enunciamos esa versión falsa y le corrimos el mismo script de demostración, y se
detiene con exactamente la rama del anclaje abierta —
`{ root := r, slot := state.latest_justified.slot } = state.latest_justified`.

### El reemplazo de checkpoint, y dónde su código se aparta de la especificación

`ST-3` acota sólo los slots. Deja pasar una transición que le cambie la **raíz**
a un checkpoint sin moverlo de slot. El catálogo lo cierra con `ST-7`: a lo
largo de una transición, cada checkpoint queda igual entero —raíz incluida— o
pasa a un slot estrictamente mayor.

En el modelo del catálogo eso vale para cualquier estado posterior al génesis,
porque la especificación compara con `>` estricto:

```python
# leanSpec, state_transition.py
if target.slot > latest_justified.slot:
    latest_justified = target
```

El código de ustedes no:

```rust
state.latest_justified =
    std::cmp::max_by_key(state.latest_justified, target, |c| c.slot);
```

`max_by_key` devuelve el **segundo** argumento cuando las claves empatan. Ante
un target en el mismo slot que el justificado, la especificación se queda con
el que estaba y ustedes se quedan con el target. Nuestra reescritura conserva
ese comportamiento: `if target.slot >= state.latest_justified.slot`.

**Tal como está enunciada, `ST-7` es falsa sobre su código.** El test
`same_slot_root_swap_needs_a_justified_root_off_the_chain` lo muestra. Parte de
un estado con `latest_justified = (4, X)` donde `historical_block_hashes[4]` es
otra raíz y el slot 4 no figura en `justified_slots`; una supermayoría vota al
target `(4, historical_block_hashes[4])`; después de `process_attestations` el
justificado sigue en el slot 4 y tiene otra raíz. Sobre ese mismo estado la
especificación no lo reemplaza: `4 > 4` es falso. Eso último lo leímos del
código de leanSpec, no lo corrimos; el catálogo lo tiene demostrado sobre su
modelo.

Ese estado no se alcanza aplicando bloques desde el génesis: está demostrado
más abajo, en **`ST-7` desde el génesis**. Pero ustedes ya
tratan como entrada posible un estado con invariantes rotas entre campos: el
comentario de `process_attestations_rejects_justification_votes_length_mismatch`
dice que un ancla de checkpoint-sync mal formada puede traer una, porque la
decodificación SSZ no las chequea.

Lo que sí vale, y está demostrado:

```lean
theorem ST7.state_transition_adelante
    (state state' : tipos.State) (block : tipos.Block) (res : ...)
    (hnz : state.latest_block_header.slot ≠ 0#u64)
    (hhist : ST7.EnElHistorial state.historical_block_hashes
               state.latest_justified) :
    stf.state_transition state block = ok (res, state') →
    (state'.latest_justified = state.latest_justified ∨
       state.latest_justified.slot < state'.latest_justified.slot) ∧
    (state'.latest_finalized = state.latest_finalized ∨
       state.latest_finalized.slot < state'.latest_finalized.slot) ∧
    ST7.EnElHistorial state'.historical_block_hashes state'.latest_justified
```

`hnz` es la hipótesis del catálogo: deja afuera el anclaje del génesis, el único
lugar donde la raíz cambia a propósito. `hhist` es la nuestra:
`EnElHistorial hist c` dice que `hist[c.slot] = c.root`, o sea que el checkpoint
justificado es el bloque que el historial tiene en ese slot. La tercera parte
de la conclusión dice que `hhist` se conserva.

La razón por la que vale no es la de la especificación. `is_valid_vote` sólo
deja pasar un voto si `attestation_data_matches_chain` lo acepta, y eso exige
`historical_block_hashes[target.slot] == target.root`. Un target que empata en
slot con el justificado tiene entonces la misma raíz que el justificado, y es
el mismo checkpoint: la asignación ocurre y no cambia nada. La especificación
está a salvo por la comparación; el código de ustedes, por el chequeo contra el
historial. Con el `>` de la especificación, `hhist` no haría falta.

La mitad de la finalidad no necesita `hhist`: `try_finalize` asigna sólo si
`source.slot > latest_finalized.slot`.

Como control negativo corrimos el mismo script del loop sin `hhist`. Queda un
único objetivo abierto, y es la rama `target.slot ≥ latest_justified.slot`.

Tres cosas que hicieron falta y que sirven fuera de este teorema:

- **La igualdad traducida de `H256` es la igualdad.** `==` sobre `[u8; 32]` se
  traduce a un loop de `CoreModels` que compara byte a byte.
  `ST7.h256_eq_true` demuestra que si devuelve `true` los dos valores son
  iguales. Sin eso no se pasa de "el código comparó y dio igual" a una igualdad
  en Lean.
- **`mem::take` dejó de ser un axioma.** `process_block_header` saca
  `historical_block_hashes` del estado con `std::mem::take`, le agrega la raíz
  del padre y lo vuelve a guardar. Con `take` como firma sin contenido era
  imposible demostrar que el historial viejo sigue ahí. Ahora es una definición
  —devuelve lo que había y deja el `Default`— y es una de las cinco
  afirmaciones de modelado que hacemos, junto a `isqrt`, `bool::then`, la
  comparación de arrays y el `HashMap`.
- **`process_block_header` sólo agrega al final del historial**, y fuera del
  anclaje deja los dos checkpoints enteros
  (`ST7.process_block_header_no_toca_checkpoints`).

Lo que este teorema solo no dice: que `hhist` empiece a valer alguna vez. En el
estado inicial es falsa. Que el primer bloque aceptado la establece, y que por
eso vale en todo estado alcanzable desde el génesis, está demostrado más abajo,
en **`ST-7` desde el génesis**. La otra hipótesis también se conserva: que
`hnz` pasa de un bloque al siguiente está demostrado con `ST-2`.

### Las otras cuatro de transición de estado

El catálogo tiene siete proposiciones sobre la transición de estado. Con las dos
de arriba, éstas completan la lista.

**`ST-1`, el avance de slots.** El catálogo la enuncia con `slot ≤ target`,
porque su modelo de `process_slots` devuelve un estado y no rechaza. La
especificación en Python y el código de ustedes rechazan los dos cuando
`slot >= target`, así que acá son dos enunciados: si acepta, el estado queda en
el slot pedido (`ST1.process_slots_avanza`); y si el slot pedido no está en el
futuro, devuelve `StateSlotIsNewer` y el estado sin tocar
(`ST1.process_slots_rechaza`). El segundo no es condicional: dice qué devuelve.

**`ST-2`, el header.** Si `process_block_header` acepta, el último header queda
en el slot del bloque. Del mismo lema sale lo que le faltaba a `ST-7`: si el
último header no era el del génesis, sigue sin serlo, acepte o rechace. Eso
está subido a la transición entera (`ST2.state_transition_conserva_no_genesis`),
para lo que hubo que demostrar que el resto de `state_transition` no toca
`latest_block_header`.

**`ST-4`, justificado ≥ finalizado.**

```lean
theorem ST4.state_transition_justificado_ge_finalizado
    (state state' : tipos.State) (block : tipos.Block) (res : ...)
    (hinv : state.latest_finalized.slot ≤ state.latest_justified.slot) :
    stf.state_transition state block = ok (res, state') →
    state'.latest_finalized.slot ≤ state'.latest_justified.slot
```

En el catálogo es un invariante de los estados alcanzables. Esto es su paso
inductivo, y vale para cualquier estado: si se cumple antes de la transición,
se cumple después. La razón está a la vista en el código de ustedes.
`try_finalize` sólo corre justo después de justificar un target; lo que
finaliza es el `source` de ese voto; y `is_valid_vote` exige
`target.slot > source.slot`. El finalizado nuevo queda entonces por debajo del
target, que a su vez no supera al justificado nuevo. No hizo falta razonar
sobre la lista de bits `justified_slots`.

Como control negativo corrimos el mismo script con un lema de `is_valid_vote`
que no dice nada. Quedan abiertos exactamente los dos casos en que la finalidad
pasa al `source`, pidiendo `source.slot ≤` el justificado nuevo.

El caso base está más abajo, en **El génesis y los estados alcanzables**:
`GEN.st4_alcanzable` es `ST-4` completa, sobre todo estado al que se llega
desde el génesis.

**`ST-6`, la finalización es irreversible.** El catálogo mismo dice que es la
mitad `latest_finalized` de `ST-3`. `ST6.finalizacion_irreversible` le pone
nombre.

**`ST-5`, la pureza, no está enunciada.** En el catálogo es
`transition s b = transition s b`, demostrada con `rfl`. Vale igual para
cualquier función de Lean, la de ustedes traducida incluida, y agregarla no
diría nada sobre el código.

### La ventana de slots justificados

`justified_slots_ops` es la lista de bits que guarda qué slots están
justificados, con índices relativos al slot finalizado. Los resultados de arriba
la esquivaron: salen de guardas, de asignaciones y del historial. Éstos entran.

No vienen del catálogo. Son los cuatro que nos propusimos el 22 de octubre, al
mirar su código por primera vez y antes de traducir nada:

| | Enunciado |
|---|---|
| ida y vuelta | después de `set_justified(s)`, `is_slot_justified(s)` devuelve `Ok(true)` |
| `extend_to_slot` | la lista nueva es la vieja más ceros al final: ningún bit cambia de valor ni de lugar |
| `shift_window` | la lista nueva es la vieja sin sus primeros `delta` bits |
| el compuesto | cuando la finalidad avanza de `f` a `f'` y la ventana se corre `f' − f`, todo slot por encima de `f'` se reporta igual que antes |

El último es el que justificaba el ejercicio:

```lean
theorem JS.finalizar_conserva_justificados
    (slots slots' : ssz.SszBitlist ...) (f f' s : U64) (delta : Usize) (b : Bool)
    (hff : f.val ≤ f'.val) (hfs : f'.val < s.val)
    (hdelta : delta.val = f'.val - f.val)
    (hfit : s.val - f.val - 1 < 2 ^ UScalarTy.Usize.numBits) :
    is_slot_justified slots f s = ok (Ok b) →
    shift_window slots delta = ok slots' →
    is_slot_justified slots' f' s = ok (Ok b)
```

Involucra tres funciones y dos sistemas de índices. El slot `s` está en la
posición `s − f − 1` antes y en `s − f' − 1` después, y `shift_window` tiene que
haber movido exactamente ese bit. No es algo que se verifique leyendo.

Cuatro cosas son distintas de todo lo anterior.

**Los enunciados son exactos.** No dicen "no retrocede" sino qué lista queda:
`slots ++ ceros` para `extend_to_slot`, `slots.drop delta` para `shift_window`.

**Dos de las conclusiones no son condicionales.** La ida y vuelta y el compuesto
concluyen que `is_slot_justified` *devuelve* `Ok`. Para eso hubo que demostrar,
como ecuaciones, qué devuelven `get`, `set`, `len` y `relative_index` —por
ejemplo `get s i = ok (s.bits[i]?)`— bajando por los modelos de `core` hasta el
fondo: índices de slice, `vec![false; n]`, la resta con desborde. La primera
llamada de cada enunciado (`set_justified`, `shift_window`) sigue siendo
condicional, como en el resto.

**Los loops de copia tienen su invariante en Lean puro.** `Copiado` y
`Desplazado` son predicados sobre listas, y sus lemas de paso no mencionan nada
de Rust. El loop traducido deja tres objetivos —bit en uno, bit en cero, fin del
rango— y cada uno es un lema de paso.

**El compuesto pide que la distancia entre en un `usize`.** `relative_index`
hace `idx as usize`, y el modelo de la cadena de herramientas no fija el ancho
de `usize`. En 64 bits `hfit` vale siempre. En 32 bits ese cast trunca, y dos
slots a distancia 2³² compartirían bit. No es un bug vivo, pero es una
precondición que el código no enuncia.

Los tres `.expect()` y el `.unwrap()` de este módulo (`"index out of bounds"`,
`"capacity limit exceeded"`, `"index within capacity"`) son el tema de la
sección que sigue.

### La ventana no entra en pánico

Todo lo de arriba dice "si la función devuelve, entonces…". Esto es lo otro: que
**devuelve**. Está hecho para las cuatro funciones de `justified_slots_ops`, que
tienen tres `.expect()`, un `.unwrap()` y dos sumas que podrían desbordar.

| Función | Cuándo devuelve |
|---|---|
| `is_slot_justified` | siempre |
| `set_justified` | exactamente cuando `is_slot_justified` responde `Ok` sobre ese slot |
| `extend_to_slot` | si el slot pedido está a lo sumo 262144 por encima del finalizado |
| `shift_window` | si la lista no pasa de 262144 bits |

El de `set_justified` son dos lemas, y juntos dicen cuándo se dispara su
`expect("index out of bounds")`:

```lean
theorem NP.set_justified_total ... :
    is_slot_justified slots f t = ok (Ok b) →
    ∃ slots', set_justified slots f t = ok slots'

theorem NP.set_justified_panico ... :
    is_slot_justified slots f t = ok (Err e) →
    set_justified slots f t = fail Error.panic
```

El segundo no es una hipótesis de trabajo: demuestra que el pánico ocurre. Si el
slot está fuera de la ventana, `set_justified` aborta.

**En el punto de uso ese pánico no se puede disparar.** El loop de
`process_attestations` llama a `set_justified` sobre el target de un voto recién
después de que `is_valid_vote` lo aceptó, y con el mismo estado entre las dos
llamadas. `NP.set_justified_tras_voto_valido` demuestra que eso alcanza:
`is_valid_vote` sólo devuelve `Ok(true)` si `is_slot_justified` respondió
`Ok(false)` sobre el target, o sea que el target está dentro de la ventana.

**El compuesto queda sin condicional.** Con `shift_window` devolviendo,
`NP.finalizar_conserva_justificados_total` dice que al avanzar la finalidad la
ventana se corre *y* todo slot por encima del límite nuevo se reporta igual.

Cómo cambia la técnica. Las ternas de antes usan `PostCond.mayThrow`, que tolera
el pánico y la divergencia. Éstas usan `⇓`, que no tolera ninguna de las dos, y
entonces cada punto donde el código podría abortar aparece como un objetivo a
demostrar: que el índice está en rango, que la suma no desborda, que lo pedido
entra en la capacidad. Al loop hay que darle una medida de terminación de verdad
(`end − start`) en vez de la constante que alcanzaba antes. El resto es lo
mismo: los mismos invariantes sobre listas y los mismos lemas de paso.

Como control negativo corrimos la demostración de `shift_window` sin la
hipótesis de capacidad. Se detiene en un objetivo, el del `expect` de
`with_length`: no puede mostrar que lo que queda entra en 262144.

**Lo que no está acá.** Que las hipótesis de capacidad valgan en todo estado
alcanzable: que la ventana nunca pase de 262144 bits y que ningún slot quede más
lejos que eso del finalizado. Son invariantes del estado entero, no de este
módulo, y están en **Dónde termina la ventana** y **La ventana no pasa de su
capacidad**. Las otras funciones de la STF tienen su sección más abajo.

### Un comentario de ustedes sobre la ventana, verificado

El comentario de `is_valid_vote` dice:

```rust
/// After `process_block_header` the window covers up to
/// `block.slot - 1`, so this is exactly a vote whose source or target slot is
/// at or beyond the importing block's own slot.
```

Es una afirmación sobre lo que hacen juntas `process_block_header`,
`extend_to_slot` e `is_slot_justified`. Ahora son dos teoremas, uno por cada
mitad de la frase.

**"Covers up to `block.slot − 1`".** Si `process_block_header` acepta, sobre todo
slot anterior al del bloque `is_slot_justified` responde `Ok`
(`VC.tras_header_cubre`). Vale para cualquier estado de entrada.

**"Exactly".** Del slot del bloque en adelante responde `Err`, que es el
`JustifiedSlotOutOfRange` (`VC.tras_header_rechaza`). Esta mitad **no vale para
cualquier estado**: pide que la ventana de entrada no llegara ya más allá del
slot anterior al bloque.

```lean
(hlen : state.justified_slots.bits.val.length +
          state.latest_finalized.slot.val + 1 ≤ block.slot.val)
```

Con una ventana más larga de lo debido, un voto con slot posterior al bloque no
se rechazaría por fuera de rango. O sea que el "exactly" del comentario es
cierto bajo un invariante que el comentario no menciona: que la ventana termina
justo en el último slot materializado. Que ese invariante se conserva a lo
largo de la transición está demostrado en la sección que sigue.

Como control negativo corrimos la segunda demostración sin `hlen`. Falla en los
dos lugares donde se la usa, y en ninguno más.

Lo que hizo falta fue el largo exacto que deja `extend_to_slot` —el máximo
entre el que tenía y el pedido—, que no estaba entre los resultados de la
ventana, y qué ventana deja `process_block_header`: la de entrada pasada por
`extend_to_slot` hasta `block.slot − 1`, con el mismo slot finalizado.

Que `hlen` se conserva de un bloque al siguiente es el tema de la sección que
sigue.

### Dónde termina la ventana

La sección anterior dejó una hipótesis suelta: que la ventana de entrada no
llegara más allá del slot anterior al bloque. Acá está como invariante de la
transición entera.

Son dos predicados sobre el estado:

- `VentanaNoPasa`: el largo de la ventana más el slot finalizado no supera el
  slot del último header. Vale en el génesis, donde la ventana está vacía y el
  finalizado es cero.
- `VentanaJusta`: largo + finalizado + 1 es exactamente el slot del último
  header. O sea que la ventana cubre del finalizado + 1 al slot del header − 1,
  ni un bit más ni uno menos.

```lean
theorem VI.state_transition_conserva_ventana ...
    (h64 : UScalarTy.Usize.numBits = 64) :
    VentanaNoPasa state →
    stf.state_transition state block = ok (res, state') →
    VentanaNoPasa state'

theorem VI.state_transition_ventana_justa ...
    (h64 : UScalarTy.Usize.numBits = 64) :
    VentanaNoPasa state →
    stf.state_transition state block = ok (Ok (), state') →
    VentanaJusta state'
```

El primero vale acepte o rechace el bloque. El segundo dice que después de un
bloque aceptado la ventana queda justa. Como `VentanaJusta` implica
`VentanaNoPasa`, el invariante se sostiene de un bloque al siguiente, y con él
el "exactly" del comentario de `is_valid_vote` queda sin hipótesis suelta
(`VI.tras_header_rechaza_inv`).

Por qué vale. `process_block_header` extiende la ventana hasta `block.slot − 1`,
y con eso la deja justa. Después, en el loop de attestations, `set_justified` no
cambia el largo, y `try_finalize` mueve las dos cosas a la vez: la finalidad
avanza `source.slot − finalizado`, y `shift_window` acorta la ventana esa misma
cantidad. La suma no cambia. Para que la cuenta cierre hace falta que el source
esté dentro de la ventana, y eso lo garantiza `is_valid_vote`, que sólo acepta
el voto si `is_slot_justified` respondió `Ok(true)` sobre el source.

Como control negativo corrimos el loop sin ese dato sobre el source. Los casos
en que no se finaliza cierran igual; quedan abiertos exactamente los dos en que
sí.

**Todo este resultado supone `usize` de 64 bits.** Es el mismo `as usize` de las
secciones anteriores, que acá aparece tres veces: el índice del source, el
`delta` que recibe `shift_window` y el índice del último slot en el header. En
32 bits esos casts truncan y la cuenta no cierra. No analizamos qué pasa en ese
caso más allá de eso.

Que la ventana no pasa de 262144 bits es el tema de la sección que sigue.

### La ventana no pasa de su capacidad

La sección anterior deja la ventana acotada por el slot del último header. Falta
acotar ese slot, y sale de un segundo invariante, sobre el historial de hashes:

- `HistorialAcotado`: `historical_block_hashes` tiene exactamente un hash por
  slot —su largo es el slot del último header— y ese slot no pasa de 262144, que
  es `HISTORICAL_ROOTS_LIMIT`.

Vale en el génesis y se conserva por `state_transition`, acepte el bloque o lo
rechace. `process_block_header` le agrega al historial la raíz del padre y un
cero por cada slot vacío entre el padre y el bloque: en total
`block.slot − parent.slot` elementos, así que si había uno por slot, sigue
habiendo uno por slot. Y antes de agregarlos chequea que el total no pase de
`HISTORICAL_ROOTS_LIMIT`. Ese total **es** el slot del bloque.

De ahí salen dos cosas.

**Ningún bloque con slot mayor que 262144 se acepta.**

```lean
theorem HC.header_acepta_slot_acotado ...
    (h64 : UScalarTy.Usize.numBits = 64)
    (hlen : state.historical_block_hashes.items.val.length =
              state.latest_block_header.slot.val) :
    stf.process_block_header state block = ok (Ok (), state') →
    block.slot.val ≤ 262144
```

Esto no es una diferencia con la especificación: el tope es el mismo en leanSpec
(`2**18`) y en su código. Es una consecuencia de ese tope, y conviene tenerla
escrita: con un hash por slot desde el génesis, la cadena de bloques no pasa
del slot 262144. El chequeo
que ustedes agregaron para evitar un pedido de memoria desmedido
(`SlotGapTooLarge`) es el que la hace cumplir.

**La ventana no pasa de 262144 bits.** Con los dos invariantes, el de esta
sección y el de la anterior, `HC.ventana_en_capacidad` da la cota, y
`HC.shift_window_no_falla` la usa: sobre la ventana de un estado así,
`shift_window` devuelve. Es la hipótesis de capacidad de **La ventana no entra
en pánico**, descargada. `HC.state_transition_conserva_acotado` dice que los dos
invariantes juntos pasan de un bloque al siguiente.

Como control negativo corrimos la cota del slot sin la hipótesis de un hash por
slot. Falla en la cuenta final.

Hizo falta el largo exacto que deja el loop que rellena los slots vacíos —antes
sólo estaba que agrega al final— y que `process_attestations` no toca el
historial, sin ninguna hipótesis.

**Dónde se usa.** En la ausencia de pánico de `try_finalize` y de
`process_block_header`, que están más abajo: son las dos funciones que llaman
a `shift_window` y a `extend_to_slot`.

### Cinco funciones de la transición no entran en pánico

**La ventana no entra en pánico** lo hizo para el módulo auxiliar. Acá empieza la
transición propiamente dicha, por las cinco funciones chicas de `stf.rs`:

| Función | Resultado |
|---|---|
| `current_proposer` | devuelve siempre: `None` sin validadores, `Some(slot % n)` con validadores |
| `is_proposer` | devuelve siempre |
| `slot_is_justifiable_after` | devuelve siempre |
| `attestation_data_matches_chain` | devuelve siempre |
| `is_valid_vote` | devuelve siempre, para cualquier estado y cualquier voto |

Ninguna lleva hipótesis: valen para toda entrada.

Dónde podía haber un pánico y por qué no lo hay:

- `current_proposer` divide por la cantidad de validadores. El `(n > 0).then(…)`
  de ustedes es lo que lo impide, y el enunciado lo dice entero: con cero
  validadores devuelve `None`, no aborta.
- `slot_is_justifiable_after` eleva al cuadrado una raíz entera, dos veces. No
  desborda porque el cuadrado de la raíz entera no supera al número original. El
  resto de sus cuentas ya usan `checked_mul` y `checked_add`.
- `attestation_data_matches_chain` lee tres posiciones del historial. Las tres
  se chequean contra el largo antes de leer.
- `is_valid_vote` junta las anteriores con dos `?`. Cuando el `?` corta, lo que
  propaga es un `Err`, y eso alcanza para que no aborte.

Como control negativo corrimos `slot_is_justifiable_after` con un lema de
`isqrt` que dice que devuelve pero no cuánto vale. Quedan abiertos exactamente
los dos cuadrados.

**`bool::then` dejó de ser un axioma.** `current_proposer` es
`(n > 0).then(|| slot % n)`, y con `then` como firma sin contenido no se podía
demostrar ni que devuelve. Ahora es una definición —llama al closure sólo si el
booleano es verdadero y envuelve el resultado en `Some`— y es la tercera
afirmación de modelado que hacemos.

**Estos cinco resultados dependen sólo de los tres axiomas de Lean.** Ni un
axioma nativo ni una declaración sin contenido: son los primeros resultados
sobre el código traducido de este paquete en que `#print axioms` no lista nada
más. Eso no quiere decir que no supongan nada. Siguen apoyándose en dos de
nuestras afirmaciones de modelado, `bool::then` e `isqrt`, que son definiciones
y por eso no aparecen como axiomas.

### `process_slots` y `process_block_header` no entran en pánico

Siguen las dos funciones de `stf.rs` que hashean.

| Función | Resultado | Hipótesis |
|---|---|---|
| `process_slots` | devuelve siempre | que el hash del estado devuelva |
| `process_block_header` | devuelve siempre | `usize` de 64 bits; un hash por slot en el historial; que el hash del header anterior y el del cuerpo del bloque devuelvan |

**El hash va como hipótesis, a propósito.** El `hash_tree_root` de este crate es
un sustituto del de ustedes. Demostrar que el sustituto termina no diría nada
sobre el suyo, así que cada enunciado lleva escrito "esta llamada al hash
devuelve", una vez por llamada. Es lo único que estos dos resultados le piden
al hash.

Dónde podía haber un pánico y por qué no lo hay:

- En `process_slots`, la resta `target_slot - state.slot`. El chequeo de arriba
  ya descartó `state.slot >= target_slot`.
- En `process_block_header`, `block.slot - parent_header.slot - 1`. El chequeo
  de `ParentSlotIsNewer` garantiza que la diferencia es al menos uno.
- `current_len + 1 + num_empty_slots`. Con un hash por slot en el historial esa
  suma vale exactamente `block.slot`, que entra en un `u64`.
- Los `push` y el loop que rellena los slots vacíos. El loop termina —ahora con
  medida de terminación— y deja exactamente `new_total` entradas.
- El `expect("pre-validated: total does not exceed limit")`. El comentario
  tiene razón: a esa altura el vector mide `new_total`, que ya pasó el chequeo
  contra `HISTORICAL_ROOTS_LIMIT`, y el `try_from` da `Ok`.
- `block.slot - 1`. El slot del bloque es mayor que el del header anterior.
- `extend_to_slot`. Recibe una ventana que entra en la capacidad, porque
  `block.slot` no pasa de 262144.

**Una precondición que el código da por sentada.** `new_total` se calcula antes
de compararlo contra el límite:

```rust
let num_empty_slots = (block.slot - parent_header.slot - 1) as usize;
let current_len = state.historical_block_hashes.len();
let new_total = current_len + 1 + num_empty_slots; // +1 for parent_root push
if new_total > HISTORICAL_ROOTS_LIMIT {
```

Si el historial tuviera más entradas que el slot del header anterior, esa suma
podría pasar de `usize::MAX` con un `block.slot` muy grande, antes de que el
chequeo llegue a rechazarlo. La hipótesis "un hash por slot" es la que lo
impide. No es una hipótesis nueva: es la primera mitad del invariante de **La
ventana no pasa de su capacidad**, que la transición conserva. No conocemos
ningún estado alcanzable que la viole, y no lo presentamos como un bug. Es la
condición bajo la cual vale el resultado, y queda escrita.

Como control negativo sacamos esa hipótesis. La prueba deja de cerrar, y lo
que queda abierto es exactamente eso: las dos sumas, en las dos ramas, y la
capacidad de la ventana en la rama que no es la del génesis.

En el modelo de Lean un desborde es un pánico. Qué hace un binario compilado
sin chequeos de desborde no lo modela este paquete.

`NP3.process_slots_devuelve` depende sólo de los tres axiomas de Lean.
`NP3.process_block_header_devuelve` depende de siete: esos tres, tres nativos,
y la firma de `fmt` del error que formatea el `expect`.

### `serialize_justifications` no entra en pánico

Es la función que vuelve a escribir el mapa de votos en los dos campos del
estado. Ordena las raíces, pide un bitlist de `raíces * validator_count` bits,
vuelca los votos de cada raíz en su tramo, y guarda las raíces.

Tiene tres `expect`, y cada uno queda atado a una hipótesis del enunciado:

| `expect` | Qué lo hace cierto |
|---|---|
| `"maximum validator justifications reached"` | a lo sumo 262144 raíces y a lo sumo 4096 validadores: son los dos límites de sus tipos, y su producto es justo la capacidad del bitlist |
| `"we just updated the capacity"` | que ninguna lista de votos sea más larga que `validator_count`: así el bit de cada voto cae adentro del tramo de su raíz |
| `"justifications_roots limit exceeded"` | a lo sumo 262144 raíces |

Con los dos límites tampoco desborda `raíces * validator_count`, ni el `base`
que avanza de a un tramo por raíz.

**La comparación de `H256` dejó de ser una hipótesis.** El ordenamiento compara
raíces con `<`, y `H256` es `[u8; 32]`. La comparación de arrays era una firma
sin contenido, así que no se podía demostrar ni que devolviera, y el enunciado
lo pedía. Ahora es una definición: el orden lexicográfico de los elementos, que
es lo que la documentación de `core` dice que hace. Con eso
`NP4.h256_cmp_devuelve` demuestra que comparar dos `H256` devuelve siempre, y
la hipótesis desapareció de este resultado y de los tres que lo usan
(`process_attestations`, `process_block` y `state_transition`). Es la cuarta
afirmación de modelado que hacemos.

**El ordenamiento escrito a mano termina.** `claves_ordenadas` reemplaza al
`sort()` de ustedes por una inserción escrita con loops explícitos.
`NP4.claves_ordenadas_devuelve` dice que termina, que no aborta y que
devuelve tantas raíces como claves tiene el mapa, sin ninguna hipótesis. Que
además las deja ordenadas está demostrado más abajo, en **El ordenamiento de
raíces ordena**; hizo falta que la comparación fuera una definición.

Controles negativos, dos. Sin la hipótesis sobre las listas de votos aparece
una meta que no cierra: que el voto entre en su tramo. Sin la cota de
validadores quedan abiertas la capacidad del bitlist y el producto.

`NP4.h256_cmp_devuelve` y `NP4.claves_ordenadas_devuelve` dependen sólo de los
tres axiomas de Lean. `NP4.serialize_justifications_devuelve` depende de siete:
esos tres, tres nativos, y la firma de `fmt` del error que formatean los
`expect`.

**Lo que no está acá.** Que el mapa que arma `process_attestations` cumpla
esas hipótesis. La de las listas de votos está en la sección que sigue; la de
las raíces, en **La cota de raíces sale de un invariante**; y la de los
validadores sale del génesis.

### El mapa de votos cumple una de esas hipótesis

De las tres hipótesis de `serialize_justifications`, una habla de las listas
de votos: que ninguna sea más larga que `validator_count`. El mapa lo arma
`process_attestations`, y acá queda demostrado que lo arma así.

| Resultado | Qué dice |
|---|---|
| `MV.construir_mapa_acotado` | el mapa que sale de `construir_mapa_de_votos` cumple la cota |
| `MV.loop_conserva_acotado` | el loop de attestations la conserva |
| `MV.serialize_tras_attestations_devuelve` | con ese mapa, `serialize_justifications` devuelve pidiendo sólo las otras dos hipótesis |

Por qué vale:

- `construir_mapa_de_votos` arma cada lista con el tramo de una raíz, que mide
  exactamente `validator_count`.
- En el loop, lo único que agrega una lista es un voto nuevo, y la agrega con
  `validator_count` votos en falso.
- Marcar un voto cambia un bit, no el largo.
- Sacar una raíz ya justificada, y filtrar al finalizar, sólo copian listas que
  ya estaban.

Son resultados del tipo "si devuelve": no dicen que el loop termine, dicen qué
mapa deja cuando termina. Es lo que hace falta para descargar una hipótesis.

Como control negativo le sacamos al loop el dato de que la lista nueva mide
`validator_count`. La prueba deja de cerrar.

**Lo que se sigue pidiendo.** Dos hipótesis:

- A lo sumo 4096 validadores. `validator_count` es `state.validators.len()` y
  4096 es el límite de ese tipo, pero el `SszList` de este crate no lleva el
  límite como invariante.
- A lo sumo 262144 raíces en el mapa. Esta es la difícil. El loop puede agregar
  una raíz por attestation, así que la cuenta fácil da "las raíces del estado
  más las attestations", que no alcanza. La cota de verdad sale de otro lado:
  las raíces del mapa son todas distintas y todas están en el historial, que
  tiene a lo sumo 262144 entradas. Ese invariante está demostrado más abajo, en
  **La cota de raíces sale de un invariante**.

`MV.construir_mapa_acotado` depende sólo de los tres axiomas de Lean.
`MV.loop_conserva_acotado` depende de once y
`MV.serialize_tras_attestations_devuelve` de catorce; el detalle está en la
tabla de **La base de confianza**.

### `try_finalize` no entra en pánico

Es la función que, cuando una justificación cierra un tramo sin slots
justificables en el medio, avanza la finalidad, corre la ventana y saca del
mapa de votos las raíces que quedaron atrás.

| Hipótesis | Para qué |
|---|---|
| el `source` es anterior al `target` | que `source.slot + 1` no desborde |
| la ventana no pasa de 262144 bits | que `shift_window` no aborte |

**`source.slot + 1` deja de ser una precondición no enunciada.** Estaba en
**Límites honestos** desde el principio: con `source.slot = u64::MAX` el
incremento desborda. Ahora está escrita como hipótesis, y la hipótesis es
natural: que el source sea anterior al target. En el único lugar donde se
llama a `try_finalize` eso ya está garantizado, porque `is_valid_vote` lo
chequea, y ese chequeo está demostrado más arriba.

**La capacidad de la ventana sale de los invariantes.**
`NP5.try_finalize_devuelve_inv` es el mismo resultado, pidiendo en vez de la
capacidad los dos invariantes que la transición conserva.

**El `HashMap` dejó de ser una hipótesis.** La consulta era una firma sin
contenido, y el enunciado pedía que devolviera. Ahora el `HashMap` está
modelado como una lista de pares clave-valor, y que la consulta devuelve está
demostrado. El detalle del modelo, y lo que cuesta creerle, está en **La base
de confianza**.

Lo que hubo que demostrar de nuevo:

- `filtrado`, el reemplazo de su `retain`, termina y no aborta, sin ninguna
  hipótesis. Es `NP5.filtrado_devuelve`.
- Copiar una lista de votos termina y no aborta. En la traducción `Vec::clone`
  es un loop.
- El avance de un rango de `u64`. La biblioteca de hax trae ese lema para
  `usize` y para `i32`, no para `u64`, y acá se recorren slots.

Controles negativos, dos. Sin "source anterior al target" queda abierto
exactamente el desborde de `source.slot + 1`. Sin la capacidad queda abierta
la precondición de `shift_window`.

Los dos resultados sobre `try_finalize` dependen de diez axiomas: los tres de
Lean, tres nativos y cuatro declaraciones. `NP5.filtrado_devuelve` depende sólo
de los tres de Lean.

### Las piezas de `process_attestations` no entran en pánico

`process_attestations` es la función grande, y es la que más reescribimos: sus
iteradores y closures quedaron como funciones auxiliares con loops explícitos.
Antes de recorrerla entera hace falta saber que cada una de esas auxiliares
devuelve. Son diez resultados:

| Función | Hipótesis |
|---|---|
| `contar_datos_distintos` | ninguna |
| `hay_raiz_cero` | ninguna |
| `primer_bit_fuera_de_rango` | ninguna |
| `votos_vacios` | ninguna |
| `marcar_votos` | ninguna |
| `cuenta_votos` | ninguna |
| `sin` (sacar una raíz del mapa) | ninguna |
| `poner_si_falta` (agregar una raíz) | que haya lugar para una entrada más |
| `construir_mapa_de_votos` | que `raíces * validator_count` no desborde |
| `construir_root_to_slot` | que `finalizado + 1` no desborde |

Siete no piden nada. Las que cuentan llevan un contador que nunca pasa de lo
recorrido, y por eso su `+ 1` no desborda. Las que leen lo hacen con `get`, que
devuelve `None` fuera de rango en vez de abortar.

**El `HashMap`, entero y demostrado.** `try_finalize` sólo lo consulta.
`construir_root_to_slot` lo crea y lo llena, así que usa las tres operaciones:
`new`, `get` e `insert`. Las tres eran firmas sin contenido y que devolvieran
era una hipótesis. Ahora son definiciones sobre una lista de pares, y
`NP6.hashmap_devuelve` demuestra que devuelven, para todo mapa.

**Varios resultados dicen además cuánto mide lo que devuelven**: cuántas
entradas quedan en el mapa, cuántos votos tiene una lista. Es lo que hace falta
para encadenarlos en el loop, donde cada `push` necesita saber que hay lugar.

Controles negativos, tres. Sin el producto acotado queda abierto el desborde
de `(i + 1) * validator_count`. Sin `finalizado + 1` acotado queda abierto ese
desborde. Sin lugar en las claves no cierra el `push`.

Nueve de los diez dependen sólo de los tres axiomas de Lean. El de
`construir_root_to_slot` depende de seis: esos tres y tres declaraciones que el
`HashMap` recibe como argumento y no usa.

**Dónde se usan.** En la sección que sigue, que las junta.

### `process_attestations` no entra en pánico

Es la función grande de la transición: recorre las attestations del bloque,
cuenta votos, justifica y finaliza, y al final vuelve a escribir el mapa de
votos en el estado.

| Hipótesis | Para qué |
|---|---|
| a lo sumo 4096 validadores | que `3 * votos` y `2 * validator_count` no desborden, y que el bitlist de votos entre en su capacidad |
| las raíces del estado más las attestations del bloque no pasan de 262144 | que haya lugar en el mapa de votos y en `justifications_roots` |
| la ventana no pasa de 262144 bits | que `shift_window` no aborte |
| `finalizado + 1` no desborda | lo usa `construir_root_to_slot` |

`NP7.process_attestations_devuelve_inv` es el mismo resultado, con las dos
últimas sacadas de los invariantes que la transición conserva.

**Qué se lleva a lo largo del loop.** Cuatro cosas: la ventana no crece; ninguna
lista de votos es más larga que `validator_count`; el mapa crece a lo sumo una
entrada por vuelta; y el contador de attestations procesadas no pasa de las
recorridas.

**El punto delicado es `set_justified`.** Aborta si el target cae fuera de la
ventana. No pasa, porque sólo se llama después de un `is_valid_vote` que dio
`true` sobre el mismo estado, y ese chequeo ya leyó ese slot. Es un resultado
de **La ventana no entra en pánico**, usado acá. Del mismo voto sale que el
source es anterior al target, que es lo que pide `try_finalize`.

**La cota de raíces es más fuerte de lo necesario, y lo decimos.** "Raíces del
estado más attestations del bloque" es una condición suficiente sobre lo que
entra a la función: el loop agrega a lo sumo una raíz por attestation. No es un
invariante de los estados alcanzables. Un estado con muchas raíces pendientes y
un bloque lleno queda afuera de este resultado, lo cual no quiere decir que
aborte: quiere decir que acá no está demostrado. La cota fina, que las raíces
del mapa son distintas y están en el historial, está más abajo, en **La cota de
raíces sale de un invariante**.

El cuerpo del loop deja 170 condiciones que verificar, una por cada punto donde
algo podría fallar en cada camino posible. Son de ocho clases y se cierran por
clase.

Controles negativos, tres. Sin la cota de validadores quedan abiertos los dos
productos. Sin la cota de raíces quedan el producto `raíces * validator_count`,
el lugar en el mapa y el límite de raíces. Sin lo que dice `is_valid_vote`
quedan `set_justified` y el orden entre source y target.

Los dos resultados dependen de catorce axiomas: los tres de Lean, siete
nativos y cuatro declaraciones.

**Dónde se usa.** En la sección que sigue, que cierra la transición.

### La transición entera no entra en pánico

`process_block` y `state_transition` son las dos últimas de las doce. Con ellas
el resultado es sobre la función que ustedes exportan:

> Para todo estado y todo bloque que cumplan las hipótesis de abajo,
> `state_transition` devuelve.

"Devuelve" incluye devolver un error. Un bloque inválido se rechaza con `Err`.
Lo que el resultado descarta es el pánico y que la función no termine.

| Hipótesis | Qué es |
|---|---|
| `usize` de 64 bits | la plataforma |
| la ventana no pasa del último header; un hash por slot en el historial | dos invariantes, que la transición conserva |
| a lo sumo 4096 validadores | el límite de su tipo |
| las raíces pendientes más las attestations del bloque no pasan de 262144 | una condición suficiente sobre lo que entra |
| los tres `hash_tree_root` devuelven | el hash de este crate es un sustituto |

Las dos funciones sólo encadenan otras que ya estaban. Lo nuevo es el
pegamento, que lo que pide cada paso siga valiendo después del anterior:

- `process_slots` y `process_block_header` no tocan los validadores ni las
  raíces pendientes. Con eso, las hipótesis de `process_attestations` sobre el
  registro valen sobre el estado que le llega.
- Las dos conservan los invariantes de la ventana y del historial. De ahí saca
  `process_block_header` que el historial está alineado, y
  `process_attestations` la capacidad de la ventana.

**Qué no dice.** Que se pueda prescindir de todas las hipótesis. Las tres que
hablan del estado se conservan de un bloque al siguiente y valen en el génesis
(las dos secciones que siguen), así que sobre estados alcanzables ya no hay que
pedirlas. La cota de raíces, en este resultado, es una condición sobre las
entradas y no un invariante; más abajo se la reemplaza por uno. Y que el hash
devuelva no se puede demostrar acá.

Controles negativos, dos. Sin el invariante del historial queda abierta la
precondición del header. Si el header no dice que deja el registro como estaba,
quedan abiertas las dos hipótesis de `process_attestations` sobre validadores y
raíces.

Los dos resultados dependen de dieciséis axiomas, exactamente los mismos que la
definición de `state_transition` sin ningún teorema de por medio.

### Las hipótesis sobre el estado se conservan

El resultado de arriba pide tres cosas del estado de entrada: los dos
invariantes y que haya a lo sumo 4096 validadores. Si hubiera que suponerlas de
nuevo en cada bloque, el resultado serviría de poco. No hace falta:

| Resultado | Qué dice |
|---|---|
| `RV.state_transition_no_toca_validadores` | después de la transición los validadores son los mismos, acepte el bloque o lo rechace |
| `RV.state_transition_conserva_hipotesis` | si las tres hipótesis valen antes del bloque, valen después |

Los dos invariantes ya se sabía que se conservan. Faltaba la tercera, y sale por
el camino más corto: ninguna función de la transición escribe en `validators`.
`try_finalize` cambia la finalidad y la ventana; `serialize_justifications`
cambia las raíces pendientes y la lista plana de votos. Ojo con ese nombre:
`justifications_validators` es la lista de votos, no el registro de
validadores.

**Para qué sirve.** Para encadenar bloques. Alcanza con suponer las tres
hipótesis una vez, sobre el estado del que se parte, y siguen valiendo bloque
tras bloque.

**Lo que este encadenamiento no cubre.** La cota de raíces pendientes más
attestations, que depende de cada bloque y no es un invariante; se reemplaza en
**La cota de raíces sale de un invariante**. El punto de partida, el génesis,
está en la sección que sigue.

Son resultados del tipo "si devuelve". Como control negativo le sacamos al loop
de attestations lo que sabe de `try_finalize`: quedan abiertas justo las metas
sobre los validadores.

Los dos dependen de los mismos dieciséis axiomas.

### El génesis y los estados alcanzables

Hasta acá casi todo decía "si valía antes del bloque, vale después". Faltaba el
punto de partida. Agregamos al crate `State::from_genesis`, copiada sin cambios
de `crates/common/types/src/state.rs`, y se tradujo sin tocar nada.

Sobre el génesis:

| Resultado | Qué dice |
|---|---|
| `GEN.genesis_devuelve` | devuelve si hay a lo sumo 4096 validadores, y lo que devuelve es el estado inicial: slot cero, sin historial, sin ventana, sin raíces pendientes |
| `GEN.genesis_exige_validadores` | al revés: si devuelve, había a lo sumo 4096 validadores |
| `GEN.genesis_cumple_hipotesis` | el estado inicial cumple los dos invariantes, la cota de validadores y el caso base de `ST-4` |

**El `unwrap` del génesis.** `from_genesis` hace
`SszList::try_from(validators).unwrap()`. Con más de 4096 validadores eso
aborta, y los dos primeros resultados lo dicen de los dos lados. No lo
presentamos como defecto: es una función de arranque y el límite es el de su
tipo. Pero es un pánico alcanzable con una entrada mal armada, y queda escrito.

Sobre lo que se alcanza desde ahí. Un estado es *alcanzable* si es el que da
`from_genesis`, o el que deja `state_transition` aplicada a un estado
alcanzable. Cuenta también el estado que queda cuando un bloque se rechaza,
porque la transición modifica el estado en el lugar. Es la lectura más
exigente.

| Resultado | Qué dice |
|---|---|
| `GEN.alcanzable_cumple` | en todo estado alcanzable valen los dos invariantes, la cota de validadores y `ST-4` |
| `GEN.st4_alcanzable` | `ST-4`, completa |
| `GEN.state_transition_devuelve_alcanzable` | la transición no entra en pánico en ningún estado alcanzable |

**Lo que cambia.** El resultado de la transición entera pedía tres cosas del
estado. Sobre estados alcanzables ya no hay que pedirlas: salen del génesis. Lo
que sigue pidiendo son tres cosas: `usize` de 64 bits; que el hash devuelva; y
que las raíces pendientes más las attestations del bloque no pasen de 262144.
Las dos primeras no hablan del estado. La tercera sí, junto con el bloque, y se
va más abajo, en **La cota de raíces sale de un invariante**.

**`ST-7` va aparte.** Su hipótesis, que el checkpoint justificado esté en el
historial, es falsa en el estado inicial, que no tiene historial. No sale del
génesis como las otras: la establece el primer bloque aceptado. Es la sección
que sigue.

Como control negativo le sacamos a `from_genesis` la cota de validadores. Queda
abierta exactamente esa cota.

Los tres resultados sobre el génesis dependen de cuatro axiomas: los tres de
Lean y la firma de `fmt` del error del `unwrap`. Los tres sobre estados
alcanzables dependen de los dieciséis de `state_transition`.

### `ST-7` desde el génesis

`ST-7` pedía dos cosas del estado. Una es del catálogo: que el último header no
sea el del génesis (`hnz`). La otra era nuestra: que el checkpoint justificado
esté en el historial (`hhist`). Estaba demostrado que `hhist` se conserva, y no
que alguna vez empiece a valer. En el estado inicial es falsa, porque no hay
historial.

La establece el primer bloque que se acepta. En `process_block_header`, si el
último header es el del génesis, su código hace el anclaje: le pone al
justificado y al finalizado la raíz de ese header. Unas líneas más abajo agrega
**esa misma raíz** al historial, que estaba vacío. Queda en la posición 0, y el
justificado está en el slot 0. Eso es `hhist`.

El invariante que se demuestra tiene por eso dos casos:

| Caso | Qué dice del estado |
|---|---|
| inicial | el último header es el del génesis, el historial está vacío y el justificado está en el slot 0 |
| anclado | el último header no es el del génesis y el justificado está en el historial: las dos hipótesis de `ST-7` |

Se pasa del primero al segundo en un solo lugar, y no se vuelve.

| Resultado | Qué dice |
|---|---|
| `G7.aceptar_saca_del_genesis` | si `process_block_header` acepta, el último header deja de ser el del génesis |
| `G7.state_transition_conserva_inv7` | la transición conserva el invariante, acepte o rechace |
| `G7.alcanzable_inv7` | el invariante vale en todo estado alcanzable |
| `G7.justificado_en_el_historial` | `hhist`, establecida: en todo estado alcanzable que ya pasó el anclaje, el justificado está en el historial |
| `G7.st7_alcanzable` | `ST-7` sobre los estados alcanzables |

```lean
theorem G7.st7_alcanzable (st st' : tipos.State) (block : tipos.Block)
    (res : core.result.Result Unit stf.Error)
    (h64 : UScalarTy.Usize.numBits = 64) (ha : Alcanzable st)
    (hnz : st.latest_block_header.slot ≠ 0#u64)
    (h : stf.state_transition st block = ok (res, st')) :
    (st'.latest_justified = st.latest_justified ∨
      st.latest_justified.slot < st'.latest_justified.slot) ∧
    (st'.latest_finalized = st.latest_finalized ∨
      st.latest_finalized.slot < st'.latest_finalized.slot)
```

**`hnz` queda, y tiene que quedar.** En el bloque que ancla, la raíz del
justificado cambia en el slot 0 a propósito. `ST-7` es falsa para ese paso, y
el catálogo la enuncia fuera del génesis por eso mismo. Desde cuándo vale `hnz`
también está dicho: desde el primer bloque aceptado
(`G7.aceptar_saca_del_genesis`) y de ahí en más siempre
(`ST2.state_transition_conserva_no_genesis`).

**Lo que esto dice del test.** El estado de
`same_slot_root_swap_needs_a_justified_root_off_the_chain` —justificado en
`(4, X)` con otra raíz en `historical_block_hashes[4]`— no se alcanza aplicando
bloques desde `from_genesis`. Antes lo creíamos; ahora está demostrado. La
diferencia con la especificación ante un empate de slots sigue en el código,
pero sólo la puede mostrar un estado que no salió del génesis, como un ancla de
checkpoint-sync mal formada.

**Un rechazo que modifica el estado.** `process_block_header` hace el anclaje
antes del chequeo de `SlotGapTooLarge`. Si el primer bloque se rechaza por ese
error, el estado queda con las dos raíces de checkpoint ya cambiadas y con el
header del génesis todavía. No rompe el invariante: el caso inicial habla del
slot del justificado, no de su raíz. Lo contamos porque es el único rechazo del
header que no deja el estado como estaba, y hubo que mirarlo para que la
demostración cerrara.

Como controles negativos cambiamos el enunciado del anclaje de dos maneras:
comparando contra la raíz que el justificado tenía *antes*, y sacando la
hipótesis de que el último header sea el del génesis. En los dos casos queda
abierta la misma meta: que esa raíz sea la que se agregó al historial. Y sin la
condición "si acepta", `aceptar_saca_del_genesis` queda abierta en las ramas
que rechazan.

Los cuatro resultados sobre la transición piden `usize` de 64 bits, por el
invariante del historial, y dependen de los dieciséis axiomas de
`state_transition`. `G7.aceptar_saca_del_genesis` depende de siete: los tres de
Lean, tres nativos y la firma de `fmt`.

### El ordenamiento de raíces ordena

`serialize_justifications` ordena las raíces antes de escribirlas en el estado,
y el comentario de su código dice para qué: *"Sorting ensures that every node
produces identical state representation"*. Ahí ustedes llaman a `.sort()`.
Nosotros lo reemplazamos por una inserción escrita a mano, `claves_ordenadas`,
porque `sort` no tiene modelo. Estaba demostrado que el reemplazo termina.
Faltaba que ordenara, y un ordenamiento escrito a mano que no ordena es justo
el error que una reescritura puede meter sin que ningún test lo note.

| Resultado | Qué dice |
|---|---|
| `ORD.comparacion_es_lexicografica` | el `<` traducido entre dos `H256` da `true` exactamente cuando el primero es menor en el orden lexicográfico de sus bytes |
| `ORD.claves_ordenadas_ordena` | lo que devuelve está en orden, y es una permutación de las claves del mapa |
| `ORD.claves_ordenadas_canonica` | dos mapas con las mismas raíces, en cualquier orden, dan la misma lista |
| `ORD.serialize_escribe_ordenado` | lo que queda en `state.justifications_roots` está ordenado y son las raíces del mapa |
| `ORD.serialize_raices_canonicas` | y no depende del orden en que el mapa las tenía |

```lean
theorem ORD.claves_ordenadas_ordena (m : mapa.MapaVotos)
    (r : alloc.vec.Vec tipos.H256)
    (h : mapa.MapaVotos.claves_ordenadas m = ok r) :
    r.val.Pairwise MenorIgual ∧ r.val.Perm m.claves.val
```

**Las dos mitades hacen falta.** "Está en orden" sola también la cumple una
función que devuelve la lista vacía. "Es una permutación" dice que no se
perdió, no se inventó y no se repitió ninguna raíz. Y `Pairwise` es la forma
fuerte de "en orden": cada elemento es menor o igual que *todos* los que vienen
después, no sólo que su vecino.

**El orden no lo definimos nosotros.** `MenorIgual a b` quiere decir que los
bytes de `b`, como lista de naturales, no son menores que los de `a` con el `<`
que Lean trae para listas, que es el lexicográfico. No inventamos un orden para
después demostrar que ordenamos según él.

**El último resultado es el comentario de ustedes, para ese campo.** Dos nodos
que llegan a las mismas raíces pendientes habiéndolas insertado en distinto
orden escriben la misma `justifications_roots`. Sale de que una lista ordenada
con los mismos elementos es única, y eso pide que el orden sea antisimétrico:
dos `H256` que no son menores uno que el otro son el mismo.

**De qué depende, dicho con cuidado.** Los tres primeros resultados dependen
sólo de los tres axiomas de Lean. Pero se apoyan en una afirmación de modelado
nuestra: que el `Ord` de `[u8; 32]` es el orden lexicográfico. Es una
definición, y `#print axioms` no la lista. Hasta acá esa definición se usaba
sólo para decir que la comparación devuelve; éste es el primer resultado que
usa *qué* devuelve. Si el `Ord` real de los arrays fuera otro, estos teoremas
hablarían de un programa que no es el de ustedes. La documentación de `core`
dice que es el lexicográfico.

**Lo que no está acá.** Que `justifications_validators` —los votos, volcados en
el mismo orden que las raíces— también coincida entre dos nodos, y por lo tanto
que coincida el estado entero. Está dos secciones más abajo, en
**`serialize_justifications` no depende del orden del mapa**.

Como controles negativos, dos. Sin la hipótesis de que el prefijo ya estaba
ordenado, el invariante de la inserción no arranca: queda abierta
`MenorIgual a b` para dos posiciones cualesquiera del prefijo. Y con la
comparación enunciada al revés no cierra ninguno de los tres casos de
`Ordering`.

Los dos resultados sobre `serialize_justifications` dependen de siete axiomas:
los tres de Lean, tres nativos y la firma de `fmt`.

### La cota de raíces sale de un invariante

La ausencia de pánico pedía una cosa de cada bloque: que las raíces pendientes
del estado más las attestations del bloque no pasaran de 262144. Era una
condición suficiente y gruesa, y había que suponerla bloque por bloque. Acá se
reemplaza por un invariante.

**El invariante.** Las raíces pendientes del estado (`justifications_roots`) no
se repiten, y todas están en el historial de hashes. De ahí sale la cota por
palomar: no puede haber más raíces pendientes que hashes en el historial, y el
historial tiene a lo sumo 262144.

**Por qué vale sobre su código.** Al mapa de votos le entran raíces por dos
lados: las que el estado ya tenía, y la raíz del target de cada voto válido. Y
`is_valid_vote` sólo acepta un voto si
`historical_block_hashes[target.slot] == target.root`. Todo lo que entra, entra
por `poner_si_falta`, que no repite. Lo demás (`sin`, y el `filtrado` de
`try_finalize`) sólo saca. Al final `serialize_justifications` escribe en el
estado exactamente las claves del mapa, que es lo que dice la sección anterior:
por eso hacía falta primero.

| Resultado | Qué dice |
|---|---|
| `RZ.h256_eq_iff` | la igualdad traducida de `H256` es la igualdad, en los dos sentidos |
| `RZ.poner_si_falta_no_repite` | `poner_si_falta` no repite claves |
| `RZ.state_transition_conserva_raices` | la transición conserva el invariante, acepte o rechace |
| `RZ.alcanzable_raices` | el invariante vale en todo estado alcanzable |
| `RZ.raices_pendientes_acotadas` | en todo estado alcanzable hay a lo sumo 262144 raíces pendientes |
| `RZ.process_attestations_devuelve_con_invariante` | `process_attestations` no entra en pánico, con el invariante en lugar de la cota por bloque |
| `RZ.state_transition_devuelve_con_invariante` | lo mismo para la transición entera |
| `RZ.state_transition_devuelve_desde_genesis` | la transición no entra en pánico en ningún estado alcanzable |

```lean
theorem RZ.state_transition_devuelve_desde_genesis (st : tipos.State)
    (block : tipos.Block)
    (h64 : UScalarTy.Usize.numBits = 64) (hd : HashDevuelve)
    (ha : Alcanzable st)
    (hatts : block.body.attestations.items.val.length ≤ 4096) :
    ∃ r, stf.state_transition st block = ok r
```

**Lo que queda pedido del bloque, y por qué no es lo mismo que antes.** Una
sola cosa: que su lista de attestations no tenga más de 4096 elementos. Ése es
el límite de su tipo. En el Rust no hace falta pedirlo: el campo de `SszList`
es privado, y una lista sólo se construye vacía o con `try_from`, que chequea
la capacidad. La traducción a Lean no conserva esa garantía —ahí `SszList` es
una estructura con un campo libre— y por eso aparece como hipótesis. Se usa
para que el contador del loop de attestations no desborde. La hipótesis vieja
hablaba del contenido del estado y del bloque juntos; ésta es un límite de tipo
que el Rust ya cumple.

**La igualdad de `H256`, del otro lado.** Para `ST-7` habíamos demostrado que si
la igualdad traducida devuelve `true`, los dos valores son iguales. Para saber
que `poner_si_falta` no repite hace falta lo contrario: que dos raíces iguales
den `true`, o sea que la búsqueda lineal las encuentre. `RZ.h256_eq_iff` junta
las dos mitades.

**Lo que no cambia.** Sigue pidiendo `usize` de 64 bits y que el hash devuelva.
Y los resultados anteriores, con la cota por bloque, siguen ahí: sirven para un
estado que no salió del génesis pero cumple sus hipótesis.

Controles negativos, dos. Sin saber que el target de un voto válido está en el
historial, el loop de attestations no cierra. Y sin saber que la búsqueda que
no encuentra la clave es porque no está, `poner_si_falta` queda con una meta
abierta: que la clave no estaba.

Los dos primeros resultados dependen sólo de los tres axiomas de Lean. El de
`process_attestations`, de catorce. Los otros cinco, de los dieciséis de
`state_transition`.

### `serialize_justifications` no depende del orden del mapa

La sección del ordenamiento dejó una mitad: `justifications_roots` no depende
del orden en que el mapa tenía las raíces. `serialize_justifications` escribe
un campo más, `justifications_validators`: la lista plana de votos, volcada
raíz por raíz siguiendo las raíces ya ordenadas. Faltaba ése.

En su código `justifications` es un `HashMap`, y un `HashMap` se recorre en un
orden que no está fijado. Ordenar las raíces es lo que hace que dos nodos
escriban el mismo estado, que es lo que dice su comentario. Acá el mapa es una
lista de pares, y el enunciado es el mismo: dos listas con las mismas entradas,
en cualquier orden, dan el mismo estado.

| Resultado | Qué dice |
|---|---|
| `CAN.volcar_votos_mismas` | volcar los votos de una raíz da lo mismo desde cualquiera de los dos mapas |
| `CAN.serialize_no_depende_del_orden` | `serialize_justifications` sobre los dos mapas es la misma cuenta |
| `CAN.serialize_canonica` | el estado que queda es el mismo, entero |

```lean
theorem CAN.serialize_no_depende_del_orden {m1 m2 : mapa.MapaVotos}
    (he : MismasEntradas m1 m2) (s : tipos.State) (vc : Std.Usize) :
    stf.serialize_justifications s m1 vc = stf.serialize_justifications s m2 vc
```

**Es una igualdad entre programas.** No dice "si los dos devuelven, devuelven
lo mismo". Dice que las dos llamadas son la misma cuenta: si una aborta, la
otra también.

**Qué pide de los dos mapas.** `MismasEntradas m1 m2` dice que representan el
mismo diccionario: las listas de pares (raíz, votos) son permutación una de la
otra, las raíces no se repiten, y hay tantas raíces como listas de votos. Las
dos últimas son lo que hace que una lista de pares sea un diccionario; sin
ellas, "el mismo mapa en otro orden" no quiere decir nada.

**Cómo, porque se puede reusar.** No describimos bit por bit lo que se escribe.
`voto` y `largo_votos` sólo miran la lista de votos de la posición que les
pasan, así que el loop que vuelca una raíz depende nada más que de esa lista; y
la lista de votos de una raíz es la misma en los dos mapas. Con eso los dos
loops son el mismo programa, sin invariantes y sin aritmética de índices. La
técnica sirve cada vez que una función mira una colección sólo a través de una
búsqueda.

**De qué depende.** De la misma afirmación de modelado que el ordenamiento: usa
que las raíces ordenadas coinciden, y eso se apoya en que el `Ord` de
`[u8; 32]` sea el lexicográfico.

**Lo que no está.** Dos cosas. Que el mapa que arma `process_attestations`
tenga tantas raíces como listas de votos: que las raíces no se repiten sí está,
en la sección anterior. Y la relación entre nuestra lista de pares y el
`HashMap` de ustedes, que es lo que haría falta para decir algo sobre un
recorrido concreto de ese `HashMap`.

Controles negativos, dos. Sin usar que las dos posiciones tienen la misma lista
de votos, los cuerpos de los dos loops no coinciden. Y si la búsqueda
devolviera la posición siguiente a la de la clave, el lema de la búsqueda no
cierra.

`CAN.volcar_votos_mismas` depende de cinco axiomas: los tres de Lean, uno
nativo y la firma de `fmt`. Los otros dos, de siete.

### Qué es esto contra el catálogo, dicho exacto

`ST-3` en
[`NyxFoundation/formal-leanSpec`](https://github.com/NyxFoundation/formal-leanSpec)
está enunciada sobre `State.transition` — la transición de un bloque entera — y
acota los dos slots de checkpoint a la vez (`State.checkpoint_monotone`).
`ST3.state_transition_no_retrocede` es ese enunciado, sobre el
`state_transition` de ustedes tal como lo traduce la cadena de herramientas. Dos
diferencias, para que nadie lea más de lo que hay:

**Habla de otro programa.** El catálogo demuestra la proposición sobre su propio
modelo en Lean de la especificación. Esto la demuestra sobre el Rust de este
crate, con los sustitutos que se listan en **Límites honestos**. Misma
proposición, otro objeto: no es una demostración del teorema del catálogo, y el
del catálogo no es una demostración sobre el código de ustedes.

**No necesita `AnchorWF`.** El teorema del catálogo carga una hipótesis extra,
`AnchorWF s` — si el último header está en el slot 0, los dos checkpoints están
en el slot 0 — porque en su modelo el anclaje de génesis fuerza los checkpoints
a slot 0, lo que hace falso el enunciado desnudo para estados adversarios. El de
ustedes asigna sólo las raíces, así que la hipótesis no hace falta. En los
estados alcanzables desde el génesis los dos coinciden, porque ahí los slots ya
son 0; en estados arbitrarios el código de ustedes y ese modelo se comportan
distinto, y eso vale saberlo sea cual sea el comportamiento buscado. Chequeado
contra `formal-leanSpec` en `ba72845`.

**Sobre un estado cualquiera, `ST-7` necesita una hipótesis que el catálogo no
tiene.** `State.checkpoint_forward` pide sólo que el último header no sea el del
génesis. `ST7.state_transition_adelante` pide además `hhist`, y sin ella es
falsa. Acá la diferencia no es de modelado sino de comportamiento: ante un
empate de slots, su código y la especificación eligen distinto. Sobre los
estados alcanzables desde el génesis la diferencia desaparece:
`G7.st7_alcanzable` pide lo mismo que el catálogo. Chequeado contra `leanSpec`
`main` del 15 nov 2026 (`Checkpoint.advance_to` y `state_transition.py`) y
contra el `main` de ustedes, que ese día seguía idéntico a `35c074b`.

**`ST-4` está como en el catálogo.** El catálogo demuestra
`justified_ge_finalized` por inducción sobre sus estados alcanzables. Acá
también: `ST4.state_transition_justificado_ge_finalizado` es el paso —si vale
antes de un bloque, vale después— y `GEN.st4_alcanzable` es el invariante sobre
los estados alcanzables desde `from_genesis`.

Las propiedades no se eligieron porque parecieran demostrables. Ese catálogo
tiene treinta y cinco proposiciones — siete sobre la transición de estado, el
resto sobre fork choice, SSZ, el validador, red, storage y sync — y éstas son
las siete. Los enunciados son anteriores a nuestro trabajo sobre ellos, y eso
importa: elegir las propias propiedades vuelve el ejercicio circular.

### La base de confianza

`#print axioms` sobre cada resultado, con la salida en `axiomas.txt`:

| Resultado | Total | De Lean | Nativos | Declaraciones |
|---|---|---|---|---|
| los dos de aritmética | 3 | 3 | — | — |
| `bind_da_ok` | 1 | 1 | — | — |
| los dos de `try_finalize` | 10 | 3 | 3 | 4 |
| el del loop | 11 | 3 | 4 | 4 |
| `process_attestations`, justificación y finalidad | 14 | 3 | 7 | 4 |
| `process_slots`, los tres resultados | 3 | 3 | — | — |
| `process_block_header`, los tres resultados | 7 | 3 | 3 | 1 |
| `process_block`, `state_transition` (`ST-3`) | 16 | 3 | 9 | 4 |
| la igualdad de `H256` | 3 | 3 | — | — |
| `process_attestations` (`ST-7`) | 14 | 3 | 7 | 4 |
| `state_transition` (`ST-4`, `ST-6`, `ST-7`, conservación del header) | 16 | 3 | 9 | 4 |
| la ventana: ida y vuelta, `shift_window`, el compuesto | 5 | 3 | 1 | 1 |
| la ventana: `extend_to_slot`, los dos resultados | 6 | 3 | 2 | 1 |
| sin pánico: `is_slot_justified` | 3 | 3 | — | — |
| sin pánico: `set_justified` (los tres), `shift_window`, el compuesto | 5 | 3 | 1 | 1 |
| sin pánico: `extend_to_slot` | 6 | 3 | 2 | 1 |
| la ventana después del header, los tres resultados | 7 | 3 | 3 | 1 |
| el invariante de la ventana sobre `state_transition`, los dos | 16 | 3 | 9 | 4 |
| la cota del slot en el header | 7 | 3 | 3 | 1 |
| los dos invariantes juntos sobre `state_transition` | 16 | 3 | 9 | 4 |
| `shift_window` sobre la ventana de un estado con los invariantes | 5 | 3 | 1 | 1 |
| sin pánico: las cinco funciones chicas de `stf.rs` | 3 | 3 | — | — |
| sin pánico: `process_slots` | 3 | 3 | — | — |
| sin pánico: `process_block_header` | 7 | 3 | 3 | 1 |
| la comparación de `H256` devuelve | 3 | 3 | — | — |
| sin pánico: `claves_ordenadas` | 3 | 3 | — | — |
| sin pánico: `serialize_justifications` | 7 | 3 | 3 | 1 |
| el mapa de votos que se arma desde el estado | 3 | 3 | — | — |
| el mapa de votos a lo largo del loop de attestations | 11 | 3 | 4 | 4 |
| `serialize_justifications` con el mapa de `process_attestations` | 14 | 3 | 7 | 4 |
| sin pánico: `filtrado` | 3 | 3 | — | — |
| sin pánico: `try_finalize`, los dos resultados | 10 | 3 | 3 | 4 |
| sin pánico: nueve auxiliares de `process_attestations` | 3 | 3 | — | — |
| las tres operaciones del `HashMap` devuelven | 6 | 3 | — | 3 |
| sin pánico: `construir_root_to_slot` | 6 | 3 | — | 3 |
| sin pánico: `process_attestations`, los dos resultados | 14 | 3 | 7 | 4 |
| sin pánico: `process_block` y `state_transition` | 16 | 3 | 9 | 4 |
| los validadores y las hipótesis a lo largo de `state_transition`, los dos | 16 | 3 | 9 | 4 |
| el génesis, los tres resultados | 4 | 3 | — | 1 |
| los estados alcanzables, los tres resultados | 16 | 3 | 9 | 4 |
| `ST-7` desde el génesis: el header sale del génesis | 7 | 3 | 3 | 1 |
| `ST-7` desde el génesis, los otros cuatro | 16 | 3 | 9 | 4 |
| el ordenamiento ordena: la comparación y `claves_ordenadas`, tres resultados | 3 | 3 | — | — |
| el ordenamiento ordena: lo que escribe `serialize_justifications`, dos | 7 | 3 | 3 | 1 |
| la igualdad de `H256` en los dos sentidos, y `poner_si_falta` no repite | 3 | 3 | — | — |
| el invariante de las raíces pendientes, los tres resultados | 16 | 3 | 9 | 4 |
| sin pánico con ese invariante: `process_attestations` | 14 | 3 | 7 | 4 |
| sin pánico con ese invariante: la transición, los dos resultados | 16 | 3 | 9 | 4 |
| `volcar_votos` desde dos mapas con las mismas entradas | 5 | 3 | 1 | 1 |
| `serialize_justifications` no depende del orden, los dos resultados | 7 | 3 | 3 | 1 |

Tres categorías, con tres pesos distintos.

**Los tres de Lean** — `propext`, `Classical.choice`, `Quot.sound` — son el piso
de cualquier demostración clásica y no dicen nada sobre este código.

**Los nativos** son los `_native.decide.ax_*`: hechos que el núcleo de Lean no
chequeó, computados por el compilador. Aparecen nueve distintos en las doce
funciones. Los resultados sobre la transición entera dependen de los nueve;
los resultados sobre componentes dependen de menos, como muestra la tabla.
No son nuestros ni de ustedes. Definir una función en Lean puede exigir
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

devuelve los mismos diez axiomas que nuestro teorema sobre `try_finalize`, uno
por uno. Traduzcan la STF con esta cadena de herramientas y no demuestren nada,
y ya los tienen; demostrar encima no ensancha la base de confianza en una sola
entrada. Lo que no hicimos fue abrir cada uno de los nueve para nombrar el hecho
que representa.

**Las declaraciones** son nuestras, en `supuestos/FunsExternal.lean`:
veinte axiomas que son firma y nada más — el tipo de trait `BuildHasher`, el
hasher por defecto, el `hash` de `[T; N]`, y diecisiete stubs de `fmt` —
catorce de `Debug`, tres de `Display`. Existen para que el Lean generado
compile: Aeneas nombra esas operaciones en la salida, `CoreModels` no tiene
modelo para ellas, y sin la declaración el módulo muere con `Unknown
identifier` y no compila nada.

Es un agujero más leve que los axiomas nativos. Un axioma que no afirma nada no
rinde nada: no se puede derivar algo falso de él porque no se puede derivar
nada. Lo que cuesta es alcance — cualquier propiedad que dependa de cómo se
comporta lo declarado queda fuera. Modelos **con** contenido compran esas
propiedades al precio de afirmar cosas que podrían estar mal. Ese canje lo
aceptamos cuando la documentación dice sin ambigüedad qué hace la operación, y
cada vez que lo aceptamos está contado acá.

Afirmaciones reales hacemos cinco. Una es `U64::isqrt`, modelado como
`Nat.sqrt`: las dos son el piso de la raíz cuadrada. Otra es `mem::take`,
modelado como "devuelve lo que había y deja `Default::default()`". La tercera es
`bool::then`, modelado como "llama al closure sólo si el booleano es verdadero y
envuelve el resultado en `Some`". La cuarta es la comparación de arrays,
modelada como el orden lexicográfico de sus elementos. La quinta, y la más
grande, es el `HashMap`: una lista de pares clave-valor, donde `get` devuelve
el valor de la clave igual a la que se pide e `insert` reemplaza el valor si la
clave ya estaba y la agrega si no. Las cuatro últimas son lo que dice su
documentación. Les creemos a las cinco, pero son afirmaciones nuestras y no
algo que la cadena de herramientas verificó. Todas menos `isqrt` eran
declaraciones sin contenido al principio; por eso los resultados sobre
`state_transition` dependen ahora de dieciséis axiomas y no de veinticuatro.

Sobre el modelo del `HashMap` hay que decir dos cosas más. No mira el hash:
compara las claves con `Eq` y nada más. Eso coincide con un `HashMap` real
bajo el contrato que `HashMap` les pide a sus claves, que dos claves iguales
tengan el mismo hash. Y no dice nada sobre costo: una lista de pares busca en
tiempo lineal y un `HashMap` no. El modelo sirve para razonar sobre qué
devuelve, no sobre cuánto tarda.

Ninguna de las veinte carga peso en los teoremas de arriba: las propiedades
salen de las guardas, de las asignaciones y del historial de hashes, no de lo
que haga el hasher o el formateador. De las cinco afirmaciones de
modelado, `ST-3` no se apoya en ninguna; `ST-7` sobre la transición entera y los
invariantes del historial se apoyan en la de `mem::take`, porque necesitan que
el historial sobreviva a `process_block_header`; la ausencia de pánico de
`current_proposer` y de `slot_is_justifiable_after` se apoya en las de
`bool::then` e `isqrt`; la de `process_block_header` en las de `mem::take` y
`bool::then`; la de `serialize_justifications`, y todo lo que la llama, en la
de la comparación de arrays; que el ordenamiento ordena, y que
`serialize_justifications` no depende del orden del mapa, también, con una
diferencia: son los únicos que usan qué devuelve la comparación y no sólo que
devuelve; y la de `try_finalize`, `process_attestations` y
`state_transition` en la del `HashMap`. Eso es una afirmación sobre las
demostraciones, leída de ellas.
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
| `hax_mvcgen` | hax | el caballo de batalla. Parte un programa en condiciones de verificación y atraviesa cada llamada que tenga un lema `@[spec]`. Para el loop de attestations deja 52 abiertas en una demostración parcial y 170 en la de corrección total. |
| ternas de Hoare y lemas `@[spec]` | hax, sobre `Std.Do` | el idioma: un lema por función, y la táctica nombra el que falta. |
| `Aeneas.Std.loop_spec` | **Aeneas, no hax** | inducción sobre loops. Ésta es la que hay que usar. |
| `Hax.loop_range_spec_unsigned` | hax | probada, descartada — abajo. |
| `--charon-args="--start-from f"` | hax | probada, descartada — ver **Cómo meterlo en su árbol**. |
| `triple_mayThrow_of`, `of_triple_mayThrow` | nuestros | puentes entre una ecuación y una terna de Hoare. |
| `triple_total_of`, `of_triple_total` | nuestros | los mismos puentes para ternas de corrección total, las que no toleran pánico ni divergencia. |
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
forma condicional de los enunciados — condicional a que no haya pánico, no a
que el bloque se acepte.

**Dos puentes, y son la parte reutilizable.**

```lean
triple_mayThrow_of : (∀ v, x = ok v → P v) → ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄
of_triple_mayThrow : ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄ → x = ok v → P v
```

`triple_mayThrow_of` es el dual de `bind_da_ok`: convierte un teorema que ya se
tiene **como ecuación** en el lema `@[spec]` que la táctica consume, así un
resultado demostrado por el camino difícil queda usable sin rehacerlo. El otro
sentido devuelve una terna a ecuación, que es como están enunciados los
resultados de arriba. Veintitrés lemas `@[spec]` alimentan las dos primeras
demostraciones sobre el loop, las de `ST-3`; todos menos cuatro tienen una
postcondición trivialmente verdadera, presentes sólo para que la táctica pueda
atravesar una llamada que no puede mover `latest_justified`. Los cuatro con contenido son `is_none_spec`,
`try_finalize_spec`, `serialize_spec` y el propio teorema del loop, reusado como
lema para la función entera.

Subir todo a `state_transition` reusó esa maquinaria y costó poco. La mitad de
la finalidad es la demostración de la justificación otra vez, con otro
invariante y otro lema para `try_finalize` — los dos no pueden estar activos a
la vez, porque la táctica elige un solo lema por llamada. `process_block_header`
llevó catorce lemas triviales más, uno por cada llamada que ni recibe ni
devuelve el estado, y con ellos `hax_mvcgen` cerró solo todas las condiciones de
verificación. `process_block` y `state_transition` cierran igual, a partir de
los lemas de lo que llaman.

`ST-7` pidió dos cosas que `ST-3` no. Lemas con contenido para las operaciones
de `core` y `alloc` por las que pasa el historial —`Vec::push`, `mem::take`, el
`try_from` y el `expect` que lo vuelven a guardar, el `==` de `H256`—, porque
ahí ya no alcanza con atravesar la llamada: hay que saber qué devuelve. Y una
forma de componer lemas que tienen hipótesis: la hipótesis va como antecedente
**dentro** de la postcondición (`⌜ hip → conclusión ⌝`), no como argumento del
lema. Así `hax_mvcgen` lo consume igual que a cualquier otro, y la hipótesis se
descarga donde se usa, con lo que el paso anterior dejó demostrado.

Con eso armado, las otras de transición de estado no pidieron nada nuevo.
`ST-4` es el script del loop otra vez, con otro invariante, un lema de
`is_valid_vote` que dice que el voto va hacia adelante y otro de `try_finalize`
que dice a dónde mueve la finalidad. Las demostraciones nuevas son largas de
escribir y cortas de pensar: el trabajo está en elegir el invariante y en decir
qué devuelve cada llamada.

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
all its dependencies"* — y eso vale para el grafo de llamadas, no para los
tipos. La función salió traducida, el tipo no, y `TypesExternal_Template.lean`
salió vacío, así que la cadena de herramientas ni siquiera pide el tipo como
externo. El nombre que cuelga aparece en el `lake build`, no en la extracción. `--start-from`
cambia qué ítems emite Charon, no de qué crate define Aeneas, así que la copia
no es un atajo que tomamos: es la única ruta que la cadena de herramientas deja.

El costo de la copia es la deriva. Si `State` cambia, alguien tiene que
sincronizar `src/tipos.rs`. Los dos problemas desaparecen juntos si los tipos y
la STF terminan en un mismo crate, que es además lo que haría que el código
verificado **sea** el código de producción.

## Límites honestos

**El hash no es SSZ.** `hash_tree_root` acá es un hash polinomial escrito en el
subconjunto traducible: mezcla los campos en un acumulador de 64 bits. Dos
estados distintos dan casi siempre raíces distintas, y con eso alcanza para los
tests; no es resistente a colisiones ni interoperable. Ningún teorema de este
paquete depende de qué raíz devuelve: lo único que se le pide es que devuelva,
y va como hipótesis. Si alguno llegara a necesitar distinguir estados por su
raíz, del lado de Lean lo correcto sería declararlo opaco y cargar esa
propiedad como hipótesis explícita.

**`source.slot + 1` puede desbordar.** Enunciar el teorema de `try_finalize`
como terna de Hoare en vez de como ecuación destapó esto: con
`source.slot = u64::MAX`, el incremento que alimenta `slot_is_justifiable_after`
entra en pánico en un build de debug. La forma ecuacional lo esconde, porque
asume que la llamada devolvió `ok`. Ningún slot va a llegar ahí de manera
realista, y la guarda de arriba exige
`source.slot > state.latest_finalized.slot`, así que no es un bug vivo — pero es
una precondición no enunciada, y pueden preferir `checked_add` o una forma
saturante. Del lado de Lean ya está enunciada: `NP5.try_finalize_devuelve` la
lleva como hipótesis, en la forma "el source es anterior al target".

**`current_len + 1 + num_empty_slots` se suma antes de chequear el límite.** Es
el mismo tipo de hallazgo, en `process_block_header`, y salió igual: al pedir
que la función devuelva. Con un hash por slot en el historial la suma vale
`block.slot` y no desborda; ese invariante la transición lo conserva. Tampoco
es un bug vivo. Está contado en **`process_slots` y `process_block_header` no
entran en pánico**.

**La base de confianza no está vacía**, y lo que hay en ella está detallado en
**La base de confianza**, arriba: nueve axiomas nativos que vienen con la
traducción, veinte declaraciones nuestras que no afirman nada, y cinco
afirmaciones de modelado que sí hacemos.

**Nuestra reescritura no es idéntica al original en un punto.** Con una raíz
repetida en `justifications_roots`, el mapa de votos se arma distinto: ustedes
se quedan con la última aparición y nosotros con la primera. No se alcanza
desde el génesis. Está contado en **Un bug que la reescritura introdujo**.

**`ST-7` no vale sobre un estado cualquiera.** Vale sobre los estados
alcanzables desde el génesis, del primer bloque aceptado en adelante. Sobre un
estado que no salió de ahí hace falta además que el checkpoint justificado esté
en el historial, y sin esa hipótesis el enunciado es falso sobre su código,
como muestra el test.

**"Ordenado" es según nuestro modelo de la comparación.** Que el ordenamiento
de raíces ordena se apoya en que el `Ord` de `[u8; 32]` sea el orden
lexicográfico, que es una definición nuestra y no algo traducido por la
cadena de herramientas. La igualdad entre nodos está demostrada para lo que
escribe `serialize_justifications`, entre dos listas de pares con las mismas
entradas; no está relacionada con el `HashMap` de su código.

**Las funciones traducidas no se pueden ejecutar en Lean.** Lean las marca
`noncomputable`; entre otras cosas dependen de los axiomas de `fmt` que usa
`.expect()`. Se demuestra sobre ellas, pero no se las puede correr con `#eval`
para probar un caso concreto: la evidencia de que devuelven lo esperado en una
entrada dada son los tests de Rust.

**La ausencia de pánico es condicional.** Está demostrada para las doce
funciones de `stf.rs` y las cuatro de `justified_slots_ops`. Cinco de las doce
devuelven sin ninguna hipótesis. Las otras siete, `state_transition` entre
ellas, devuelven con las hipótesis de su sección. Una de esas hipótesis no se
puede demostrar en este paquete: que el hash devuelva.

**Del bloque queda pedido el límite de su lista de attestations.** El resultado
final sobre estados alcanzables pide que el bloque no traiga más de 4096
attestations. Es la capacidad del tipo, que el Rust garantiza y la traducción a
Lean no conserva. No es una condición sobre lo que el bloque dice, pero es una
hipótesis escrita y no un teorema.

**El invariante de la ventana supone `usize` de 64 bits.** Los resultados sobre
dónde termina la ventana llevan esa hipótesis explícita. En 32 bits los
`as usize` truncan y no valen tal cual.
