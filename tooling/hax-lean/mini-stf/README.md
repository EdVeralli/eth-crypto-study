# mini-stf — la STF de ethlambda en un crate solo

> **Para LambdaClass hay otro documento: [`PROPOSAL.md`](PROPOSAL.md), en
> inglés.** Ese es el entregable — qué es suyo y qué es nuestro, qué cambió en
> cada función, qué cuesta y cómo correrlo. Este README es nuestra bitácora:
> tiene el camino, los errores y las reglas que fuimos encontrando.


Crate armado para pasar la transición de estado de ethlambda por la cadena de
herramientas Rust → Lean (`hax` + Charon + Aeneas).

## Por qué existe

Charon compila el crate **y todas sus dependencias**, pero Aeneas sólo **emite
definiciones del crate local**. Los tipos que vienen de una dependencia salen
nombrados y sin definir, y el Lean generado no tipa. Lo medimos: un crate de
prueba que importaba `ethlambda-types` generó `Funs.lean` con firmas que
mencionan `ethlambda_types.state.State`, y un `Types.lean` con el namespace
vacío.

Para que `State` y `Block` existan del otro lado tienen que estar **adentro del
crate que se extrae**. De ahí este crate.

## Qué hay adentro

| módulo | de dónde sale | líneas |
|---|---|---|
| `stf` | **copia** de `state_transition/src/lib.rs`, sólo cambian los `use` | 646 |
| `justified_slots_ops` | **copia**, sólo cambian los `use` | 91 |
| `tipos` | definiciones de `ethlambda-types`, sin los derives | ~250 |
| `ssz` | **nuestro**: sustitutos de `SszList` y `SszBitlist` | ~130 |
| `stubs` | **nuestro**: `tracing` y `metrics` sin efecto | ~50 |

Lo copiado viene de [lambdaclass/ethlambda](https://github.com/lambdaclass/ethlambda)
(MIT): `crates/blockchain/state_transition/src/{lib,justified_slots_ops}.rs` y
`crates/common/types/src/{primitives,checkpoint,state,block,attestation}.rs`.

## Qué se cambió, exactamente

El cuerpo de `stf.rs` es **idéntico al original**. Lo único que cambia:

1. Las líneas `use`: los tipos vienen de `crate::tipos` en vez de
   `ethlambda_types`, y `tracing`/`metrics` de `crate::stubs`.
2. Se quitó `pub mod beacon;` — otra cadena de bloques, 47.160 líneas, no es
   la STF de lean.
3. Se quitaron los tests (líneas 655 en adelante del original).

Los stubs de logging existen justamente para no tocar el cuerpo: si en vez de
eso borráramos los `info!`, el código dejaría de ser el de ellos.

## Lo que se pierde, y hay que tenerlo presente

**Los contenedores SSZ son nuestros.** `SszList` y `SszBitlist` son envoltorios
de `Vec` con el mismo API. El flujo de control y la aritmética de la STF siguen
siendo de ethlambda; la representación de las listas, no. Cualquier teorema
hablará de la lógica de ellos sobre nuestros contenedores.

**`hash_tree_root()` ya NO es un stub.** Lo fue hasta el 30 oct, cuando devolvía
siempre `H256::ZERO`, y eso era peor que un detalle: la STF compara raíces en
cuatro lugares (`state_transition:85`, `process_slots:117`,
`process_block_header:164` y `:228`), así que con el cero esas comparaciones no
pasaban trivialmente — **se volvían falsas para cualquier entrada real**. Un
teorema sobre `state_transition` habría hablado de una función que rechaza casi
todos los bloques.

Ahora es un **hash polinómico** propio: multiplicar por un primo y sumar,
recorriendo los campos con loops de índice. No da los mismos valores que SSZ —no
sirve para interoperar— pero cumple lo único que la STF le pide: que estados
distintos den raíces distintas.

Del lado de Lean se trata al revés: ahí conviene declararlo **opaco** y agregar
la inyectividad como **hipótesis explícita** en los teoremas que la necesiten
("suponiendo que el hash no colisiona, vale `ST-3`"). Es la forma estándar de
modelar criptografía, y es lo que hace `fradamt/verified-consensus` con sus tres
axiomas delegados a ArkLib.

Los seis tests pasan con el hash real igual que con el stub, lo que confirma que
no estaban apoyados en el cero.

**Las advertencias de compilación son esperadas.** Seis variables sin usar: la
STF las calcula sólo para los mensajes de log, y los stubs descartan sus
argumentos.

## Correrlo

```bash
cd tooling/hax-lean
docker run --platform linux/amd64 -it \
  -v "$PWD/mini-stf:/work" \
  -v hax-cargo:/root/.cargo/registry \
  -v hax-cache:/root/.cache/hax \
  -v hax-elan:/root/.elan \
  hax-lean bash
```

Adentro, un solo comando:

```bash
cd /work && bash regenerar.sh
```

El script hace las tres cosas en orden: extrae, **vuelve a copiar lo escrito a
mano** (una extracción fallida borra los archivos de `Assumptions/`) y compila.
La extracción que corre adentro es:

```bash
cargo hax into lean \
  --charon-args="--opaque '{impl core::fmt::Debug for _}' \
                 --opaque '{impl core::fmt::Display for _}'"
```

⚠️ **Dos `--opaque`, no cuatro.** Hasta el 2 de noviembre hacían falta cuatro:
también `process_attestations` y `serialize_justifications`. Las dos se
reescribieron y hoy traducen con cuerpo completo. La sección de abajo cuenta los
cuatro porque es la historia de cómo se descubrieron, pero el comando de arriba
es el que vale.

## Los `--opaque`: los cuatro del principio, y por qué cada uno

Sin ellos Aeneas sale con código 2 y **no escribe un solo archivo**. Cada uno se
descubrió corriendo y leyendo el error; ninguno era predecible desde el código.

| Patrón | Qué pasaba sin él |
|---|---|
| `process_attestations` | *"Early returns inside of loops are not supported yet"*. Son exactamente **dos** `return` adentro de un `for`, en las líneas 348 y 359. |
| `serialize_justifications` | Su `.iter().flat_map(...)` obliga a traducir el `Iterator` de los slices de `std`, y ahí Aeneas falla con un problema de lifetimes en `find` — **adentro de `core`, no de nuestro código**. Eso dispara un error interno con stack trace de OCaml y mata la corrida entera. |
| `{impl core::fmt::Debug for _}` | `[Error] Unreachable` en cada `#[derive(Debug)]`. No alcanza con sacar el derive: `.expect()` lo exige. |
| `{impl core::fmt::Display for _}` | Lo mismo con los `write!` de `Display`. |

El patrón que vale la pena recordar: **dos de los cuatro bloqueos estaban en
código nuestro o de la biblioteca estándar, no en la STF.** Cuando Aeneas no
puede con la firma de algo transversal —como el iterador de slices— no deja un
`sorry` en una función: no emite nada.

## Resultado: el MVP cerrado

**La STF de ethlambda existe en Lean y Lean la acepta.** `lake build` cierra en
verde, 1736 jobs, cero errores.

**Diez de las doce funciones traducidas, cero `sorry`:**

```
def stf.state_transition        def stf.is_valid_vote
def stf.process_slots           def stf.attestation_data_matches_chain
def stf.process_block           def stf.slot_is_justifiable_after
def stf.process_block_header    def stf.is_proposer
def stf.current_proposer        def stf.try_finalize*
```

(\* `try_finalize` tradujo, pero despues la volvimos opaca: usa un `HashMap` y
modelar `get` y `retain` quedo para otro dia. Cuenta como nueve, no diez.)

Mas `justified_slots_ops` entero. Y los tipos salieron como estructuras de
verdad: `structure tipos.State`, `tipos.Block`, `tipos.Checkpoint`,
`tipos.AttestationData`, `ssz.SszList`, `ssz.SszBitlist`, `inductive stf.Error`.

## Lo que hubo que hacer, en orden

Seis vueltas, y **cada obstaculo solo se descubrio corriendo**. Ninguno era
predecible leyendo el codigo.

| # | Sintoma | Causa | Arreglo |
|---|---|---|---|
| 1 | 413 errores, cero archivos | un `dyn Error` en `ethlambda-storage` | el mini crate |
| 2 | *"Early returns inside of loops"* | 2 `return` adentro de un `for` | `--opaque process_attestations` |
| 3 | error interno de Aeneas, cero archivos | `Iter::find` **dentro de `core`** | `--opaque serialize_justifications` |
| 4 | `[Error] Unreachable` en cada derive | `Debug` / `Display` | `--opaque '{impl core::fmt::… for _}'` |
| 5 | `Unknown identifier HashMap`, `isqrt`, `mem::take`… | **`CoreModels` no cubre todo `core`/`std`** | modelos a mano en `Assumptions/` |
| 6 | `repeat_n`, `Vec::extend`, `Option::copied` | lo mismo | reescribir dos lineas |

## Dos reglas mas, aprendidas el 2 nov

**Un loop adentro de otro: no. Un loop que llama a una funcion con otro loop
adentro: si.** Son lo mismo computacionalmente, pero Aeneas convierte cada loop
en definiciones aparte y no logra unificar los contextos cuando estan anidados
en el mismo cuerpo:

```
[Error] Could not match the contexts
Source: 'src/tipos.rs', lines 244:31-246:33
```

El arreglo es sacar el loop interno a una funcion propia. Lo verifico
`State::hash_tree_root`, que tiene cinco loops y llama a `mezclar_raiz` —que
adentro tiene otro— y traduce sin problema.

**`Verification/ProofObligations.lean` importa `MiniStf.Extraction`, no
`MiniStf`.** El modulo raiz importa `Verification`, asi que importarlo desde ahi
es un ciclo (`bad import 'MiniStf'`). El encabezado que escribe hax ya lo dice.

## Los supuestos, que es donde hay que mirar

24 axiomas. **La mayoria es ruido**, pero no todos:

- **17 son `fmt`** — como se imprime un `H256`. Ningun teorema los va a tocar.
- **3 son las funciones opacas**: `process_attestations`, `serialize_justifications`,
  `try_finalize`. Agujeros reales, elegidos a conciencia.
- **5 son funciones de `core` sin modelo**: `isqrt`, `mem::take`, `bool::then`,
  y el `Ord` y el `Hash` de `[T; N]`.

⚠️ **`isqrt` es el que mas duele.** Es un axioma, y es justo lo que usa
`slot_is_justifiable_after` para detectar cuadrados perfectos — el teorema mas
lindo que habiamos identificado (la identidad de los numeros pronic). Esta
bloqueado hasta reemplazarlo por una definicion real sobre `Nat.sqrt`. Es el
primer supuesto que conviene cerrar.

### La auditoria, corrida el 30 oct

Salida completa en [`axiomas.txt`](axiomas.txt). Reproducir:

```bash
cp supuestos/RevisarAxiomas.lean proofs/lean/
cd proofs/lean && lake env lean RevisarAxiomas.lean
```

**Tres funciones salen limpias** — los tres estandar de Lean y nada mas:
`stf.process_slots`, `stf.attestation_data_matches_chain`,
`justified_slots_ops.is_slot_justified`.

**`isqrt` bloquea dos**: `slot_is_justifiable_after` y `is_valid_vote`. Un axioma
sin definicion es una funcion de la que no se sabe nada, asi que el teorema de
los pronic no es dificil: es imposible hasta reemplazarlo.

**Y cuatro `_native.decide.ax_*`**, que nadie pidio. Son native axioms —el
resultado lo calcula el compilador de Lean, el kernel no revisa— y los metio
Aeneas solo, probablemente al despachar condiciones de borde sobre las
constantes grandes del estado. Los arrastran `extend_to_slot`, `set_justified`,
`process_block_header` y, por transitividad, `state_transition` y
`process_block`.

Eso ultimo es un hallazgo que va mas alla de este crate: en los cuatro repos del
cuadro comparativo el native axiom siempre es rastreable hasta una linea que
escribio una persona. Aca no hay tal linea. Esta anotado en
`docs/repos-comparados.md`, seccion "El quinto caso".

## Que cambio del codigo de ethlambda

El cuerpo de `stf.rs` es el original **salvo una linea**, en `process_slots`:

```rust
// original
historical_block_hashes.extend(std::iter::repeat_n(H256::ZERO, num_empty_slots));
// aca
for _ in 0..num_empty_slots { historical_block_hashes.push(H256::ZERO); }
```

`repeat_n` y `Vec::extend` no estan en `CoreModels`. El loop hace lo mismo, pero
queda anotado: es un cambio, no una copia.

## La carpeta `supuestos/`

`proofs/` se regenera y pesa GB, asi que esta en el `.gitignore`. Pero
`Assumptions/TypesExternal.lean` y `Assumptions/FunsExternal.lean` **los
escribimos a mano** y hax no los pisa. Las copias viven en `supuestos/`; despues
de un `proofs/` nuevo hay que volver a ponerlas:

```bash
cp supuestos/TypesExternal.lean supuestos/FunsExternal.lean proofs/lean/MiniStf/Assumptions/
```

## El primer teorema, demostrado el 30 oct

En [`teoremas/ProofObligations.lean`](teoremas/ProofObligations.lean). Correrlo:

```bash
cp teoremas/ProofObligations.lean proofs/lean/MiniStf/Verification/
cd proofs/lean && lake env lean MiniStf/Verification/ProofObligations.lean
```

### Que dice

El comentario del codigo de ethlambda, en `slot_is_justifiable_after`, afirma esto:

```rust
// Pronic numbers have the form n(n+1): 2, 6, 12, 20, 30, 42, 56, ...
// Mathematical insight: For pronic delta = n(n+1), we have:
//   4*delta + 1 = 4n(n+1) + 1 = (2n+1)^2
// Check: 4*delta+1 is an odd perfect square
```

O sea que detecta pronics preguntando si `4·delta + 1` es un cuadrado perfecto,
en vez de factorizar. **Eso ahora esta demostrado:**

```lean
theorem pronic_iff_cuadrado (n : ℕ) :
    (∃ m, m * m = 4 * n + 1) ↔ (∃ k, n = k * (k + 1))
```

Y los dos teoremas dependen **solo de los tres axiomas estandar de Lean**
(`propext`, `Classical.choice`, `Quot.sound`). Ni native axioms ni agujeros
nuestros.

### Lo que encontro: un chequeo que sobra

El codigo pregunta **dos** cosas sobre `m = 4·delta + 1`: que sea cuadrado
perfecto **y** que sea impar (`m % 2 == 1`). La segunda **nunca puede fallar**
si la primera pasa: `4·delta + 1` es impar siempre, asi que su raiz tambien.

```lean
theorem chequeo_de_paridad_redundante (n m : ℕ) (h : m * m = 4 * n + 1) :
    m % 2 = 1
```

No es un bug — el resultado es correcto — pero es una condicion que siempre se
cumple. Aparecio al escribir el enunciado, que es para lo que sirve esto.

### Lo que todavia NO esta demostrado, y hay que ser claro

Los dos teoremas son sobre `ℕ`: demuestran **el contenido matematico del
comentario**, no una propiedad de la funcion generada. Falta el puente:

```lean
theorem slot_is_justifiable_after_correcta (slot fin : Std.U64) :
    stf.slot_is_justifiable_after slot fin = ok true ↔ ...
```

Ese es mas trabajo, y ahi va a aparecer lo interesante: `checked_mul delta 4`
falla cuando `delta ≥ 2^62`, asi que **la funcion devuelve `false` para deltas
pronic muy grandes**. Inalcanzable en la practica — son mas slots que los que
cabrian en la vida del universo — pero el enunciado tiene que decirlo. Ese es el
tipo de resultado que justifica el ejercicio.

## La red de seguridad: los tests del original

`src/stf.rs` termina con los **437 renglones de tests del `lib.rs` original**,
copiados tal cual; lo unico cambiado son los `use`. Correrlos:

```bash
cd /work && cargo test
```

Los seis pasan. Y **pasan por el motivo correcto**, que es lo que habia que
verificar antes de confiar en ellos:

- Llaman **directo** a `process_attestations` (cinco de seis) y a
  `attestation_data_matches_chain` (el otro). Ninguno pasa por
  `state_transition` ni `process_block_header`, que son los dos lugares donde el
  stub de `hash_tree_root` importaria.
- `hash_tree_root` aparece en los tests solo como
  `body_root: BlockBody::default().hash_tree_root()` — un campo que asignan y
  nunca verifican. Las aserciones son sobre `latest_justified`,
  `latest_finalized`, `justified_slots` y variantes de error.

**Y la cobertura cae justo donde hace falta.** Las tres funciones que hay que
reescribir para que traduzcan son `process_attestations`, `try_finalize` y
`serialize_justifications`, y las dos ultimas **solo se llaman desde la
primera**. Asi que los cinco tests que ejercitan `process_attestations` cubren
las tres.

Lo que NO cubren: `state_transition`, `process_block`, `process_block_header`,
`process_slots`, que no se van a tocar.

## El objetivo: una propuesta para LambdaClass

Esto empezo como prueba de factibilidad y tiene un destino mas concreto:
mostrarle a LambdaClass como se ve su STF escrita en el subconjunto que Aeneas
entiende, con sus tests en verde, y con `ST-3` demostrado.

`ST-3` es una de las 35 proposiciones de
[`NyxFoundation/formal-leanSpec`](https://github.com/NyxFoundation/formal-leanSpec),
el modelo en Lean del consenso nuevo: *"`latest_justified.slot` y
`latest_finalized.slot` nunca retroceden"*. Lo que la vuelve la vara ideal es que
**no la inventamos nosotros** y que la suite de ethlambda ya la afirma por
ejemplo: uno de sus tests se llama literalmente
`latest_justified_does_not_regress_within_block`. El teorema lo volveria
universal.

Para llegar hay que separar dos cosas, y mezclarlas arruinaria la propuesta:

| | Que es | Les sirve? |
|---|---|---|
| La reescritura de sus doce funciones | **la propuesta** | si, tal cual, en su repo |
| Nuestros sustitutos SSZ, el stub de hash, los `--opaque`, los modelos en `Assumptions/` | el banco de pruebas | no — ellos tienen los tipos reales |

Y hay un costo que tenemos que poner nosotros sobre la mesa: el codigo reescrito
es **menos idiomatico**. Un `for` con indices donde habia un
`.iter().filter().count()` es mas feo y mas facil de equivocar al leerlo. Eso es
mantenimiento, y una propuesta que no lo menciona no es creible.

## El bug del 4 nov: el error que no salía

Lo encontramos de rebote. Pablo mandó
[el manual de hax para Lean](https://hax.cryspen.com/manual/lean/quick_start/),
que trae soporte para invariantes de loop. Para escribir el invariante de
`process_attestations` había que leer con lupa cómo quedó ese loop traducido, y
leyéndolo apareció esto.

**Qué estaba mal.** El original corta con `return Err(...)` en tres lugares de
adentro del loop: el `?` de `is_valid_vote`, `EmptyAggregationBits` y
`AggregationBitsOutOfBounds`. Acá los `return` tuvieron que irse —Aeneas no los
soporta adentro de un loop— y se reemplazaron por una bandera, `fallo`. La
bandera se llenaba, hacía que las vueltas siguientes no trabajaran… **y después
nadie la miraba**. La función devolvía `Ok(())` con un bloque inválido, y encima
llamaba a `serialize_justifications`, que el original nunca alcanza al cortar.
Dos divergencias, no una.

**El arreglo**, al final de `process_attestations` y antes de serializar:

```rust
match fallo {
    Some(e) => return Err(e),
    None => {}
}
```

El `return` queda **afuera** del loop, así que no choca con la regla de Aeneas.

**Por qué los seis tests no lo vieron.** Los dos que chequean errores
(`rejects_justification_votes_length_mismatch` y
`rejects_empty_validator_registry`) prueban los errores de **antes** del loop,
que siempre estuvieron bien. Ninguno de los seis toca los tres de adentro. El
agujero estaba justo donde no mirábamos, y eso matiza algo que veníamos
diciendo: los tests verdes prueban que la reescritura preserva el comportamiento
**en los casos que cubren**, no en general.

**Los dos tests nuevos**, que no están en la suite de ethlambda:

| Test | Qué fuerza |
|---|---|
| `process_attestations_rejects_empty_aggregation_bits` | el mismo voto válido del test de regresión, sin un solo bit prendido → `EmptyAggregationBits` |
| `process_attestations_rejects_an_out_of_range_bit` | bits de largo 6 con el índice 5 prendido sobre 4 validadores → `AggregationBitsOutOfBounds { index: 5, validator_count: 4 }` |

Y se verificaron con un control, que es la parte que importa: **sacando el
arreglo, los seis de ethlambda pasan y los dos nuevos fallan.** Un test que no
falla cuando el bug está no prueba nada.

**Un efecto lateral que destrabó un teorema.** Antes, el loop generado
descartaba `fallo` al terminar: el acumulador era una tupla de cuatro y el
resultado de tres. Esa diferencia impedía aplicar `Hax.loop_range_spec_unsigned`,
que exige el mismo tipo en los dos lados. Con el arreglo, `fallo` tiene que
salir del loop y los dos tipos se igualan:

```
ControlFlow (Range × State × U64 × MapaVotos × Option Error)
            (        State × U64 × MapaVotos × Option Error)
```

O sea que arreglar el bug habilitó la mitad de `ST-3` que nos faltaba.

## Tres cosas que aprendimos del manual que mandó Pablo

**1. `--charon-args="--start-from <función>"` no trae los tipos de una
dependencia.** El manual dice que extrae la función *"along with all its
dependencies"*, y es cierto de la cadena de llamadas, no de los tipos. Probado
sobre `prueba-types`, un crate de una sola función que usa `State` de
`ethlambda-types`: la función salió traducida, el tipo no, y
`TypesExternal_Template.lean` quedó vacío —ni siquiera lo pide como externo—, así
que el `Unknown identifier` aparece recién en `lake build`.

**Conclusión: `src/tipos.rs` no sobra.** Charon compila el crate y todas sus
dependencias, pero Aeneas emite definiciones **sólo del crate local**, y
`--start-from` cambia el primer filtro, no el segundo. Antes copiábamos los tipos
por decisión nuestra; ahora es con la alternativa descartada por medición.

**2. El soporte de invariantes de loop es una táctica de Lean, no una anotación
de Rust.** `for_loop_with_invariant` reemplaza el `loop` que genera Aeneas por
`Hax.forLoopWithInvariant` y el invariante se escribe del lado de la
demostración. Pide un `for` sobre un rango de enteros **sin early returns
adentro** — que es exactamente la forma a la que nos obligó Aeneas. No hay que
tocar el Rust.

**3. El idioma de hax son ternas de Hoare, y pregunta más que una ecuación.**
`try_finalize_no_retrocede` está enunciado como `h : try_finalize ... = ok (...)`,
o sea **asumiendo que no falló**. La terna `⦃ pre ⦄ prog ⦃ post ⦄` no deja
asumirlo, y al enunciarlo así salta una obligación que la forma ecuacional
esconde:

```
a : UScalar.max UScalarTy.U64 < ↑source.slot + ↑1#u64
⊢ (ExceptConds.false.1 { down := Error.panic }).down
```

**`source.slot + 1` puede desbordar.** Con `source.slot = u64::MAX`,
`try_finalize` entra en pánico. El teorema que tenemos sigue siendo correcto —no
afirma nada sobre el caso de falla—, pero la propiedad más fuerte no se cumple
sin una precondición.

## Las dos mitades de ST-3, 5 nov

⚠️ **Ojo con como se dice.** `ST-3` en el catalogo esta enunciada sobre
`State.transition` -- la transicion de un bloque entera -- y acota los dos
slots de checkpoint a la vez. Lo que hay aca es cada mitad sobre el componente
donde ese campo se mueve: la justificacion en `process_attestations`, la
finalidad en `try_finalize`. **Eso no es la proposicion del catalogo**, y el
5 nov lo dijimos mal en la primera version de esta seccion.

Falta subir las dos a `state_transition`: que `process_slots` no toque los
checkpoints, que `process_block_header` no los baje, y que la mitad de
finalidad suba por el mismo loop. Y una trampa que el catalogo ya avisa: el
anclaje de genesis del primer bloque fuerza los checkpoints a slot 0, lo que
hace FALSO el enunciado desnudo para estados adversarios -- de ahi la hipotesis
`AnchorWF` que ellos cargan. Un lift que la ignore no cierra.

Y el conteo: son **35** proposiciones, no 36 (eso lo veniamos diciendo mal),
de las cuales **7 son de transicion de estado** y las otras 28 de partes que la
mini-STF no contiene: fork choice vive en el `Store`, SSZ es serializacion,
red, storage y sync no estan.

Dicho eso, lo demostrado:

| Teorema | Sobre | Dice |
|---|---|---|
| `try_finalize_no_retrocede` | `try_finalize` | el slot **finalizado** no retrocede |
| `try_finalize_no_toca_justified` | `try_finalize` | no toca el slot justificado |
| `ST3.process_attestations_loop_no_retrocede` | el loop | el slot **justificado** no retrocede en una vuelta |
| `ST3.process_attestations_no_retrocede` | **la funcion entera** | el slot justificado no retrocede |

El cuarto es el que mas pesa: habla de `process_attestations`, la funcion que
ethlambda llama, y no de una parte de ella. No cierra ST-3 -- para eso falta el
lift de arriba -- pero cubre el modo de falla que si les ocurrio. Base de axiomas: veinte -- tres estandar de
Lean, seis nativos de la biblioteca de tacticas de Aeneas, y once declaraciones
y modelos de `std` que solo existen para que las firmas chequeen.

### El lema del loop tenia que ser el de Aeneas, no el de hax

`Hax.loop_range_spec_unsigned` enuncia la obligacion del paso con `⇓`, que
exige que el cuerpo **no falle nunca**. Eso convierte "el slot justificado no
retrocede" en un teorema mucho mas grande: ausencia de panico en las doce
funciones que el cuerpo llama, seis con loops propios.

`Aeneas.Std.loop_spec` toma una postcondicion completa, con ramas de falla y
divergencia. Eligiendo `PostCond.mayThrow`:

- las obligaciones de falla y divergencia se descargan solas;
- el desborde de `attestations_processed + 1` deja de importar, asi que se cae
  la necesidad del invariante reforzado que habiamos anotado el 4 nov;
- tolerando la divergencia, el `∨ PostCond.div P` se satisface por la derecha
  y **no hace falta medida de terminacion**.

Y el enunciado que queda es condicional al exito, que es la forma correcta y no
una version debilitada: la propiedad habla de la transicion de estado, y si la
transicion falla el bloque se rechaza y no hay estado nuevo del que afirmar
nada.

### Los dos puentes

Es la pieza mas reutilizable del dia:

```lean
triple_mayThrow_of : (∀ v, x = ok v → P v) → ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄
of_triple_mayThrow : ⦃True⦄ x ⦃mayThrow (⌜P ·⌝)⦄ → x = ok v → P v
```

`triple_mayThrow_of` es el dual de `bind_da_ok`: convierte cualquier teorema que
ya tengamos **como ecuacion** en el lema `@[spec]` que `mvcgen` sabe usar. El
otro vuelve. Con los dos se demuestra del lado que conviene y se enuncia del
lado que se lee.

De ahi que `try_finalize_spec` y `serialize_spec` salgan en una linea de los
teoremas ecuacionales, sin rehacer nada.

### Lo que NO se pudo: la funcion entera como ecuacion

El primer intento del teorema 5 fue peleando los binds, como en los teoremas 2
y 3. No sale: el `let` que desarma la tupla que devuelve el loop es un `match`
sobre el par, `split` no lo atraviesa, y ni `simp only []` ni `dsimp only` lo
reducen. Con `mvcgen` si, porque maneja sola los cuatro `if` del preambulo y el
`match` de la bandera.

### ⚠️ Un axioma muerto pisando una definicion real

`Assumptions/FunsExternal.lean` todavia declaraba `axiom
stf.process_attestations` y `axiom stf.serialize_justifications`, de cuando las
dos eran `--opaque`, con las firmas viejas (`HashMap` donde hoy va
`mapa.MapaVotos`).

Y no chocaban con las definiciones generadas, que es lo peligroso: ese archivo
**no abre `namespace mini_stf`**, asi que declara `stf.foo` mientras el generado
declara `mini_stf.stf.foo`. Dos nombres distintos. Con `open mini_stf`, el
ambiguo `stf.foo` resuelve al axioma.

O sea que **se puede escribir un teorema contra el axioma en vez de contra el
codigo, y compila.** No prueba nada y parece que si. Lo unico que lo delata es
`#print axioms`.

Los nuestros estaban limpios y los dos axiomas ya se sacaron. Pero el riesgo es
estructural y no un descuido: hax siembra ese archivo **una sola vez** y despues
no lo vuelve a mirar, asi que cuando una funcion deja de ser opaca su axioma se
queda ahi. **Al sacar un `--opaque`, sacar tambien su axioma.**

## Lo que sigue

Los tres hallazgos de herramienta -- que los axiomas nativos vienen de la
biblioteca de tacticas de Aeneas, que `--start-from` no trae los tipos de una
dependencia, y que un axioma de `Assumptions/` puede pisar una definicion
generada sin que nada avise -- quedan anotados aca y en el PROPOSAL, pero **no
vamos a reportarlos a Cryspen**. Decision tomada el 6 nov.

1. **Subir las dos mitades a `state_transition`**, que convierte lo que hay en
   ST-3 de verdad. Es el paso corto, y el que va a destapar la trampa del
   anclaje de genesis.

   Despues, de las 7 de transicion de estado hay dos al alcance: **ST-6** (la
   finalizacion es irreversible), que el catalogo dice que es *"the
   `latestFinalized` half of ST-3"* -- o sea nuestro teorema 2 subido -- y
   **ST-7** (el reemplazo de checkpoint es estrictamente hacia adelante, sin
   cambio de raiz en el mismo slot). Esa ultima vale por si sola: ethlambda usa
   `max_by_key`, que ante empate devuelve el SEGUNDO argumento, o sea que cambia
   la raiz dejando el slot igual -- justo lo que ST-7 prohibe. Puede que no sea
   alcanzable porque `is_valid_vote` chequea por slot y rechazaria el voto
   antes, pero entonces estaria a salvo por otro motivo que el de la
   especificacion, y eso es lo que un teorema aclara.
2. **Reescribir los teoremas 2 y 3 como ternas** si alguna vez hace falta: hoy
   no, los puentes los hacen usables como estan.
