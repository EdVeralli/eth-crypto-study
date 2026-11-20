# mini-stf — la STF de ethlambda en un crate solo

> **Para LambdaClass hay otro documento: [`PROPOSAL.md`](PROPOSAL.md), en
> inglés, y su par en castellano, [`PROPUESTA.md`](PROPUESTA.md).** Ese es el
> entregable — qué es suyo y qué es nuestro, qué cambió en
> cada función, qué cuesta y cómo correrlo. Este README es nuestra bitácora:
> tiene el camino, los errores y las reglas que fuimos encontrando.

Esta bitácora está en orden cronológico y conserva los números de cada etapa.
El estado final está en [`PROPUESTA.md`](PROPUESTA.md) /
[`PROPOSAL.md`](PROPOSAL.md); donde un número de acá difiere, vale el de la
propuesta.


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
| `stf` | **copia** de `state_transition/src/lib.rs`: ocho de las doce funciones sin cambios, cuatro reescritas, 19 funciones auxiliares nuestras, y al final el módulo de tests del original (437 renglones) con tres tests agregados | 1585 |
| `justified_slots_ops` | **copia**, sólo cambian los `use` | 90 |
| `tipos` | definiciones de `ethlambda-types`, sin los derives | 431 |
| `ssz` | **nuestro**: sustitutos de `SszList` y `SszBitlist` | 154 |
| `mapa` | **nuestro**: lista de asociación que reemplaza un `HashMap` | 245 |
| `stubs` | **nuestro**: `tracing` y `metrics` sin efecto | 49 |

(Líneas al 15 nov 2026.)

Lo copiado viene de [lambdaclass/ethlambda](https://github.com/lambdaclass/ethlambda)
(MIT): `crates/blockchain/state_transition/src/{lib,justified_slots_ops}.rs` y
`crates/common/types/src/{primitives,checkpoint,state,block,attestation}.rs`.

## Qué se cambió, exactamente

> Nota del 15 nov 2026: esta sección describe el estado del 29 oct. Después se
> reescribieron cuatro de las doce funciones y los tests volvieron a `stf.rs`,
> con dos más nuestros; está contado más abajo en esta misma bitácora ("La red
> de seguridad", "El bug del 4 nov").

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

> Nota del 15 nov 2026: éstos son los números del primer cierre. El estado
> final es **doce de doce** funciones traducidas, cero `sorry`, y `lake build`
> con 1742 jobs el 6 nov (1743 en el rearmado en limpio del 12 nov).

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

> Nota del 15 nov 2026: lo que sigue es la foto del 30 oct. Al final quedaron
> **28 axiomas declarados** en `supuestos/FunsExternal.lean`: los 17 de `fmt`
> (14 `Debug` + 3 `Display`) y 11 firmas de `core`/`std`. (Desde la tarde del
> 15 nov son 27: `mem::take` paso a ser una definicion, por lo mismo que
> `isqrt`. Ver la nota de ST-7 en "Lo que sigue". Y desde el 17 nov son 26:
> tambien `bool::then`.) Ya no hay ninguna
> funcion de la STF opaca (los dos `--opaque` que quedan son solo
> `Debug`/`Display`), e `isqrt` es una definicion sobre `Nat.sqrt` desde el
> 30 oct, no un axioma. Y una cuenta que abajo no cierra: el desglose suma 25
> y el total dice 24. El 24 es el correcto para ese dia: en el commit `f028e61`
> el archivo tenia 17 + 2 + 5, porque de las tres funciones opacas solo
> `process_attestations` y `serialize_justifications` tenian su axioma ahi.

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

(Nota del 15 nov 2026: se cerro ese mismo 30 oct. `isqrt` paso a ser una
definicion sobre `Nat.sqrt` y el teorema de los pronic esta mas abajo.)

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
los pronic no es dificil: es imposible hasta reemplazarlo. (Nota del 15 nov
2026: reemplazado el 30 oct, ver arriba.)

**Y cuatro `_native.decide.ax_*`**, que nadie pidio. Son native axioms —el
resultado lo calcula el compilador de Lean, el kernel no revisa— y los metio
Aeneas solo, probablemente al despachar condiciones de borde sobre las
constantes grandes del estado. Los arrastran `extend_to_slot`, `set_justified`,
`process_block_header` y, por transitividad, `state_transition` y
`process_block`.

(Nota del 15 nov 2026: el conteo final es otro. Contando las doce funciones
de la STF son **9** nativos distintos, y los nueve llegan a los teoremas sobre
`state_transition` entera. A los teoremas sobre `process_attestations` llegan
7; los dos de mas son `process_block_header._native.decide.ax_3` y
`extend_to_slot_loop.body._native.decide.ax_3`.)

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
  hash que no es SSZ importaria.
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
| Nuestros sustitutos SSZ, el hash sustituto, los `--opaque`, los modelos en `Assumptions/` | el banco de pruebas | no — ellos tienen los tipos reales |

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
Lean, siete nativos de la biblioteca de tacticas de Aeneas, y diez declaraciones
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

> Nota del 15 nov 2026: el paquete se cerro el 6 nov. Los puntos de abajo son
> trabajo futuro posible, no pendientes. Lo unico pendiente es enviar el
> paquete a LambdaClass.
>
> El punto 1 entero se hizo ese mismo 15 nov, en tres tandas: ST-3 sobre
> `state_transition`, despues ST-7, despues ST-1, ST-2, ST-4 y ST-6. Cada
> tanda tiene su nota mas abajo.

Los tres hallazgos de herramienta -- que los axiomas nativos vienen de la
biblioteca de tacticas de Aeneas, que `--start-from` no trae los tipos de una
dependencia, y que un axioma de `Assumptions/` puede pisar una definicion
generada sin que nada avise -- quedan anotados aca y en el PROPOSAL, pero **no
vamos a reportarlos a Cryspen**. Decision tomada el 6 nov.

1. **Subir las dos mitades a `state_transition`**, que convierte lo que hay en
   ST-3 de verdad. Es el paso corto, y el que va a destapar la trampa del
   anclaje de genesis.

   > Nota del 15 nov 2026: **hecho.** `ST3.state_transition_no_retrocede`
   > esta demostrado, sin `sorry`. Hicieron falta tres lemas (`process_slots`
   > no toca los checkpoints, `process_block_header` conserva los slots, y la
   > finalidad a traves del loop) y la composicion por `process_block`. La
   > trampa del anclaje no mordio: ethlambda escribe solo la RAIZ de los
   > checkpoints, no el slot, asi que no hace falta la hipotesis `AnchorWF`
   > que si carga el catalogo. Como control se enuncio la version falsa
   > (igualdad del checkpoint entero) y el mismo script se detiene justo en
   > la rama del anclaje. Esta contado en PROPUESTA.md, "La transicion
   > entera".

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

   > Nota del 15 nov 2026: **ST-7 hecha, y el teorema aclaro las dos cosas.**
   >
   > Tal como la enuncia el catalogo (solo con la hipotesis de que el ultimo
   > header no sea el del genesis), ST-7 es FALSA sobre el codigo de
   > ethlambda. El test nuevo
   > `same_slot_root_swap_needs_a_justified_root_off_the_chain` lo muestra:
   > con `latest_justified = (4, X)`, `historical_block_hashes[4] != X` y el
   > slot 4 sin marcar en `justified_slots`, un voto con supermayoria al
   > target del slot 4 le cambia la raiz al justificado sin moverlo de slot.
   > La especificacion compara con `>` estricto y no lo cambiaria.
   >
   > Lo que si vale es `ST7.state_transition_adelante`: si el justificado
   > esta en el historial (`EnElHistorial`: `hist[c.slot] = c.root`), ningun
   > checkpoint cambia de raiz sin subir de slot, y esa hipotesis se conserva.
   > La prediccion de arriba era casi: el voto no se rechaza "por slot", pasa;
   > lo que salva es `attestation_data_matches_chain`, que obliga a que el
   > target tenga la raiz del historial, o sea la misma del justificado.
   >
   > Lo que costo, en orden:
   >
   > 1. `H256 == H256` se traduce a un loop de `CoreModels` sobre 32 bytes.
   >    Hubo que demostrar que si da `true` los valores son iguales
   >    (`ST7.h256_eq_true`): `loop_spec` con el invariante "el prefijo
   >    coincide".
   > 2. `attestation_data_matches_chain` e `is_valid_vote` con postcondicion
   >    de verdad. `hax_mvcgen` las atraviesa solo con lemas para `Slice::len`,
   >    el `deref` de `SszList` y un `from_residual` que diga "nunca es `Ok`".
   > 3. El loop: mismo script que el teorema 4, invariante de cuatro partes.
   >    Quedan exactamente dos objetivos, las dos ramas del `if` de la
   >    justificacion, y se cierran con dos lemas a mano.
   > 4. **`core.mem.take` era un axioma** y por eso era imposible demostrar
   >    que `process_block_header` conserva el historial: lo saca del estado
   >    con `mem::take` y de un axioma no se sabe ni que devuelve lo que
   >    recibio. Paso a definicion. Los axiomas declarados bajan de 28 a 27,
   >    `process_block_header` de 9 a 8 y `state_transition` de 24 a 23.
   > 5. Las hipotesis van DENTRO de la postcondicion (`hip -> conclusion`),
   >    no como argumento del lema; asi `hax_mvcgen` los compone.
   >
   > Control negativo: el mismo script del loop sin la hipotesis deja un solo
   > objetivo abierto, la rama `target.slot >= latest_justified.slot`.
   >
   > Lo que NO esta: que el primer bloque despues del genesis establezca
   > `EnElHistorial`, y que `latest_block_header.slot != 0` se conserve. Con
   > esos dos lemas se podria decir "vale en todo estado alcanzable".
   >
   > Un tropiezo para no repetir: al limpiar tacticas "que no se usan" segun
   > el linter saque una que si hacia falta. Dentro de un `first`, el aviso
   > "this tactic is never executed" sobre una alternativa quiere decir que
   > esa alternativa fallo antes de llegar ahi, no que el bloque sobre. El
   > build completo lo agarro.

   > Segunda nota del 15 nov 2026: **las otras de transicion de estado.**
   > Quedaron ST-1, ST-2, ST-4 y ST-6 (teorema 8 del archivo). Con ST-3 y
   > ST-7 son las siete del catalogo, contando que ST-5 (pureza) es `rfl` y
   > no se enuncia.
   >
   > - ST-1: dos enunciados, porque ethlambda y la especificacion en Python
   >   RECHAZAN cuando `slot >= target` y el modelo del catalogo no. Si
   >   acepta queda en el slot pedido; si no esta en el futuro, rechaza sin
   >   tocar el estado. Aca no hay divergencia con la especificacion.
   > - ST-2: si el header acepta, queda en el slot del bloque. Del mismo
   >   lema sale que `latest_block_header.slot != 0` se conserva, y eso se
   >   subio a `state_transition`: era uno de los dos lemas que le faltaban
   >   a ST-7. Hubo que demostrar que `process_attestations` no toca el
   >   header (otro loop con el script de siempre; cerro solo).
   > - ST-4: el paso inductivo, para cualquier estado. La razon es corta:
   >   `try_finalize` corre justo despues de justificar un target, finaliza
   >   el source, y un voto valido tiene `source.slot < target.slot`. No
   >   hizo falta tocar la lista de bits. Falta el caso base (el genesis).
   > - ST-6: corolario de ST-3 con nombre.
   >
   > Todo compilo al primer intento, con la maquinaria de ST-7: lema con
   > contenido para `is_valid_vote`, lema de `try_finalize`, dos lemas de
   > cierre para las dos ramas del `if`, e hipotesis dentro de la
   > postcondicion. Control negativo de ST-4: con el lema trivial de
   > `is_valid_vote` quedan abiertos justo los dos casos en que la finalidad
   > pasa al source.
   >
   > Lo que sigue faltando para "vale en todo estado alcanzable": que el
   > primer bloque despues del genesis establezca `EnElHistorial` (ST-7) y
   > el caso base de ST-4. Las dos piden construir el estado del genesis,
   > que el crate no tiene.

   > Nota del 17 nov 2026: **los cuatro teoremas originales, sobre la ventana
   > de slots justificados** (teorema 9 del archivo, namespace `JS`). Son los
   > del analisis del 22 oct, sobre `justified_slots_ops`, y nunca se habian
   > hecho: todo lo anterior esquivo la lista de bits.
   >
   > Quedaron los cuatro, mas fuertes que como estaban enunciados:
   > `extend_to_slot` solo agrega ceros al final; `shift_window` es
   > `drop delta`; despues de `set_justified(s)`, `is_slot_justified(s)`
   > DEVUELVE `Ok(true)`; y el compuesto, para cualquier respuesta `b` y no
   > solo para `true`.
   >
   > Lo que costo, en orden:
   >
   > 1. La capa base: `get`, `set`, `len`, `with_length` como ECUACIONES
   >    (`get s i = ok (s.bits[i]?)`). Hay que desarmar los modelos de `core`
   >    nivel por nivel con `#print` y `simp [...]`: `Vec::index` ->
   >    `Slice::index` -> `SliceIndex::get` -> `slice_index` ->
   >    `Slice.index_usize`. Cuatro corridas para cuatro lemas.
   > 2. `vec![false; n]` es `seq_create`, que hace `List.mapM clone`. Hizo
   >    falta `mapM_ok` (mapear `ok` devuelve la lista) por induccion.
   > 3. `relative_index`: `checked_sub` es `uoverflowing_sub`, que resta
   >    vectores de bits. Lema `sub_val` con `BitVec.toNat_sub_of_le`, y
   >    despues tres casos (`t < f`, `t = f`, `t > f`).
   > 4. Los invariantes `Copiado` y `Desplazado` sobre `List Bool`, con sus
   >    lemas de paso en Lean puro. Compilaron todos al primer intento, y eso
   >    hizo que los loops salieran casi solos: `hax_mvcgen` deja tres
   >    objetivos por loop y cada uno es un lema de paso.
   > 5. Para las funciones enteras, otra vez la hipotesis dentro de la
   >    postcondicion.
   >
   > Dos cosas que aparecieron:
   >
   > - El `as usize` de `relative_index`. El modelo de Aeneas no fija el
   >   ancho de `usize` (`System.Platform.numBits`), asi que el compuesto
   >   necesita la hipotesis de que la distancia entra. En 32 bits truncaria.
   > - Las funciones traducidas son `noncomputable`, asi que no se pueden
   >   correr con `#eval`. Quise usarlo para mostrar un caso concreto y no se
   >   puede. No confirme el motivo exacto; dependen del axioma de `fmt` que
   >   usa `.expect()`, que alcanza para explicarlo.
   >
   > Lo que sigue: los `.expect()` y el `.unwrap()` de este modulo. Con las
   > ecuaciones de la capa base ya se puede atacar la ausencia de panico de
   > `set_justified`, `extend_to_slot` y `shift_window`, que pide invariantes
   > del estado (que la ventana cubre el slot, que no pasa de la capacidad).

   > Segunda nota del 17 nov 2026: **la ventana no entra en panico** (teorema
   > 10, namespace `NP`). Primer resultado de ausencia de panico del paquete.
   >
   > - `is_slot_justified` devuelve siempre.
   > - `set_justified` entra en panico EXACTAMENTE cuando `is_slot_justified`
   >   responde `Err` (dos lemas, uno por lado; el segundo demuestra
   >   `= fail Error.panic`).
   > - `extend_to_slot` devuelve si `t - f <= 262144`; `shift_window` si la
   >   lista no pasa de 262144.
   > - En el punto de uso: tras un voto que `is_valid_vote` acepta,
   >   `set_justified` sobre su target devuelve. O sea que el
   >   `expect("index out of bounds")` no se dispara en `process_attestations`.
   > - El teorema 4 queda sin condicional de panico.
   >
   > Como se hace, que es lo reutilizable:
   >
   > 1. Postcondicion `⇓` en vez de `PostCond.mayThrow`. Con eso `hax_mvcgen`
   >    deja un objetivo por cada punto donde el codigo podria abortar: la
   >    precondicion del `expect`, la rama `h_fail` de cada suma.
   > 2. Los lemas `@[spec]` tambien tienen que ser totales. Salen de las
   >    ecuaciones de la capa base con el puente `triple_total_of`.
   > 3. `expect` y `unwrap` llevan PRECONDICION: `⌜∃ t, r = Ok t⌝`. La terna
   >    se demuestra por casos sobre `r` y `simp [Triple, WP.wp, ...]`.
   > 4. `loop_spec` con medida de verdad:
   >    `termination := fun x => x.1.end.val - x.1.start.val`, y en cada rama
   >    `cont` se cierra con `Or.inl (by omega)`.
   > 5. Los lemas con hipotesis SI sirven como `@[spec]`: `hax_mvcgen` deja
   >    cada hipotesis como un objetivo aparte. Para ternas totales no vale
   >    el truco de meter la hipotesis en la postcondicion.
   > 6. `of_triple_total` convierte la terna en `∃ v, x = ok v ∧ P v`.
   >
   > Todo compilo en seis corridas. Control negativo: `shift_window` sin la
   > hipotesis de capacidad se detiene en el `expect` de `with_length`.
   >
   > Lo que sigue: las hipotesis de capacidad como invariantes del estado
   > (que `justified_slots` nunca pase de 262144), y la ausencia de panico
   > del resto de la STF, funcion por funcion, con esta misma receta.

   > Tercera nota del 17 nov 2026: **el comentario de `is_valid_vote`**
   > (teorema 11, namespace `VC`). El codigo de ethlambda dice que despues de
   > `process_block_header` la ventana cubre hasta `block.slot - 1`, y que
   > por eso se rechaza "exactamente" el voto con slot igual o posterior al
   > del bloque. Son dos teoremas:
   >
   > - `tras_header_cubre`: sobre todo slot anterior al del bloque,
   >   `is_slot_justified` responde `Ok`. Vale para cualquier estado.
   > - `tras_header_rechaza`: del slot del bloque en adelante responde `Err`.
   >   NO vale para cualquier estado: pide que la ventana de entrada no
   >   llegara ya mas alla del slot anterior al bloque (`hlen`). El "exactly"
   >   del comentario depende de un invariante que el comentario no dice.
   >
   > Lo que hizo falta: el largo exacto de `extend_to_slot` (otro loop, con
   > el invariante "el largo no cambia") y un lema "eco" para el header, que
   > devuelve como postcondicion la propia llamada a `extend_to_slot`.
   >
   > Tropiezo: `omega` no cierra objetivos con un `max` en el contexto si el
   > `max` tiene adentro una suma de naturales coercionados. Hay que sacar
   > el hecho limpio antes (`Nat.le_max_right`, `Nat.max_eq_right`) y no
   > dejar el `max` a la vista.
   >
   > Control negativo: sin `hlen` la demostracion falla en los dos lugares
   > donde se usa.
   >
   > Lo que sigue: que `hlen` se conserve a lo largo de la transicion. Es el
   > invariante "la ventana llega justo hasta el ultimo slot materializado",
   > y de el salen tambien las hipotesis de capacidad del teorema 10.

   > Cuarta nota del 17 nov 2026: **ese invariante, hecho** (teorema 12,
   > namespace `VI`). `VentanaNoPasa` (largo + finalizado <= slot del header)
   > se conserva por `state_transition`, y tras un bloque aceptado queda
   > `VentanaJusta` (largo + finalizado + 1 = slot del header).
   >
   > La idea: `try_finalize` mueve la finalidad `source.slot - finalizado` y
   > `shift_window` acorta la ventana lo mismo, asi que la suma no cambia. Lo
   > que hay que saber es que el source esta dentro de la ventana, y sale de
   > `is_valid_vote` (lema `is_valid_vote_fuente_spec`).
   >
   > Dos cosas de tecnica:
   >
   > - Un lema `@[spec]` no puede tener una variable libre que no aparezca en
   >   el programa (aca, la cota `L`). `mvcgen` no la puede instanciar. Hay
   >   que reformular sin ella: en vez de "si la suma + 1 es L, sigue siendo
   >   L", "la suma no cambia".
   > - TRAMPA SERIA. Dentro de un `first | exact ⟨..., fun h => by cases h⟩
   >   | ...`, si el `by` de adentro deja objetivos sin resolver NO falla la
   >   alternativa: Lean registra el error, admite el objetivo con `sorry` y
   >   da por buena esa rama. Lo mismo con `obtain ... := (by assumption : ..)`
   >   cuando el `assumption` falla. Se vio porque `#print axioms` mostro
   >   `sorryAx`. Regla: nada de `by` que pueda fallar adentro de un termino
   >   en una alternativa de `first`; cada caso en su vineta, o el paso que
   >   puede fallar a nivel de tactica (`refine ...; cases h`).
   >   Los builds anteriores no tienen este problema: no hay ningun "sorry"
   >   en la salida, y Lean avisa por cada declaracion que lo use.
   >
   > Hipotesis nueva en todo el teorema: `h64`, que `usize` es de 64 bits.
   > Aparece tres veces el `as usize`.
   >
   > Control negativo: el loop con el lema trivial de `is_valid_vote` cierra
   > los casos en que no se finaliza y deja abiertos los dos en que si.
   >
   > Lo que sigue (el 16 de la lista): acotar el slot del header por el tope
   > de `historical_block_hashes`, para que la ventana no pase de 262144.

   > Quinta nota del 17 nov 2026: **el 16, hecho** (teorema 13, namespace
   > `HC`). Invariante `HistorialAcotado`: un hash por slot, y el slot del
   > header <= 262144. Se conserva por `state_transition`.
   >
   > Consecuencia que conviene tener escrita: `process_block_header` no
   > acepta ningun bloque con slot mayor que 262144
   > (`header_acepta_slot_acotado`). No es divergencia: el tope es `2**18`
   > en leanSpec y en ethlambda (verificado contra el `main` de los dos). El
   > `new_total` que el codigo compara contra `HISTORICAL_ROOTS_LIMIT` es
   > exactamente `block.slot`.
   >
   > Con este invariante y el del teorema 12, la ventana no pasa de 262144
   > bits y `shift_window` sobre ella devuelve
   > (`shift_window_no_falla`): queda descargada la hipotesis de capacidad
   > del teorema 10.
   >
   > Tecnica: para nombrar hipotesis sin nombre con
   > `(by assumption : patron)`, el patron necesita los TIPOS cuando hay
   > notacion de campo (`l.items` no resuelve si no se sabe el tipo de `l`).
   > Escribir `ssz.SszList.items (Prod.fst (_ : A × B))` en vez de
   > `(Prod.fst _).items`. Y no mezclar con `subst_vars`: reordena las
   > igualdades y rompe los patrones.
   >
   > Control negativo: sin "un hash por slot" la cota del slot falla en la
   > cuenta final.
   >
   > Lo que sigue: la ausencia de panico de las doce funciones de `stf.rs`.
   > Para `try_finalize` y `process_block_header` ya estan las piezas de la
   > ventana; falta el resto de cada una.

   > Sexta nota del 17 nov 2026: **las cinco chicas no entran en panico**
   > (teorema 14, namespace `NP2`): `current_proposer`, `is_proposer`,
   > `slot_is_justifiable_after`, `attestation_data_matches_chain` e
   > `is_valid_vote`. Sin hipotesis, para toda entrada.
   >
   > - `core.bool.Bool.then` paso de axioma a definicion: `current_proposer`
   >   es `(n > 0).then(|| slot % n)`. Declaraciones sin contenido: 27 -> 26.
   >   `process_block_header` baja de 8 a 7 axiomas y `state_transition` de
   >   23 a 22. Los 42 resultados anteriores siguieron compilando sin tocar.
   > - `slot_is_justifiable_after`: el unico panico posible era el
   >   `isqrt().pow(2)`. `core.num.U64.pow` es `UScalar.tryMk (x ^ n)`, que
   >   falla si no entra. Lema `pow_total` con precondicion, y la
   >   precondicion sale de `Nat.sqrt_le'` (OJO: esta en forma `sqrt n ^ 2`,
   >   no `sqrt n * sqrt n`).
   > - Los closures de `and_then` e `is_some_and`: se despliegan con
   >   `simp only [...]` ANTES de `hax_mvcgen`, con el nombre de la instancia
   >   y el de su `call_once`.
   > - La igualdad de `H256`, ahora total: `loop_spec` con medida
   >   `32 - i`. Salen las ramas `h_fail` de los dos `array_index` y de
   >   `i + 1`, y se cierran con `exfalso; scalar_tac`.
   > - `attestation_data_matches_chain` cerro SOLA: `hax_mvcgen` descargo los
   >   tres indices con las guardas que estan en el codigo.
   > - `is_valid_vote`: `branch` y `from_residual` con contenido. Si `branch`
   >   corta, lleva un `Err`; con eso `from_residual` devuelve.
   > - `x % n` de Aeneas: `WP.spec_imp_exists (UScalar.rem_spec x h)` da
   >   `∃ r, x % n = ok r ∧ r.val = x.val % n.val`.
   >
   > Los cinco dependen SOLO de los tres axiomas de Lean. Ojo al contarlo:
   > siguen apoyandose en `bool::then` e `isqrt`, que son definiciones
   > nuestras y no aparecen en `#print axioms`.
   >
   > Control negativo: con un lema de `isqrt` que no dice cuanto vale,
   > quedan abiertos los dos cuadrados.
   >
   > Lo que sigue: las otras siete de `stf.rs`. `process_slots` deberia ser
   > la mas corta (una resta guardada y el hash).

   > Septima nota del 17 nov 2026: **`process_slots` y
   > `process_block_header` no entran en panico** (teorema 15, namespace
   > `NP3`). Son las dos que hashean.
   >
   > - Decision de Eduardo: NO probar que el hash sustituto termina (son mas
   >   de diez loops y no diria nada del hash real). "El hash devuelve" va
   >   como hipotesis escrita, una por llamada. Se usa con `devuelve_spec`:
   >   de `∃ r, x = ok r` saca la terna total, y como lema `@[spec]` con
   >   hipotesis `hax_mvcgen` deja la hipotesis como meta lateral.
   > - `process_slots`: sin mas hipotesis. Quedaron dos `h_fail`, los dos
   >   de `target_slot - state.slot`, y cierran con `exfalso; scalar_tac`.
   > - `process_block_header`: pide `usize` de 64 bits y que el historial
   >   tenga tantas entradas como el slot del ultimo header (la primera
   >   mitad de `HC.HistorialAcotado`).
   > - Lemas totales NUMERICOS, no estructurales: `take` da el largo, `push`
   >   da `largo + 1`, el loop da el largo final, `try_from` con la
   >   hipotesis "entra" da `∃ t, r = Ok t`. Con eso las 19 metas que deja
   >   `hax_mvcgen` son aritmetica pura y cierran todas con
   >   `first | scalar_tac | (exfalso; scalar_tac) | simp_all`, despues de
   >   `subst_vars` y `simp only [cast_usize_64 h64] at *`. Sin `by`
   >   anidados, por la trampa del `sorry`.
   > - El `expect("pre-validated: ...")` de ustedes queda verificado: el
   >   `try_from` da `Ok` porque el vector mide `new_total`.
   > - `Vec::push` total pide `largo < Usize.max`.
   >
   > **La precondicion.** `new_total = current_len + 1 + num_empty_slots` se
   > calcula ANTES del chequeo contra `HISTORICAL_ROOTS_LIMIT`. Con el
   > historial alineado vale `block.slot`. Sin esa hipotesis la suma puede
   > desbordar. No es un estado alcanzable segun el teorema 13, y no se
   > presenta como bug: es la condicion bajo la que vale el resultado.
   >
   > Control negativo: sin la hipotesis del largo quedan abiertas cinco
   > metas. Las dos sumas en cada una de las dos ramas (genesis y no
   > genesis) y la capacidad de `extend_to_slot` en la rama no genesis. En
   > la rama del genesis el slot del header es cero y la capacidad sale
   > sola del chequeo del limite.
   >
   > Axiomas: `process_slots_devuelve` 3 (los de Lean);
   > `process_block_header_devuelve` 7 (3 de Lean, 3 nativos y el `fmt` de
   > `FueraDeCapacidad`).
   >
   > Lo que sigue: las otras cinco de `stf.rs`. `try_finalize` y
   > `process_attestations` usan `HashMap.get/insert/new`, que siguen
   > siendo axiomas sin contenido: hay que decidir si se modelan o si se
   > toma "devuelven" como hipotesis, igual que con el hash.

   > Octava nota del 17 nov 2026: **`serialize_justifications` no entra en
   > panico** (teorema 16, namespace `NP4`), y de paso `claves_ordenadas`.
   >
   > - SORPRESA: yo habia dicho que esta no pedia ninguna decision previa, y
   >   no era asi. El ordenamiento compara `H256` con `<`, que baja a
   >   `core.Array.Insts.CoreCmpOrd.cmp`, una de las 26 declaraciones sin
   >   contenido. No se puede probar que devuelve. Se tomo como hipotesis
   >   escrita (`hcmp : ∀ x y, ∃ o, cmp x y = ok o`), igual que el hash. La
   >   alternativa, modelar la comparacion lexicografica, queda abierta:
   >   seria la cuarta afirmacion de modelado y permitiria probar que
   >   ademas ORDENA.
   > - Hipotesis del resultado: `hcmp`; a lo sumo 262144 raices; a lo sumo
   >   4096 validadores; ninguna lista de votos mas larga que
   >   `validator_count`. Cada `expect` de la funcion queda atado a una.
   > - Lemas base nuevos, con ecuacion y con terna total: `Vec::deref`,
   >   `Slice::get`, `deref_mut`, `Slice::get_mut` (solo el largo),
   >   `Vec::len`, `Vec::new`, `Option::is_none`.
   > - `burbujear` (el loop interno de la insercion): medida de terminacion
   >   `2 * j + seguir`. Si intercambia baja `j`; si no, apaga `seguir`.
   > - `posicion` (busqueda lineal): medida `largo - i`.
   > - Un lema `@[spec]` NO puede tener una variable libre que no este en
   >   el programa, tampoco en una hipotesis. `largo_votos` con cota `c` no
   >   servia; quedo como "devuelve cero, o el largo de alguna lista de
   >   votos". Y `volcar_votos` pide "cada lista, puesta a partir de
   >   `base`, entra en el destino", sin nombrar la cota.
   > - Las cuentas con producto (`base = i * vc`, destino de `n * vc` bits):
   >   un lema `tramo : a < b → a * c + c ≤ b * c` y despues `omega`, que
   >   trata `i * vc` como atomo.
   > - Cerrar con `first | (exfalso; scalar_tac) | (refine ...; scalar_tac)`
   >   sin `by` anidados.
   >
   > Controles negativos: sin la hipotesis de los votos aparece la meta
   > `largo ≤ validator_count` sin cerrar; sin la cota de validadores
   > fallan la capacidad del bitlist y el producto.
   >
   > Axiomas: `claves_ordenadas_devuelve` 4 (3 de Lean y la comparacion de
   > arrays); `serialize_justifications_devuelve` 8 (esos 4, 3 nativos y el
   > `fmt` de `FueraDeCapacidad`).
   >
   > Lo que sigue: `try_finalize`, `process_attestations`, `process_block`
   > y `state_transition`. Para juntar con `process_attestations` falta
   > probar que el mapa que arma cumple las hipotesis de arriba.

   > Novena nota del 17 nov 2026: **el mapa de votos cumple la hipotesis de
   > las listas** (teorema 17, namespace `MV`). Tres resultados:
   > `construir_mapa_acotado`, `loop_conserva_acotado` y
   > `serialize_tras_attestations_devuelve`.
   >
   > - De las tres hipotesis de `serialize_justifications` que hablan de
   >   datos, se descarga UNA: ninguna lista de votos mas larga que
   >   `validator_count`. Las otras dos quedan pedidas. La de 4096
   >   validadores, porque nuestro `SszList` no lleva el limite como
   >   invariante. La de 262144 raices es la dificil: el loop agrega hasta
   >   una raiz por attestation, y la cota real pide probar que las raices
   >   del mapa son distintas y estan en el historial.
   > - `VotosAcotados c m := ∀ v ∈ m.valores, largo v ≤ c`. Con `≤` y no
   >   con `=`: `votos(i)` devuelve una lista VACIA si no hay entrada `i`,
   >   y con `=` eso rompe el invariante en `sin` y en `filtrado`.
   > - Forma de los lemas: "para toda cota `c`, si valia antes vale
   >   despues". Asi no queda una variable libre en el `@[spec]`.
   > - Son parciales (`PostCond.mayThrow`), con `termination := fun _ => 0`
   >   y `Or.inr` para la divergencia, como los loops del teorema 6.
   > - `Vec::clone` esta modelado como un LOOP sobre un iterador de slice
   >   (`clone_loop`). Hizo falta su lema: el iterador pierde un elemento
   >   por vuelta y el destino gana uno, asi que la copia no es mas larga.
   > - `Slice::get_mut` con contenido: lo que se lee, que el largo no
   >   cambia, y que todo elemento de lo que se escribe de vuelta ya
   >   estaba o es el que se escribio. Con eso sale `votar`.
   > - Un loop con el iterador sin desarmar NO avanza en `hax_mvcgen`: hay
   >   que hacer `obtain ⟨desde, hasta⟩ := iter` antes.
   > - Los lemas totales (`⇓`) del teorema 16 se pueden usar adentro de
   >   pruebas parciales sin tocarlos.
   > - Las 28 metas del loop de attestations son cadenas de implicaciones
   >   y cierran todas con `grind`.
   >
   > Control negativo: con `votos_vacios` sin decir cuanto mide lo que
   > devuelve, `grind` falla en el loop.
   >
   > Axiomas: `construir_mapa_acotado` 3; `loop_conserva_acotado` 14 (3 de
   > Lean, 4 nativos, 7 declaraciones); `serialize_tras_attestations_devuelve`
   > 18 (3, 7 y 8).
   >
   > Lo que sigue: la cota de raices (el invariante hondo), o
   > `try_finalize` con el `HashMap`.

   > Decima nota del 17 nov 2026: **`try_finalize` no entra en panico**
   > (teorema 18, namespace `NP5`). Tres resultados: `filtrado_devuelve`,
   > `try_finalize_devuelve` y `try_finalize_devuelve_inv`.
   >
   > - Hipotesis: source anterior al target (cierra el `source.slot + 1`
   >   que estaba en los limites desde el 5 nov); ventana ≤ 262144 bits
   >   (o los dos invariantes, en la version `_inv`); y que
   >   `slot_de_raiz` devuelva, porque `HashMap::get` es un axioma sin
   >   contenido. Decision: hipotesis escrita, igual que el hash.
   > - El avance de un rango de `u64` NO viene en la biblioteca de hax
   >   (trae `IteratorRange_next_spec` para `i32` y `_usize`). Se copio la
   >   forma del de `usize`. Diferencia: `forward_checked` de `u64`
   >   convierte el paso `1#usize` con `try_from`, que compara contra
   >   `U64.MAX` y `U64.MIN` casteados a `usize`. Tres lemas chicos:
   >   `u64_max_en_usize` (no es cero; se parte en
   >   `System.Platform.numBits_eq`), `u64_min_en_usize` y `uno_en_u64`.
   >   OJO: no dejarlos como `have` antes del `simp_all`, que los reescribe
   >   y los deja inservibles; meterlos DESPUES del `mvcgen`.
   > - `Vec::clone` total: medida de terminacion, el largo del iterador.
   >   Invariante `copiado + pendiente ≤ Usize.max`. `hax_mvcgen`
   >   despliega solo el `seq_push` y deja la rama del panico como meta.
   > - `filtrado` total: invariante "claves y valores copiados ≤ lo
   >   recorrido", para que los dos `push` tengan lugar.
   > - La funcion entera cierra con `all_goals scalar_tac`: tres cuentas.
   >
   > Controles negativos: sin `horden` queda `U64.max < source.slot + 1`;
   > sin `hcap` queda la precondicion de `shift_window`.
   >
   > Axiomas: `try_finalize_devuelve` y `_inv` 13 (3 de Lean, 3 nativos, 7
   > declaraciones); `filtrado_devuelve` 3.
   >
   > INCIDENTE: a mitad de sesion el motor de Docker se colgo (error 500 y
   > despues sin respuesta, con la VM reiniciada sola). Se arreglo cerrando
   > Docker Desktop del todo y abriendolo de nuevo. Los volumenes
   > `hax-elan`, `hax-cargo` y `hax-cache` y la imagen no se perdieron.
   >
   > Lo que sigue: `process_attestations`, que es el loop grande, y
   > despues `process_block` y `state_transition`.

   > Nota del 18 nov 2026: **las piezas de `process_attestations` no entran
   > en panico** (teorema 19, namespace `NP6`). Es la etapa A de dos: las
   > funciones auxiliares sueltas. La etapa B es el loop y la funcion
   > entera. Diez resultados con nombre, sobre unas dieciocho funciones.
   >
   > - Sin hipotesis: `contar_datos_distintos`, `hay_raiz_cero`,
   >   `primer_bit_fuera_de_rango`, `votos_vacios`, `marcar_votos`,
   >   `cuenta_votos`, `sin`.
   > - Con hipotesis: `poner_si_falta` (lugar para una entrada mas),
   >   `construir_mapa_de_votos` (`raices * validator_count` no desborda),
   >   `construir_root_to_slot` (`finalizado + 1` no desborda y el
   >   `HashMap` devuelve).
   > - `HashMapDevuelve` es una estructura con las tres hipotesis del
   >   `HashMap` (`new`, `get` para TODO mapa, `insert` para todo mapa).
   >   El `get` de `try_finalize` era para un mapa fijo; aca cambia en
   >   cada vuelta.
   > - `Vec[i]` (`CoreOpsIndexIndex.index`) no tenia lema: hay que
   >   desplegarlo en DOS `simp`, como en `JS.get_eq`. Con uno solo no
   >   llega al `get` de adentro.
   > - Cerrar loops que cuentan: `refine ⟨⟨trivial, ?_, ?_⟩, Or.inl ?_⟩ <;>
   >   scalar_tac`, NO `omega`. `omega` no sabe que `↑1#usize` es 1 y la
   >   alternativa cae al `exfalso`, que falla con un mensaje engañoso.
   > - `votos_del_segmento` necesita ADEMAS `i < Usize.max`: con
   >   `validator_count = 0` el producto no acota a `i + 1`.
   > - Un comentario de documentacion (`/-- ... -/`) justo antes de
   >   `section` es un error de sintaxis.
   > - El `Default` de `AttestationData` (arrays de 32 bytes incluidos)
   >   cerro solo con `hax_mvcgen`.
   > - Las cuentas con producto: `simp_all <;> omega`, despues de dejar
   >   escrito `(i + 1) * vc = i * vc + vc`.
   >
   > Controles negativos: sin el producto acotado quedan
   > `Usize.max < i * vc` y `Usize.max < (i + 1) * vc`; sin `hfin` queda
   > `U64.max < finalizado + 1`; sin lugar en las claves no cierra el
   > `push`.
   >
   > Axiomas: nueve resultados con 3 (los de Lean);
   > `construir_rts_devuelve` 11 (3 y ocho declaraciones, las del
   > `HashMap`).
   >
   > Lo que sigue: la etapa B. Hace falta un invariante del loop que junte
   > la ventana, el historial, la cota de las listas de votos y el tamano
   > del mapa.

   > Segunda nota del 18 nov 2026: **`process_attestations` no entra en
   > panico** (teorema 20, namespace `NP7`). Es la etapa B. Dos resultados:
   > `process_attestations_devuelve` y `process_attestations_devuelve_inv`.
   >
   > - Invariante del loop, mas simple de lo temido: ventana ≤ 262144;
   >   `VotosAcotados vc`; claves y valores del mapa ≤ `C + recorridas`;
   >   contador ≤ recorridas. No hizo falta llevar el historial.
   > - `total_con`: junta un lema total con uno parcial sobre la misma
   >   llamada. Asi se reusaron los lemas `VotosAcotados` del teorema 17
   >   (parciales) con los "devuelve" del 19 (totales) sin reprobar nada.
   > - Hubo que rehacer `filtrado` y `try_finalize` con postcondicion de
   >   TAMANO (el del teorema 18 decia solo "devuelve"): la ventana no
   >   crece y el mapa no crece. Forma sin variable libre: "para toda cota
   >   `c`, si claves y valores ≤ `c`, lo que devuelve tambien".
   > - `is_valid_vote_loop_spec`: de `Ok true` saca source < target y que
   >   `set_justified` devuelve sin cambiar el largo. `set_justified_dado`
   >   lleva eso como hipotesis del lema, y `hax_mvcgen` la deja como meta.
   > - El lema del loop tenia una cota `C` suelta y no servia como
   >   `@[spec]`. Version para usar: `C := max claves valores` del mapa
   >   inicial.
   > - 170 metas, ocho clases. Receta:
   >   `first | omega | exact hm.consulta rts _ | grind [VotosAcotados] |
   >   (scalar_tac_preprocess; grind [VotosAcotados]) | (exfalso; ...) |
   >   scalar_tac | (exfalso; scalar_tac)`.
   >   `scalar_tac_preprocess` existe como tactica suelta y sirve para que
   >   `grind` vea los escalares.
   > - Quedaba UNA meta: `Usize.max < 3 * votos`. Cerro al dejar escrito
   >   antes del `hax_mvcgen` que `1073741824 ≤ Usize.max` y que
   >   `(3#usize).val = 3`.
   > - `set_option maxHeartbeats 0 in` sobre el teorema del loop. Tarda
   >   unos dos minutos y medio.
   > - Para iterar: se desarrollo la funcion entera en otro archivo, con
   >   el loop como `sorry`, mientras el loop corria en segundo plano.
   >
   > Controles negativos: sin `vc ≤ 4096` quedan `Usize.max < 2 * vc` y
   > `Usize.max < 3 * votos`; sin la cota de raices quedan el producto
   > `raices * vc`, el lugar en el mapa y el limite de raices; con
   > `is_valid_vote` sin contenido quedan cuatro metas, las de
   > `set_justified` y las del orden source/target.
   >
   > Axiomas: los dos resultados 20 (3 de Lean, 7 nativos, 10
   > declaraciones).
   >
   > OJO, para no sobrevender: la hipotesis "raices + attestations ≤
   > 262144" es suficiente, no un invariante. La cota fina sigue pendiente.
   >
   > Lo que sigue: `process_block` y `state_transition`. Hay que mostrar
   > que el estado que deja `process_block_header` cumple las hipotesis de
   > `process_attestations` (validadores y raices no cambian; la ventana y
   > el historial ya estan).

   > Tercera nota del 18 nov 2026: **`process_block` y `state_transition` no
   > entran en panico** (teorema 21, namespace `NP8`). Con esto la ausencia
   > de panico cubre las doce funciones de `stf.rs`. Dos resultados:
   > `process_block_devuelve` y `state_transition_devuelve`.
   >
   > - Salio en una pasada. Las dos funciones cerraron con
   >   `first | assumption | grind | (simp_all; done)`.
   > - El pegamento: `process_slots_no_toca_registro` (ecuacional, con
   >   `bind_da_ok`, copiando `ST7.process_slots_no_toca`) y
   >   `header_registro_spec` (parcial, con la misma lista de lemas que
   >   `HC.header_historial_spec`). Dicen que validadores y raices
   >   pendientes no cambian.
   > - Lemas de cada paso para la transicion (`*_transicion_spec`):
   >   devuelve, conserva `VentanaNoPasa` y `HistorialAcotado`, y no toca
   >   el registro. Se arman a mano con `triple_total_of`, juntando el
   >   "devuelve" con los lemas de conservacion que ya estaban.
   > - `HashDevuelve`: los tres `hash_tree_root` devuelven, para todo
   >   argumento. Tiene que ser "para todo" porque el hash se aplica a
   >   estados intermedios.
   >
   > Hipotesis del resultado final: `usize` de 64 bits, `VentanaNoPasa`,
   > `HistorialAcotado`, validadores ≤ 4096, raices + attestations ≤
   > 262144, `HashDevuelve`, `HashMapDevuelve` y la comparacion de `H256`.
   >
   > Controles negativos: sin `HistorialAcotado` queda abierta esa misma
   > meta para el header; si el lema del header no dice que deja el
   > registro, quedan `validadores ≤ 4096` y `raices + attestations ≤
   > 262144` sobre el estado posterior.
   >
   > Axiomas: los dos resultados 22 (3 de Lean, 9 nativos, 10
   > declaraciones), los mismos que el `def` de `state_transition`.
   >
   > OJO, para no sobrevender: "la transicion no entra en panico" es BAJO
   > HIPOTESIS. No esta que valgan en todo estado alcanzable: falta el
   > genesis, la cota de raices es sobre las entradas, y tres hipotesis
   > (hash, `HashMap`, comparacion) no se pueden probar aca.
   >
   > Lo que sigue: modelar la comparacion de `H256` (saca una hipotesis),
   > la cota fina de raices, o el caso inicial del genesis.

   > Cuarta nota del 18 nov 2026: **`axiomas.txt` rehecho, y ahora lo arma
   > un script.** Eduardo noto dos cosas al leerlo. Una: no decia en que
   > teoremas participa cada axioma. Dos: tampoco decia con todas las
   > letras "el teorema X utiliza los axiomas A, B, C": ponia
   > `TOTAL 13 = 3 estandar + 3 nativos + 7 modelos`, dos listas sueltas, y
   > los tres de Lean ni los nombraba.
   >
   > Ahora tiene dos partes:
   >
   > - PARTE 1, un bloque `TEOREMA <nombre>` por teorema, con "utiliza N
   >   axiomas" y los tres grupos nombrados uno por uno.
   > - PARTE 2, un bloque `AXIOMA <nombre>` por axioma, con una linea que
   >   dice que es y la lista de teoremas donde aparece. Al final, los 25
   >   teoremas que solo usan axiomas de Lean.
   >
   > Lo arma `axiomas.py` a partir del log del build
   > (`python3 axiomas.py /tmp/build.log`, FUERA del contenedor, que no
   > tiene python). Antes se agregaban los bloques a mano en cada paso. El
   > script corta si encuentra `sorryAx`. Se verifico que los 71 totales
   > coinciden con los del archivo anterior.
   >
   > De paso: `bind_da_ok` usa UN solo axioma de Lean, `propext`; los otros
   > 70 usan los tres.
   >
   > OJO al leer la parte 2: "aparece en" quiere decir que la demostracion
   > pasa por codigo que nombra al axioma, no que se apoye en lo que hace.

   > Nota del 19 nov 2026: **la comparacion de arrays dejo de ser un
   > axioma.** `core.Array.Insts.CoreCmpOrd.cmp` es ahora una definicion en
   > `supuestos/FunsExternal.lean`: el orden lexicografico de los
   > elementos, con una auxiliar recursiva `cmp_listas`. Es la CUARTA
   > afirmacion de modelado (antes `isqrt`, `mem::take`, `bool::then`).
   > Declaraciones sin contenido: 26 -> 25.
   >
   > - Resultado nuevo: `NP4.h256_cmp_devuelve`, comparar dos `H256`
   >   devuelve siempre. Por induccion sobre la primera lista,
   >   generalizando la segunda; el caso de dos cabezas se parte en
   >   `compare x.val y.val`.
   > - La hipotesis `hcmp` se SACO de los enunciados, no se dejo y se
   >   descargo aparte: 13 teoremas la llevaban, entre ellos
   >   `serialize_justifications`, `process_attestations`, `process_block` y
   >   `state_transition`. `claves_ordenadas_devuelve` quedo sin ninguna
   >   hipotesis.
   > - Se hizo con un script: borrar la linea del parametro (pasando el
   >   `:` a la linea anterior cuando era el ultimo), borrar ` hcmp` de los
   >   argumentos, y borrar el `· exact hcmp _ _` que cerraba una meta que
   >   ya no aparece.
   > - Los 71 resultados anteriores recompilaron al primer intento.
   > - `as` es palabra reservada en Lean: `a :: as` no parsea.
   > - Al cambiar `FunsExternal.lean` se recompila todo lo nuestro; el
   >   build completo tarda parecido porque las dependencias estan cacheadas.
   >
   > Efecto en los axiomas: `state_transition` 22 -> 21;
   > `process_attestations` 20 -> 19; `serialize_justifications` 8 -> 7;
   > `claves_ordenadas` 4 -> 3. `core.Array.Insts.CoreCmpOrd.cmp` ya no
   > aparece en ningun teorema (estaba en 19).
   >
   > CUIDADO con el orden al tocar `teoremas/ProofObligations.lean`
   > mientras corre `regenerar.sh`: el paso 2 copia el archivo, y si se
   > edita despues el build valida la version vieja. Paso una vez; se
   > detecto con `diff -q` y se corrio de nuevo.
   >
   > Lo que esto habilita y NO esta hecho: probar que `claves_ordenadas`
   > ordena. Y lo que sigue en la misma linea: modelar el `HashMap`.
2. **Reescribir los teoremas 2 y 3 como ternas** si alguna vez hace falta: hoy
   no, los puentes los hacen usables como estan.
