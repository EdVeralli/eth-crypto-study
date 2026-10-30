# mini-stf — la STF de ethlambda en un crate solo

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

Adentro, y **los cuatro `--opaque` son imprescindibles** (por qué, más abajo):

```bash
cd /work
cargo hax into lean \
  --charon-args="--opaque 'mini_stf::stf::process_attestations' \
                 --opaque 'mini_stf::stf::serialize_justifications' \
                 --opaque '{impl core::fmt::Debug for _}' \
                 --opaque '{impl core::fmt::Display for _}'"
cd proofs/lean && lake build
```

## Los cuatro `--opaque`, y por qué cada uno

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

`ST-3` es una de las 36 proposiciones de
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

## Lo que sigue

1. **Reemplazar `isqrt`** por una definicion sobre `Nat.sqrt`, para desbloquear
   el teorema de `slot_is_justifiable_after`.
2. **Escribir el primer teorema** en `Verification/ProofObligations.lean`, que
   hax crea vacio a proposito.
3. **Recuperar las tres opacas**: reescribir sus iteradores con indices y los
   `return` de adentro del loop como variable mas `break`. Son unas 230 de las
   654 lineas, y eso **si** toca el cuerpo de ellos. Antes conviene traerse los
   437 renglones de tests del original y correrlos contra la version reescrita.
