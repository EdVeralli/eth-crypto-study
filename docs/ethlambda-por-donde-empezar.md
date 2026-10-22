# Aplicar Rust → Lean a ethlambda: por dónde empezar

Los cinco repos que estudiamos responden *qué se puede hacer*. Este documento responde la
otra pregunta, que es la nuestra: **qué pedazo de ethlambda sería candidato, y por qué.**

Todo lo que sigue está medido sobre un clon de solo lectura de
[`lambdaclass/ethlambda`](https://github.com/lambdaclass/ethlambda), commit `22d1a72`
(22 oct 2026). Como con los demás repos del ecosistema: **se lee, no se pushea**.

---

## 1. El límite, para no perder tiempo

La vía Rust → Lean (Charon + Aeneas, disparada por `cargo hax into lean`) **no traduce la
biblioteca estándar**. Todo lo que venga de `std` hay que modelarlo a mano, y `unsafe` y
concurrencia directamente no están soportados. El detalle está en
[`verified-zkevm.html`](verified-zkevm.html).

Consecuencia directa: **un cliente de consenso entero no pasa.** ethlambda son 145.508
líneas de Rust con actores, tokio, libp2p y RocksDB. Buscar "traducir ethlambda" es
buscar un no.

Lo que sí pasa es un **núcleo de cómputo puro y autocontenido**. Así que la pregunta
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
  entra como supuesto es chico y obviamente correcto, no un `HashMap` con orden de
  iteración indefinido.
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
- **En contra**: usa `HashMap`, que es `std`. Habría que modelarlo, **y el orden de
  iteración de un `HashMap` es precisamente donde vive ese bug**. Eso lo hace más caro y,
  a la vez, más interesante.

> **Observación al leer el código, sin demostrar:** acá parece que lo resolvieron bien. El
> desempate es `max_by_key(|root| (peso, *root))`, y como los roots son únicos no hay
> empates posibles, así que el máximo no depende del orden. **Convertir esa observación en
> demostración sería el teorema.**

---

## 5. El plan de una semana

1. **Instalar la cadena** y traducir el crate con `cargo hax into lean`.
2. **Mirar qué quedó en la plantilla** (`FunsExternal_Template.lean`): eso dice el costo
   real antes de escribir un solo teorema.
3. **Modelar a mano lo que falte** — para `justified_slots_ops` debería ser sólo el
   bitlist.
4. **Enunciar y demostrar** los teoremas 1 a 4.

**Si sale**, tenés una propiedad demostrada sobre código de producción. **Si no sale**, en
una semana sabés exactamente dónde se traba y por qué — que para Pablo también es un
resultado, y bastante mejor que una opinión.

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

*Medido el 22 de octubre de 2026 sobre `lambdaclass/ethlambda` en el commit `22d1a72`,
clon de solo lectura. Los conteos de `async`/`unsafe`/locks son sobre `src/` de cada
crate, con `grep`; el `unsafe` que aparece en `state_transition` es una palabra dentro de
un comentario que cita la spec, no código.*
