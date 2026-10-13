# Cuadro sinóptico: los repos del ecosistema Lean 4 de Ethereum

Los cuatro repos que nos pasó Pablo. Del primero, `cryptography-specs`, tenemos copia de
estudio propia y lo recorrimos archivo por archivo; de los otros tres hicimos el análisis
leyéndolos. Todos los números están verificados sobre clones de solo lectura; la fecha de
lectura está en cada ficha.

Cada repo tiene su página HTML con el detalle; acá está el resumen para comparar de un
vistazo.

---

## 1. Dónde está cada uno

Ethereum se parte en dos mundos, y cada repo vive en uno:

```
CONSENSO  (quién propone bloques, quién vota, cómo se agregan las firmas)
├── cryptography-specs ....... la criptografía del consenso (BLS, KZG, XMSS)  ← copia propia
└── gasper-lean4 ............. el protocolo de finalidad (Casper FFG)

EJECUCIÓN  (qué pasa adentro de un bloque: el EVM, el estado, el gas)
├── leanerSTFSpec ............ la transición de estado, para zkVM stateless
└── verified-zkevm ........... el paraguas de la EF para verificar zkVM
```

Y se tocan en un solo punto: la ejecución también necesita criptografía (los
precompilados de curvas, el KZG de los blobs). Por eso `leanerSTFSpec` cita a
`cryptography-specs` como referencia: **el primer repo es la capa de abajo del segundo.**

Ojo con la palabra "lean", que juega doble en todo esto: *lean Ethereum* y *Lean
Consensus* es "lean" de liviano, por el rediseño del consenso; Lean 4 es el lenguaje.
Nombres como `leanerSTFSpec` o `leanerVM` aprovechan el doble sentido a propósito.

---

## 2. La tabla maestra

| | **cryptography-specs** | **leanerSTFSpec** | **verified-zkevm** | **gasper-lean4** |
|---|---|---|---|---|
| **Quién** | Ethereum Foundation | Alexander Hicks (lidera el proyecto zkEVM de la EF) | Ethereum Foundation (organización) | Nyx Foundation (Japón) |
| **Qué especifica** | criptografía: BLS12-381, KZG, XMSS | el EVM y la transición de estado | — (es un paraguas de 14 repos) | Casper FFG: la finalidad |
| **Capa** | consenso | ejecución | ejecución | consenso |
| **Consenso** | el nuevo (post-cuántico) | — | — | **el actual** (Beacon Chain) |
| **Archivos `.lean`** | 77 | 265 | varía por repo | 65 |
| **Líneas de Lean** | 19 995 | 41 736 | — | 11 948 |
| **Teoremas** | 357 a mano (492 con los autogenerados) | 2 318 | — | 359 |
| **Lean / Mathlib** | v4.29.1 | v4.34.0 | varía | v4.31.0 |
| **Licencia** | CC0 | Apache-2.0 o MIT | varias | MIT |
| **Estado al leerlo** | activo (XMSS completado oct 2026) | activo | activo | **quieto desde jun 2026** |

### Rigor: de qué axiomas dependen los teoremas

Esta es la parte que más nos costó entender, y la que más dice sobre cada proyecto.

**Primero, lo que es igual en los tres:** todo teorema en Lean lo revisa el *kernel*, el
núcleo chico del lenguaje que acepta o rechaza cada paso. Eso pasa siempre, por el solo
hecho de usar Lean; no distingue a nadie.

**Lo que cambia es de qué se permite depender.** Un teorema puede apoyarse en axiomas:
afirmaciones que se aceptan sin demostrar. Lean trae tres estándar, y además hay una vía
de escape — `native_decide` y `bv_decide` — donde el kernel, en vez de revisar el paso,
deja que **el compilador de Lean calcule el resultado en ese momento** y lo acepta sin
mirarlo. Eso deja un axioma extra registrado en el teorema, y a eso le decimos
*native axiom*.

Entonces la pregunta útil es: ¿qué axiomas se permiten, y hay **alguien que lo controle**?

| Repo | Axiomas permitidos | ¿Quién controla que se cumpla? |
|---|---|---|
| **cryptography-specs** | `propext`, `Quot.sound`, `Classical.choice` **+ 10 teoremas con *native axioms*** | **nadie** |
| **leanerSTFSpec** | `propext`, `Quot.sound`, `Classical.choice` | **un programa, en cada cambio que alguien sube** |
| **gasper-lean4** | **`propext` y `Quot.sound`. Nada más.** | **un programa, cada vez que se compila** |

Qué quiere decir cada caso:

- **`cryptography-specs`: nadie.** No hay una regla escrita que diga qué axiomas se
  permiten, ni un programa que la controle. Por eso los 10 teoremas con *native axioms*
  estaban ahí sin que nadie los hubiera contado: los encontramos nosotros, escribiendo
  `docs/native_axioms.lean`, un script que recorre los teoremas y pregunta de qué depende
  cada uno.

- **`leanerSTFSpec`: un programa propio, llamado `check-decls`.** Recorre todos los
  teoremas del repo y, si alguno depende de un axioma que no está en la lista permitida,
  **el build falla**. Corre automáticamente en cada cambio que alguien sube, y no existe
  manera de pedir una excepción, ni siquiera "por esta vez" (*"There is no exemption
  mechanism"*, dice el reglamento).

  **Ojo, no revalida las demostraciones.** El kernel y `check-decls` responden preguntas
  distintas: el kernel, *¿esta demostración es correcta?*; `check-decls`, *¿de qué depende,
  y está permitido?*. Lean ya deja registrado de qué axiomas depende cada teorema;
  `check-decls` lee esa lista y la compara. No recalcula ni un paso. (Sí revisa el
  resultado compilado y no el texto fuente, así nadie puede disfrazar una violación
  escribiéndola de otra forma.)

  Donde sí agrega validaciones propias es en cosas que **al kernel le dan igual**:
  prohíbe `@[csimp]`, `@[extern]`, `unsafe`, `partial` y `opaque`. El reglamento explica
  la diferencia: esas no son inseguras *lógicamente*, pero rompen la **correspondencia
  entre lo demostrado y lo ejecutado**. `@[csimp]`, por ejemplo, permite decirle al
  compilador "cuando corras, usá esta otra función más rápida en vez de la que escribí":
  el teorema sigue siendo cierto sobre la función original, pero ya no es esa la que
  corre.

- **`gasper-lean4`: un comando propio que corre al compilar** y escupe un informe de todo
  el proyecto. El de este commit dice, textual:

  ```text
  Axiom Profile:
    ✓ sorryAx: not used                                 (ninguna demostración incompleta)
    ✓ native compute (trustCompiler / ._native.*): not used   (ningún native axiom)
    ✓ Classical.choice: not used                        (ni siquiera el axioma de elección)
  ```

**En resumen:** en los tres, el kernel revisa las demostraciones. La diferencia es que en
dos hay además un **guardia automático** que impide que se cuele un axioma de más, y en el
tercero no — por eso ahí hay 10 teoremas con *native axioms*, uno de ellos central
(`uncompress_compress`), que nadie había contado hasta que los contamos nosotros.

`gasper-lean4` llega al extremo: eliminó hasta el axioma de elección, y el premio es que
las definiciones se vuelven **calculables** — la versión ejecutable sale casi gratis con
`decide`, y el teorema puente entre las dos se demuestra en una línea.

### Por qué los axiomas importan tanto

Porque la lista de axiomas es, literalmente, **la lista de cosas que hay que creer sin
demostración** para que el teorema valga. Todo lo demás lo revisó el kernel.

**Los tres estándar alcanzan para toda la matemática.** Mathlib entera —cientos de miles
de teoremas de álgebra, análisis y teoría de números— está construida sobre esos tres y
nada más. Toda la matemática que usan estos repos (campos finitos, curvas elípticas,
polinomios) sale de ahí. No hay nada que falte *por culpa de los axiomas*.

**¿Y qué sería un axioma que no vale?** Lo primero es saber que Lean **no verifica que un
axioma sea verdad**: lo acepta por definición, ése es el trato. Declarar uno es gratis y no
produce ningún error. La disciplina está afuera del lenguaje. Un axioma se vuelve inválido por
dos motivos distintos:

- **Porque es falso.** De una falsedad se deduce cualquier cosa, incluso su propia negación.
  No hace falta que el error salte a la vista: alcanza con un enunciado que parezca razonable y
  no lo sea. A partir de ahí todo lo que se apoye en él sigue compilando perfecto y ya no
  significa nada.
- **Porque es verdadero, pero habla del problema.** Éste es el peligroso en la práctica. Si
  alguien declarara como axioma "la verificación de firmas BLS es correcta", todo lo que se
  construya encima compilaría y diría `theorem`, sin que nadie hubiera demostrado justo lo único
  que importaba: se pidió prestado el enunciado en lugar de probarlo.

**Qué caracteriza entonces a uno válido:** que sea un enunciado **general de lógica, que no sepa
nada del problema que estás resolviendo**, y que exista una demostración —hecha fuera de Lean, en
teoría de conjuntos— de que agregarlo no introduce contradicciones. Los tres estándar cumplen las
dos cosas: no saben nada de BLS, de hashes ni de Ethereum, y está probado que son seguros de usar.

**Quién lo detecta:** adentro de Lean, nadie. El kernel acepta cualquier axioma sin chistar — eso
*es* un axioma. Lo único que lo delata es la lista de axiomas del teorema, y alguien que la mire y
decida si esa lista es aceptable. Por eso importa tanto quién controla esa lista, que es lo que
compara la tabla de arriba: en `leanerSTFSpec` y en `gasper-lean4` la revisa un programa en cada
cambio; en `cryptography-specs`, nadie.

Entonces, cuando algo no está demostrado, es por una de estas tres razones, que conviene
no mezclar:

| Caso | Ejemplo | ¿Se puede arreglar? |
|---|---|---|
| **Es una conjetura** | que SHA-256 no tenga colisiones, que el logaritmo discreto sea difícil | **no, nunca**: es el supuesto sobre el que se apoya toda la criptografía. Se declara como axioma aparte y explícito |
| **Falta trabajo** | `ConcreteBlsLaws` | **sí**: son leyes matemáticas, demostrables con los tres axiomas. Nadie las demostró todavía |
| **Se usó un atajo** | los 10 teoremas con *native axioms* | **sí**: son evitables. Upstream abrió el issue #28 para sacar dos de ellos, y en XMSS usaron `decide +kernel` (el mismo cálculo, hecho por el kernel) |

**Y el detalle que más importa:** la lista de axiomas **no muestra todo**. Un teorema puede
valer "si se cumple tal cosa", y esa hipótesis no aparece como axioma. Es exactamente el
caso de `ConcreteBlsLaws`: los teoremas de la ceremonia de KZG valen *si* el pairing
programado cumple tres leyes que nadie demostró, y `#print axioms` no lo dice.

Así que la base real de un teorema tiene tres pisos, y solo el primero se ve mirando
axiomas:

```
1. Axiomas de Lean ............ los 3 estándar (+ native axioms donde se usó el atajo)
2. Supuestos criptográficos ... hashes sin colisiones, log discreto difícil
3. Hipótesis sin demostrar .... ConcreteBlsLaws  ← este NO aparece en #print axioms
```

Por eso en el mapa completo separamos "Matiz 1" (la hipótesis) de "Matiz 2" (los native
axioms): el segundo es el visible; el primero es el grave.

### Dónde se usa Lean (las tres preguntas)

| Repo | ¿Se compila el Lean? | ¿Se traduce código entre Lean y otro lenguaje? | ¿Hay Lean en el entorno de ejecución? |
|---|---|---|---|
| **cryptography-specs** | **sí** → `_native.so` de 8,8 MB | no | **invocable** (33 `@[export]`), pero **nadie lo consume** |
| **leanerSTFSpec** | sí, apuntan a 2× de revm | no | **no**: cero `@[export]`, corre como proceso aparte |
| **verified-zkevm** | no (se compila el Rust) | **sí: Rust → Lean** (hax, Aeneas/Charon) | **no** |
| **gasper-lean4** | para razonar, no para servir | no | **no**, y no podría (pide `Fintype Hash`) |

**La conclusión de toda la tabla:** Lean compilado y llamable desde otro lenguaje existe
en **un solo repo de los cuatro**, `cryptography-specs`. Y todavía nadie lo usa en
producción. En producción corre Rust, C y Go.

### El hueco principal de cada uno

| Repo | Qué falta |
|---|---|
| **cryptography-specs** | `ConcreteBlsLaws`: los teoremas de la ceremonia valen *si* el pairing programado cumple tres leyes que nadie demostró |
| **leanerSTFSpec** | el teorema de refinamiento que ata la spec a las implementaciones: ni siquiera está acordado **cómo enunciarlo** |
| **verified-zkevm** | la demostración vale sobre la *traducción*, no sobre el Rust: hay que confiar en `rustc` → Charon → Aeneas |
| **gasper-lean4** | falta LMD-GHOST, o sea **la mitad de Gasper**: la que elige qué cadena seguir |

---

## 3. Ficha por repo

### `ethereum/cryptography-specs` — la criptografía (del que tenemos copia propia)

> La criptografía escrita una sola vez en Lean, de modo que la misma fuente se **ejecute**
> (se compila a C, se llama desde Python, genera los vectores) y se **demuestre**.

- **Lo verificamos corriéndolo**: `lake build` (3444 jobs), `bls_smoke.py` byte a byte
  contra `py_ecc`, y la suite de 364 vectores regenerada sin una sola diferencia (2:57:50).
- **La plomería**: 33 `@[export]`, 928 líneas de binding en C a mano, `_native.so` de
  8,8 MB enlazado contra `libleanshared`.
- **Lo que descubrimos investigando**: nadie lo consume. Las specs de consenso en Python
  usan `py_arkworks_bls12381` y `ckzg`; el paquete está en PyPI desde mayo de 2026 y
  ningún cliente lo pinea.
- **Páginas**: `propuesta-foda.html`, `mapa-completo.html`, `architecture-map.html`,
  `fp-paso-a-paso.html`.

### `alexanderlhicks/leanerSTFSpec` — el EVM en Lean

> Una spec formal y ejecutable del *guest program*: el programa que corre adentro de un
> zkVM para validar bloques sin tener el estado.

- **Una sola función**: `runStatelessGuest : ByteArray → ByteArray`. Entra bloque más
  witness; salen 43 bytes de los que importa **uno**: válido o inválido. Total y
  determinística.
- **Cinco lenguajes encadenados**: Lean (la spec, los teoremas y las herramientas de
  chequeo), Python (73 scripts que son guardias, nunca spec), Markdown (4 868 líneas de
  spec informal, normativa), TOML (las fuentes de verdad, incluida la versión exacta de
  `py_ecc` que la semántica asume) y Bash/YAML.
- **El método que vale copiar**: testing diferencial. Lean y el Python de las
  `execution-specs` resuelven el mismo problema por separado, y un tercer programa compara
  las salidas. *"Observations are bug-finding evidence."*
- **Dato que los conecta**: sus módulos `Field`, `Curve`, `Pairing` y `Precompiles` están
  **vacíos** ("scaffolding only"), y cuando los escriba va a validar contra el
  `Bls/G1.lean` y `G2.lean` de `cryptography-specs`.
- **Página**: `leaner-stf-spec.html`. Leído el 11 oct 2026, commit `daa6a8a`.

### `github.com/verified-zkevm` — el paraguas y el puente Rust ↔ Lean

> Organización de la EF, 14 repos, meta declarada: *"making formally verified bug-free
> zk(E)VMs a possibility by 2027"*.

- **Tres frentes**: zkVM (`clean`, `zkLean`, spec Sail de RISC-V), EVM (`evm-asm`, KEVM) y
  criptografía (`ArkLib` 318★, `VCVio` 130★, `CompPoly`, `hax`).
- **El tema que le interesaba a Pablo**: cómo se conecta Rust con Lean.
  - **Rust → Lean existe y está maduro**: Charon baja el Rust a un formato intermedio
    (LLBC) y Aeneas lo sube a Lean 4; `cargo hax into lean` es el envoltorio cómodo.
  - **Lean → Rust no existe.** Lean compila a C, no tiene backend Rust.
- **Lo que hay que entender**: traducir **no es** demostrar. Son tres pasos —
  traducir (automático), **enunciar** qué significa que la función sea correcta (a mano,
  y es el paso que más piensa) y demostrar (a mano). Después de traducir, cada función
  queda traducida sin enunciado, con enunciado y `sorry`, o demostrada.
- **El precedente real**: ML-KEM (Kyber) de la librería SymCrypt de Microsoft, escrito en
  Rust, verificado con esta herramienta.
- **El costo**: la demostración vale sobre la traducción. Si Charon o Aeneas traducen mal,
  demostraste algo precioso sobre un programa que no es el tuyo.
- **Página**: `verified-zkevm.html`. Leído el 11 oct 2026.

### `NyxFoundation/gasper-lean4` — el consenso demostrado

> Casper FFG, el mecanismo de finalidad del consenso que corre **hoy** en Ethereum,
> formalizado en Lean 4 + Mathlib.

- **Tres teoremas**: *accountable safety* (si hay fork entre bloques finalizados, todos
  los validadores de la intersección son castigables), *slashable bound* (y esa
  intersección pesa, con cota explícita) y *plausible liveness* (y aun así el sistema
  puede seguir finalizando).
- **Generaliza el paper**: de 1-finalización a *k*-finalización, y de validadores
  estáticos a dinámicos. Traduce la formalización en Coq de Runtime Verification y
  **corrige un bug** del original.
- **Lo que no cubre**: LMD-GHOST. Casper FFG no elige qué cadena seguir, solo pone
  candados: "de este punto para atrás no se toca más".
- **Página**: `gasper-lean4.html`. Leído el 12 oct 2026, commit `7650709`.

#### Los dos repos hermanos (misma fundación)

| Repo | Qué es | Dato |
|---|---|---|
| `formal-leanSpec` | el modelo en Lean del **consenso nuevo** | 36 proposiciones, todas demostradas, con IDs (`ST-1`, `FC-3`…) que el cliente cita en sus comentarios |
| `verity` | el **cliente** de Lean Consensus | 29 235 líneas de Rust, **cero de Lean**; corre en devnet junto a `ethlambda` y `ream` |

**Y acá está el hallazgo más valioso de todo el estudio:** el Lean de `formal-leanSpec`
nunca procesó un bloque, y aun así encontró **dos bugs críticos** en la especificación que
todos los clientes están transcribiendo:

- **Sin horizonte de slot futuro**: un proposer honesto puede firmar un bloque en el slot
  2⁶³ y el loop de `process_slots` itera esa cantidad de veces. DoS para todos. Lo
  descubrieron *al demostrar que el loop termina*: termina matemáticamente, lo cual es
  silencioso sobre que sea un loop real no acotado.
- **La cabeza de la cadena no es función pura del store**: ante una equivocación, el
  código se queda con la atestación que entró primero al diccionario. Dos nodos honestos
  con los mismos bloques en distinto orden pueden elegir cabezas distintas. *"Every unit
  test passes, and heads diverge only on the interop network."*

---

## 4. Lo que se repite en los cuatro

1. **Spec ejecutable.** Los cuatro escriben la especificación como código que corre, no
   como prosa. Es la misma idea que Ethereum ya aplica con el Python de `consensus-specs`,
   un escalón más abajo.
2. **Cada proyecto serio se escribe su propio auditor de axiomas.** `cryptography-specs`
   no lo tiene (lo hicimos nosotros); `leanerSTFSpec` tiene `check-decls`; `gasper-lean4`
   tiene `#mr_audit_axioms`. Todos revisan lo mismo: de qué depende cada teorema.
3. **El patrón "puente".** Siempre hay un código que corre, una matemática que lo describe
   y un teorema que dice que coinciden. Lo vimos en `FpZMod.lean` (`powNat_eq_pow`), en
   `gasper-lean4` (`justifiedB_iff`) y en Aeneas (`mul2_add1_spec`). Cambia de dónde viene
   el lado programador; la forma del teorema es la misma.
4. **El hueco está siempre en el mismo lugar**: en la unión entre lo demostrado y lo que
   corre. `ConcreteBlsLaws`, el teorema de refinamiento, la fidelidad del traductor, el
   backend C que "sits outside every proof". Nadie lo cerró todavía.
5. **Y la conclusión práctica**: en producción corre Rust, C y Go. Lean está en la mesa de
   al lado — demuestra, genera vectores, audita specs y encuentra bugs antes de que
   lleguen a la red. El puente para que entre al runtime existe y está probado, pero nadie
   lo cruzó con algo que procese bloques de verdad.

---

## 5. No confundir

| Esto | No es esto |
|---|---|
| **Formalizar**: demostrar que las reglas son correctas | **Implementar**: escribir el programa que las sigue |
| **Compilar** Lean a C (backend del compilador) | **Traducir** código entre dos lenguajes de trabajo |
| **Traducir** Rust a Lean (Aeneas) | **Demostrar**: eso se escribe a mano, después |
| **Demostrado**: el kernel revisó cada paso | **Demostrado con *native axioms***: un paso lo calculó el compilador de Lean y el kernel lo aceptó sin revisar |
| **Demostrado** | **Demostrado *si* alguien demuestra otra cosa** (`ConcreteBlsLaws`) |
| **Kani**: todos los casos **hasta un límite** | **Teorema**: todos los casos, sin límite |

---

*Fuentes: clones de solo lectura de los cuatro repos, leídos entre el 11 y el 12 de
octubre de 2026. El detalle y las citas textuales, en las páginas HTML de esta misma
carpeta.*
