# Cuadro sinóptico: los repos del ecosistema Lean 4 de Ethereum

Los cinco repos que nos pasó Pablo. Del primero, `cryptography-specs`, tenemos copia de
estudio propia y lo recorrimos archivo por archivo; de los otros cuatro hicimos el análisis
leyéndolos. Todos los números están verificados sobre clones de solo lectura; la fecha de
lectura está en cada ficha.

Cada repo tiene su página HTML con el detalle; acá está el resumen para comparar de un
vistazo.

---

## 0. Lo más importante: cómo convive Lean con los otros lenguajes

Los cuatro repos usan Lean de cuatro maneras **distintas**, y ésa es la comparación que más
sirve. Resumidas:

| Repo | Lenguajes en juego | La jugada |
|---|---|---|
| **cryptography-specs** | **Lean 4 → C → Python** | Lean **es** el programa. `lake build` lo compila a C; 928 líneas de binding en C escritas a mano lo envuelven como extensión de Python, y Python lo llama como a cualquier biblioteca, sin enterarse de que abajo hay Lean |
| **verified-zkevm** | **Rust → Lean 4** (el Lean es el que se genera) | El programa es Rust y sigue siendo el original. Charon y Aeneas (o `cargo hax into lean`) leen el Rust y **generan** un Lean equivalente, que nunca se ejecuta. Ojo: lo generado son **sólo las definiciones**, y una definición no afirma nada. La pregunta que no contesta es *"¿demostración formal de qué?"* — esa respuesta se escribe a mano: el enunciado del teorema primero, la demostración del mismo después |
| **leanerSTFSpec** | **Lean 4 + Python** en paralelo (y en el horizonte, assembly RISC-V y Pancake) | Hay **dos programas que hacen lo mismo**, escritos por separado: la spec oficial de Ethereum, que está en Python, y la de Alexander, en Lean. Se les da el mismo bloque, cada uno calcula el resultado por su cuenta, y después se comparan las dos respuestas. Si no coinciden, uno de los dos está mal. Ninguno de los dos llama al otro |
| **gasper-lean4** | **Lean 4 y nada más** | No hay segundo lenguaje: el repo es 100% Lean. Se usa sobre todo como un matemático usa el papel — escribir con precisión qué significa que un bloque quede finalizado y demostrar que dos bloques en conflicto no pueden finalizarse los dos. Hay una parte que **sí calcula** (`Executable/`, con 58 `#eval`), pero corre adentro de Lean al compilar, sobre modelos de juguete de 6 u 8 bloques. Nada desplegable: el único ejecutable declarado imprime "Hello" |
| **verified-consensus** | **Lean 4 y nada más** | Lean solo, como el de arriba. Pero es el único de los cinco que **ya trae escrito el enunciado** de qué significa que un consenso sea correcto: trece garantías, demostradas sobre un modelo. Lo que falta es atarlo a un cliente, y ese cliente va a ser Rust |

Y en detalle:

### cryptography-specs — Lean compilado, llamado desde Python

Lean es el que programa la criptografía. `lake build` la baja a C, y 928 líneas de binding en C
escritas a mano la envuelven en una extensión de Python (`_native.so`, 8,8 MB); 33 `@[export]`
(14 funciones y 19 constantes) les dan nombre del lado de afuera. Python hace `import` y ejecuta Lean sin
enterarse. Así corrimos los 364 vectores de prueba.

**Lo que hay que destacar:** es el único de los cuatro donde *el código demostrado y el código
que corre son el mismo objeto*. Y, en el mismo repo, el único donde 10 teoremas se apoyan en
**native axioms** — el atajo en que el kernel no revisa un paso y deja que lo calcule el
compilador. La ventaja más grande y el relajo de rigor más grande, juntos.

### verified-zkevm — el Rust genera el Lean

Acá el original es Rust y nadie lo toca. Charon + Aeneas (o `cargo hax into lean`) leen la
representación intermedia del compilador de Rust y escriben un Lean equivalente, que se vuelve a
generar en cada cambio. Los teoremas se demuestran sobre ese Lean.

**Lo que se genera y lo que no.** Acá conviene ser preciso, porque es donde se confunde todo el
mundo: la traducción produce **las definiciones**, y nada más. El enunciado de qué quiere decir
"esta función es correcta", y la demostración de que lo es, se escriben **a mano** en Lean, igual
que en cualquier otro repo. La herramienta te ahorra transcribir el programa; no te ahorra demostrar
nada.

*Ejemplo, del tutorial de Aeneas.* De la función Rust `fn mul2_add1(x: u32) -> u32 { (x + x) + 1 }`
la herramienta genera sola su equivalente en Lean. Lo que no genera —y no podría— es el enunciado
`mul2_add1_spec`, que dice dos cosas que el Rust no dice en ninguna parte: que el resultado vale
2x+1, y, la parte interesante, **la precondición de que no desborda**. El Rust en modo release
envuelve el overflow en silencio; para demostrar que la función hace lo que uno cree, hay que
declarar explícitamente que eso no pasa. Toda la basura que el programador barrió bajo la alfombra
sale a la luz ahí, y hay que hacerse cargo una por una. (Si no se puede demostrar la precondición,
acabás de encontrar un bug.) Y después todavía falta escribir la demostración, paso por paso.

A eso hay que sumarle lo que ni siquiera se traduce: `unsafe`, llamadas al sistema e intrínsecos
quedan en `FunsExternal.lean` con un modelo escrito a mano, que es un supuesto más. **De las tres
piezas que hacen falta —definiciones, enunciados, demostraciones— la traducción automática cubre
una.**

**Lo que hay que destacar:** el Lean **nunca se ejecuta** — es un objeto de estudio al costado —
y la demostración vale sobre *la traducción*, no sobre tu Rust: hay que confiar en `rustc`, en
Charon y en Aeneas. Y en el otro sentido no existe nada: **Lean → Rust no hay**.

### leanerSTFSpec — Lean corre en paralelo, como árbitro

Acá Lean sí se compila, y les importa que corra rápido: el objetivo escrito en `CONTRIBUTING.md`
es quedar *"within 10× of native clients (evmone/revm-class), aiming for about 2×"*: el techo que se
fijan es diez veces más lento que un cliente nativo, y aspiran a dos. Pero **no lo llama nadie**:
hay cero `@[export]` en los 265 archivos, o sea que ninguna de sus funciones está expuesta para que
otro programa la use.

Lo que hacen es esto. Existen dos programas que calculan lo mismo, escritos por separado: la spec
oficial de Ethereum, que está en Python y se conoce como EELS, y ésta, que está en Lean. Un script
les entrega a los dos el mismo bloque, cada uno calcula el nuevo estado por su cuenta, y después se
comparan las dos respuestas. Si difieren, uno de los dos tiene un error y hay que ir a buscar cuál.
A eso se le dice **testing diferencial**.

**Lo que hay que destacar:** Lean no es una biblioteca acá, es un perito que se corre aparte para
auditar a otro. Y ojo hasta dónde llega eso: comparar salidas demuestra que coincidieron *en los
casos que probaste*, no en todos los posibles. Lo que convertiría eso en una garantía de verdad —el
teorema de refinamiento que ate la spec en Lean a las implementaciones reales (`evm-asm`, en
assembly RISC-V, y `stateless-pancaketh`, en Pancake)— ni siquiera está acordado **cómo
enunciarlo**.

### gasper-lean4 — Lean solo, sin salir de Lean

El repo es Lean y nada más: 65 archivos `.lean` y 359 teoremas. Lo único que no es Lean son el
Makefile, el YAML de CI y las tipografías y el CSS de KaTeX, que son los assets del sitio de
documentación. Lean se usa acá sobre todo como un matemático usa el papel — para escribir con
precisión qué significa que un bloque quede justificado y después finalizado, y demostrar cosas
sobre eso.

Lo que demuestran es Casper FFG, la parte del consenso que decide cuándo un bloque ya no se puede
revertir. El resultado principal: no pueden quedar finalizados dos bloques en conflicto a menos que
un tercio del stake haya hecho trampa — y si eso pasara, se puede señalar exactamente a quién
castigar.

**Sí hay una parte que calcula, y conviene saberlo.** Las definiciones de `Core/` son
*afirmaciones*: dicen qué significa algo, y no se ejecutan — son el material de los teoremas. Pero
hay una carpeta `Executable/` que da, de las mismas nociones, una versión que **sí se computa**:
donde `Core/` afirma "este conjunto de validadores forma quórum", `Executable/` tiene una función
que lo **calcula** y devuelve verdadero o falso, **más un teorema que demuestra que las dos
coinciden**. (En Lean lo primero se llama `Prop` y lo segundo `Bool`; el par concreto es
`IsQIntersectionWitness` / `qIntersectionWitnessB`.)
Después, en `Executable/UseCases/`, hay 58 `#eval` que lo corren sobre modelos concretos: 99
validadores, 6 u 8 bloques, y el árbol de padres escrito a mano.

**Lo que hay que destacar:** eso corre adentro de Lean, al compilar, sobre juguetes. Desplegable no
hay nada — el único ejecutable declarado en el `lakefile` imprime "Hello" y es el esqueleto que dejó
`lake new`, sin tocar. Y el techo está escrito en la firma de las funciones: piden `Fintype Hash`,
o sea que el conjunto de hashes tiene que ser finito y recorrible. Con `Hash := Fin 6` eso se cumple
y anda; con los 2²⁵⁶ hashes de la cadena real, no. A cambio, es el más riguroso de los cuatro: sus
teoremas usan sólo `propext` y `Quot.sound`, ni siquiera `Classical.choice`.

### verified-consensus — Lean solo, pero con el enunciado hecho

Como gasper-lean4: no hay segundo lenguaje. 1.047 archivos `.lean` y nada más, salvo
`verify.sh` (bash) y `check-review-boundary.rb` (Ruby), que son las herramientas de auditoría.
Cero `@[export]`, ningún ejecutable, nada que se traduzca. Para la pregunta de Pablo, el
casillero de Rust está vacío.

**Pero por qué importa igual.** Acá hay un modelo del protocolo con 8.360 teoremas, y entre
ellos trece garantías agrupadas en un solo enunciado, `Consensus`. Eso es justo la pieza cara:
lo que normalmente hay que escribir a mano antes de poder demostrar nada. Está escrita, está
revisada por su autor y tiene **testigos** — corridas concretas que satisfacen cada premisa, para
mostrar que ninguna de las trece es un teorema vacío.

**Y el modelo computa de verdad**: 27 de sus 29 archivos llevan instancias `Decidable`, y los
testigos corren la máquina de estados (hay un `#eval` que calcula el estado de un nodo después de
30 rondas). O sea que la puerta para llamarlo desde afuera **se puede construir**; sólo faltan los
`@[export]`.

Las tres vías para conectarlo con Rust, en orden de costo:

| Vía | Qué sería acá | Estado |
|---|---|---|
| **Oráculo** | ponerle `@[export]`, correrlo al lado del cliente Rust sobre los mismos eventos y comparar | nadie lo hizo; es lo más barato y encuentra discrepancias desde el primer día |
| **Rust → Lean** | traducir el consenso del cliente con hax/Aeneas y demostrar que cumple `Consensus` | el enunciado ya existe, que es la mitad del trabajo. Pero traducir un cliente entero está muy por encima de lo que esas herramientas manejan hoy |
| **Refinamiento** | demostrar que el cliente refina el modelo | lo correcto, y lo que nadie logró en ningún repo del ecosistema |

**El límite que hay que tener claro:** esto es un modelo, no una implementación. **No tiene una
sola línea de criptografía** — busqué BLS, SHA, Blake: nada. "Firmas infalsificables" no es
código, es una *premisa* del teorema. Un cliente real tiene que ganarse esa premisa verificando
firmas de verdad, y que se la gane no lo demostró nadie.

---

## 1. Dónde está cada uno

Ethereum se parte en dos mundos, y cada repo vive en uno:

```
CONSENSO  (quién propone bloques, quién vota, cómo se agregan las firmas)
├── cryptography-specs ....... la criptografía del consenso (BLS, KZG, XMSS)  ← copia propia
├── gasper-lean4 ............. el protocolo de finalidad del consenso de hoy (Casper FFG)
└── verified-consensus ....... el protocolo candidato nuevo (decoupled consensus)

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

| | **cryptography-specs** | **leanerSTFSpec** | **verified-zkevm** | **gasper-lean4** | **verified-consensus** |
|---|---|---|---|---|---|
| **Quién** | Ethereum Foundation | Alexander Hicks (el repo vive en su cuenta personal) | Ethereum Foundation (organización) | Nyx Foundation (comentarios en japonés en el código) | Francesco D'Amato (cinco años en EF Research; desde julio 2026 en Ethlabs) |
| **Qué especifica** | criptografía: BLS12-381, KZG, XMSS | la transición de estado (el módulo del EVM todavía está vacío) | — (es un paraguas de 14 repos) | Casper FFG: la finalidad | el *decoupled consensus*: §7 del paper, todavía no público |
| **Capa** | consenso | ejecución | ejecución | consenso | consenso |
| **Consenso** | el nuevo (post-cuántico) | — | — | **el actual** (Beacon Chain) | **el candidato nuevo** |
| **Archivos `.lean`** | 77 | 265 | varía por repo | 65 | **1 047** |
| **Líneas de Lean** | 19 995 | 41 736 | — | 11 948 | **334 092** |
| **Teoremas** | 357 a mano (492 con los autogenerados) | 2 318 | — | 359 | **8 360** |
| **Lean / Mathlib** | v4.29.1 | v4.34.0 | varía | v4.31.0 | v4.34.1 |
| **Licencia** | CC0 | Apache-2.0 o MIT | varias | MIT | CC0 |
| **Estado al leerlo** | activo (XMSS completado oct 2026) | activo | activo | **quieto desde jun 2026** | activo (publicado 23 sep, último commit 12 oct 2026) |

### Rigor: de qué axiomas dependen los teoremas

Esta es la parte que más nos costó entender, y la que más dice sobre cada proyecto.

**Primero, lo que es igual en los tres:** todo teorema en Lean lo revisa el *kernel*, el
núcleo chico del lenguaje que acepta o rechaza cada paso. Eso pasa siempre, por el solo
hecho de usar Lean; no distingue a nadie.

**Lo que cambia es de qué se permite depender.** Un teorema puede apoyarse en axiomas:
afirmaciones que se aceptan sin demostrar. Lean trae tres estándar, y además hay una vía
de escape — `native_decide` y `bv_decide` — donde el kernel, en vez de revisar el paso,
**le cree a código compilado**. Con `native_decide` ese código es el compilador de Lean, que
calcula el resultado ahí mismo; con `bv_decide` es un programa externo —un SAT solver— que
devuelve un certificado, revisado a su vez por un verificador compilado. En los dos casos queda
un axioma extra registrado en el teorema, y a eso le decimos *native axiom*.

Entonces la pregunta útil es: ¿qué axiomas se permiten, y hay **alguien que lo controle**?

| Repo | Axiomas permitidos | ¿Quién controla que se cumpla? |
|---|---|---|
| **cryptography-specs** | `propext`, `Quot.sound`, `Classical.choice` **+ 10 teoremas con *native axioms*** | **nadie** |
| **leanerSTFSpec** | `propext`, `Quot.sound`, `Classical.choice` | **un programa, en cada cambio que alguien sube** |
| **gasper-lean4** | **`propext` y `Quot.sound`. Nada más.** | **un programa, cada vez que se compila** |
| **verified-consensus** | `propext`, `Quot.sound`, `Classical.choice`. Cero axiomas propios, cero `sorry` | **un script de seis pasos** (`verify.sh`), que además chequea que la frontera de revisión no se ensucie |

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
  prohíbe `@[csimp]`, `implemented_by`, `extern`, `unsafe`, `partial` y `opaque`. El reglamento explica
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
  que importaba: se pidió prestado el enunciado en lugar de demostrarlo.

**Qué caracteriza entonces a uno válido:** que sea un enunciado **general de lógica, que no sepa
nada del problema que estás resolviendo**, y que exista una demostración —hecha fuera de Lean, en
teoría de conjuntos— de que agregarlo no introduce contradicciones. Los tres estándar cumplen las
dos cosas: no saben nada de BLS, de hashes ni de Ethereum, y esa demostración existe.

**Quién lo detecta:** adentro de Lean, nadie. El kernel acepta cualquier axioma sin chistar — eso
*es* un axioma. Lo único que lo delata es la lista de axiomas del teorema, y alguien que la mire y
decida si esa lista es aceptable. Por eso importa tanto quién controla esa lista, que es lo que
compara la tabla de arriba: en `leanerSTFSpec` y en `gasper-lean4` la revisa un programa en cada
cambio; en `cryptography-specs`, nadie.

Entonces, cuando algo no está demostrado, es por una de estas tres razones, que conviene
no mezclar:

| Ejemplo | Caso | ¿Se puede arreglar? |
|---|---|---|
| que SHA-256 no tenga colisiones, que el logaritmo discreto sea difícil | **Es una conjetura** | **no, nunca**: es el supuesto sobre el que se apoya toda la criptografía. Se declara como axioma aparte y explícito |
| `ConcreteBlsLaws` | **Falta trabajo** | **sí**: son leyes matemáticas, demostrables con los tres axiomas. Nadie las demostró todavía |
| los 10 teoremas con *native axioms* | **Se usó un atajo** | **sí**: son evitables. Upstream abrió el issue #28 para sacar dos de ellos, y en XMSS usaron `decide +kernel` (el mismo cálculo, hecho por el kernel) |

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
| **leanerSTFSpec** | sí, y les importa la velocidad (techo de 10× de un cliente nativo, aspiran a 2×) | no | **no**: cero `@[export]`, corre como proceso aparte |
| **verified-zkevm** | no (se compila el Rust) | **sí: Rust → Lean** (hax, Aeneas/Charon) | **no** |
| **gasper-lean4** | para razonar, no para servir | no | **no**: hay `#eval` de juguete adentro de Lean, nada desplegable — y no escalaría (pide `Fintype Hash`) |
| **verified-consensus** | sí, sólo para verificar: una hora de build | no | **no**: cero `@[export]` y ningún ejecutable — aunque el modelo **sí computa**, así que la puerta se podría construir |

De los ocho casilleros de las dos últimas columnas, sólo dos dicen algo. Van en detalle,
porque son los dos que de verdad nos sirven:

**Traducción de código: sólo en `verified-zkevm`, y en un solo sentido, Rust → Lean.** El Rust
sigue siendo el original y nadie lo toca: la traducción se genera al costado, se vuelve a generar
en cada cambio y no se edita a mano. Charon no lee el texto del `.rs` — lee la representación
intermedia del compilador (MIR), el programa ya desazucarado y con los tipos resueltos — y la baja
a LLBC. Aeneas convierte eso en Lean funcional puro: hace desaparecer las referencias mutables y
los préstamos, y envuelve todo en un tipo `Result`, que obliga a contemplar el caso de falla en cada paso,
porque una función Rust puede entrar en pánico o desbordar y en Lean toda función tiene que ser total. Lo que Aeneas no sabe convertir
—`unsafe`, llamadas al sistema, intrínsecos— queda declarado en `FunsExternal.lean` con un modelo
escrito a mano: eso no es traducción, es un supuesto, y todo teorema que pase por ahí vale sólo si
ese modelo describe bien lo que hace el Rust. Y **Lean → Rust no existe**: Lean compila a C, no
tiene backend Rust.

**Lean en el entorno de ejecución: sólo en `cryptography-specs`, y a medias.** Los 33 `@[export]`
hacen que esas definiciones Lean aparezcan como símbolos C adentro del `.so`; el binding en C las
envuelve y Python las llama con un `import` común y corriente. Eso es lo único que cierra el
círculo entre teoremas y ejecución: lo que corre es *la misma definición* de la que hablan los
teoremas, no una reimplementación que hace lo mismo. Si la spec se reescribiera en otro lenguaje,
los teoremas seguirían valiendo sobre el Lean pero no sobre lo que se ejecuta, y recuperar esa
garantía costaría un teorema de refinamiento — justo lo que a `leanerSTFSpec` le falta. Pero
**ningún cliente importa el paquete**: las specs de consenso en Python siguen con
`py_arkworks_bls12381` y `ckzg`. La puerta está abierta y todavía no entró nadie.

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
| **verified-consensus** | el modelo **supone** la criptografía y los tiempos en vez de calcularlos: "firmas infalsificables" es una premisa, no código. Que un cliente real se gane esas premisas no lo demostró nadie |

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
  las salidas. Para ellos esas observaciones son *"bug-finding evidence"*.
- **Dato que los conecta**: sus módulos `Vm`, `Field`, `Curve`, `Pairing` y `Precompiles` están
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
| `formal-leanSpec` | el modelo en Lean del **consenso nuevo** | 36 proposiciones, todas demostradas salvo 3 que quedan como axiomas (la criptografía, delegada a ArkLib), con IDs (`ST-1`, `FC-3`…) que el cliente cita en sus comentarios |
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

### `fradamt/verified-consensus` — el protocolo nuevo, demostrado entero

> El modelo en Lean 4 del *decoupled consensus* —la Sección 7 del paper que ya estudiamos
> en [`decoupled-consensus-apuntes`](https://github.com/EdVeralli/decoupled-consensus-apuntes)—
> y la demostración de sus garantías. Autor: Francesco D'Amato.

- **Un solo teorema para trece garantías**: `concreteConsensus` agrupa el encaje de las tres
  cadenas (finalizado dentro de estable, estable dentro de confirmado), la *accountable safety*,
  la monotonía, las cotas de inclusión y la resistencia a un apagón de red. Demostrarlas juntas
  obliga a cubrir las interacciones entre capas, que es donde estos protocolos se rompen.
- **La separación entre lo que lee un humano y lo que revisa la máquina.** De las 334.092
  líneas sólo hay que confiar en dos bibliotecas, y las dos tienen únicamente definiciones:
  `Model` (29 archivos, ~5.700 líneas) y `Statements` (12 archivos, ~1.150 líneas). **El 2% del
  repo.** Y `verify.sh` chequea mecánicamente que esa frontera no se contamine.
- **Testigos contra el teorema vacío.** Para cada enunciado público hay una corrida concreta que
  satisface todas sus premisas, demostrada en Lean. Es la prueba de que ninguna de las trece
  garantías es verdadera por vacuidad. No lo vimos en ningún otro repo. Lo dicen ellos mismos:
  *"a wrong binding leaves the theorem true and empty"*.
- **Los native axioms, confinados.** Usa `native_decide` cinco veces, las cinco en el testigo del
  apagón, y el README lo aclara: ese testigo arrastra `Lean.ofReduceBool`, el teorema de revisión
  no. Mismo atajo que `cryptography-specs`, con la diferencia de que acá está acotado y escrito.
- **Lo que ellos declaran que falta**: sus premisas son más fuertes que las del paper, y por eso
  la finalidad les exige `K ≥ 5` donde el paper dice `K ≥ 4`; los testigos tienen un bizantino
  **silencioso**, sin equivocación ni tráfico adversario; y modelan una sola ventana de asincronía.
- **El paper no es público** (`consensus.tex`, commit `9f5ed717ffac`) — pero nosotros tenemos el
  PDF, en el repo de apuntes. Es la única de las cinco formalizaciones que podemos leer contra su
  propia fuente. Ojo: nuestro PDF es del 28 de agosto y llega hasta §7; el `.tex` que formalizaron
  referencia además §8, §9 y §10, así que es una versión posterior.
- **Página**: todavía no tiene. Leído el 18 oct 2026, commit `d379754`.

---

## 4. Lo que se repite en todos

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
   backend C, que queda fuera de toda demostración. Nadie lo cerró todavía.
5. **Y la conclusión práctica**: en producción corre Rust, C y Go. Lean está en la mesa de
   al lado — demuestra, genera vectores, audita specs y encuentra bugs antes de que
   lleguen a la red. El puente para que entre al runtime existe y ya se usó, pero nadie
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

*Fuentes: clones de solo lectura de los cuatro repos. `cryptography-specs` se recorrió archivo
por archivo entre septiembre y el 7 de octubre de 2026; los otros tres se leyeron entre el 11 y el
13 de octubre. El detalle y las citas textuales, en las páginas HTML de esta misma carpeta.*
