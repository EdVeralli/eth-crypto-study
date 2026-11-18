# Reglas de trabajo

## Git: solo se pushea a repos de EdVeralli

- Este repo (`github.com/EdVeralli/eth-crypto-study`) es el único al que se
  commitea y se pushea.
- **Nunca** hacer `push`, subir ramas ni abrir PRs a repos que no sean de
  `EdVeralli` — `ethereum/cryptography-specs` incluido, aunque el `origin` de un
  clon local apunte ahí o haya credenciales con permiso de escritura.
- Antes de cualquier push: `git remote -v` y confirmar que el destino está bajo
  `EdVeralli/`. Si no lo está, parar y preguntar.

## Los dos directorios

| Directorio | Qué es | Qué se puede hacer |
|---|---|---|
| `~/eth-crypto-study` | Repo propio y **autocontenido**: fuentes, build, venv, vectores, notas | Todo: leer, escribir, compilar, correr, commitear, pushear |
| `~/cryptography-specs` | Clon de `ethereum/cryptography-specs`. **No existe desde el formateo del 12 nov 2026**; si hace falta, se vuelve a clonar | **Solo lectura**; únicamente para traer commits de upstream |

Esta carpeta es la única carpeta de trabajo necesaria. Tiene `lake build` en
verde (3444 jobs), su propio `.venv` con los bindings de Python compilados y los
364 vectores de prueba. No hace falta agregar el clon de lectura a la sesión.

**Ojo con la máquina.** Lo de arriba vale en la Mac. `.lake/` y `.venv/` están en
el `.gitignore`, así que en un clon nuevo **no existen**: ahí solo se puede trabajar
sobre la documentación, salvo que se instale `elan` y se rehaga el build. El clon de
solo lectura de `cryptography-specs` tampoco está en otra máquina, y para los docs no
hace falta. Ver `docs/RETOMAR.md`, sección "Como retomar en otra computadora".

La Mac se formateó el 12 nov 2026 y el entorno se rehízo ese día: Lean con `elan`
(en `~/.elan/bin`), Python 3.12 con `uv` (en `~/.local/bin`) y el `.venv` nuevo.
Ninguna de esas dos carpetas está en el `PATH` por defecto. Los pasos exactos
están en `RESTAURAR.md`.

**Los repos del ecosistema** (`leanerSTFSpec`, `verified-zkevm`, `gasper-lean4`,
`verified-consensus`) se clonan **de solo lectura** para analizarlos. Vale la misma
regla: nunca pushear ahí. Lo que escribimos sobre ellos vive en `docs/` de este repo.

```bash
lake build                            # verde
.venv/bin/python docs/bls_smoke.py    # ALL CHECKS PASSED
caffeinate -i -s .venv/bin/python -m pytest -q   # suite completa, ~3 h
```

La suite hay que correrla **con la Mac enchufada**: `caffeinate -s` sólo la
mantiene despierta con corriente. Con batería se duerme y la corrida no avanza.

## Dónde está el estado

- `README.md` — qué estamos haciendo y las tareas pendientes
- `docs/RETOMAR.md` — dónde quedamos y los comandos para volver a arrancar
- `docs/notas-investigacion.md` — todo lo aprendido sobre el repo original
- `docs/repos-comparados.md` — el cuadro comparativo de los cinco repos del
  ecosistema que nos pasó Pablo. **La sección 0 es la que más le importa a él**:
  cómo convive Lean con los otros lenguajes (Rust, Python, C) en cada repo.
- `tooling/hax-lean/mini-stf/PROPUESTA.md` (y `PROPOSAL.md`, en inglés) — el
  paquete para LambdaClass: la STF de ethlambda pasada por la cadena de
  herramientas Rust → Lean, con sus teoremas. El `README.md` de esa carpeta es
  la bitácora de cómo se llegó.
- `RESTAURAR.md` — cómo rearmar el entorno desde cero, y dónde quedó el trabajo.

Leer esos seis antes de proponer el próximo paso.

## Vocabulario

- **"cadena" sola está prohibida.** La palabra tiene dos sentidos en este repo y se
  confunden: la **cadena de herramientas** (`rustc → Charon → Aeneas → Lean`) y la
  **cadena de bloques**. Escribir siempre cuál de las dos — "la cadena de herramientas",
  "la cadena de bloques" o el nombre propio ("la Beacon Chain"). "Encadenadas" para
  describir herramientas una atrás de otra está bien.

## Contexto del proyecto

Estudio de las especificaciones de criptografía de Ethereum escritas en Lean 4
(BLS12-381, KZG, XMSS). La etapa de infraestructura está cerrada: `lake build`
en verde, bindings de Python andando y los 364 vectores de prueba reproducidos
byte a byte. Lo que queda es estudio y verificación, listado en el README.

Desde fines de octubre de 2026 hay una segunda línea de trabajo: aplicar la
cadena de herramientas Rust → Lean (hax + Charon + Aeneas) a la función de
transición de estado de `lambdaclass/ethlambda`. El resultado es el crate
`tooling/hax-lean/mini-stf/`, cerrado el 6 nov 2026 y ampliado el 15 nov con
las siete proposiciones de transición de estado del catálogo de
formal-leanSpec (`ST-1` a `ST-7`) y, el 17 nov, con los cuatro teoremas sobre
la ventana de slots justificados, la ausencia de pánico de ese módulo y un
comentario del código de ethlambda verificado. Son 67 resultados. Lo único
pendiente es enviárselo a LambdaClass; qué teoremas faltan está en los
pendientes 8 y 9 del `README.md`.
