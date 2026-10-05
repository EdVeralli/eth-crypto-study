# Retomar trabajo

_Ultima actualizacion: 2026-10-05_

## Donde quedamos (5 oct 2026): repaso de los mapas

La infraestructura esta cerrada (ver mas abajo). Desde el 29 sept estamos
armando y repasando la **documentacion de estudio** en `docs/`, para que
alguien que llega (Pablo, por ejemplo) entienda el repo sin haber estado en
las sesiones. Son tres paginas HTML que se abren con el navegador:

1. `docs/mapa-completo.html` — el big picture
2. `docs/architecture-map.html` — los modulos por dentro y por que spec-first
3. `docs/fp-paso-a-paso.html` — guia del piso 1 (`Bls/Fp.lean`)

### Estado del repaso de `mapa-completo.html`

| Seccion | Estado |
|---|---|
| Encabezado e intro ("Que corre y que se demuestra") | Repasado: sin "upstream"; la bajada explica spec vs teoremas |
| Leyenda de colores (las dos filas) | Repasado: mismos nombres que el diagrama 1 (spec / teoremas / binding, con su mundo) |
| Bloque de pisos de estudio ("El mapa es la vista de arriba...") | Repasado: explica que es un piso; "en el repo" en vez de "en tu Mac" |
| Diagrama 1: las capas | Repasado: cada caja dice en que mundo esta (Python, C, Lean); nota del lakefile en criollo |
| Diagrama 2: build y verificaciones | Repasado: "teoremas" en vez de "pruebas"; verificaciones numeradas 1-2-3 |
| Que es un vector de prueba | Nueva: dos `data.yaml` reales (valido vs adulterado) y el test invertido |
| Mapa archivo por archivo | Repasado: explicacion de como leerlo y ejemplo con `G1Group` |
| Donde la separacion no es perfecta | Repasado (5 oct): datos verificados con `#print axioms`: 10 de 492 teoremas dependen de *native axioms* (`native_decide` + `bv_decide`), 3 son reglas generales (`uncompress_compress` entre ellas). Desplegable con la tabla y como comprobarlo. Se agrego `docs/native_axioms.lean` |
| Tres verificaciones, las tres en verde | Repasado: se deja como esta |
| Glosario | Repasado: 6 terminos nuevos (.so, marshalling, simbolo C, lakefile, sorry, native axioms) |

**El repaso de `mapa-completo.html` esta terminado.**

### Pendiente

- Repasar `architecture-map.html` con el mismo criterio (frases que no se
  entienden, ejemplos concretos).
- Repasar `fp-paso-a-paso.html`.
- Escribir la guia del piso 2: `Bls/G1.lean` + `G1Group` / `G1Order` / `G1Msm`.

### Criterios que fuimos acordando para los mapas

- Explicar en criollo, con analogias, y con **ejemplos reales del repo**.
- Cada caja dice en que lenguaje ("mundo") estamos: Python, C o Lean.
- "Teoremas" para las demostraciones de Lean; "proof KZG" para los 48 bytes
  criptograficos de KZG. Nunca "pruebas" a secas.
- Compacto: si algo es largo, va en un desplegable.
- Decir **native axioms** (no "atajos") para `native_decide` / `bv_decide`.
- Antes de afirmar algo sobre los teoremas, verificarlo con Lean (`#print axioms`,
  `docs/native_axioms.lean`), no suponerlo. El 1 oct el mapa decia "8
  native_decide en ejemplos concretos" y era incompleto.
- Las paginas de `docs/` se enlazan entre si con links relativos.

## Estado de la infraestructura (cerrado el 28 sept)

**Todo cerrado.** El build de Lean esta completo, BLS12-381 y KZG corren desde
Python, y la suite completa de 364 vectores de prueba paso sin una sola
diferencia. No hay nada pendiente de la etapa de "hacerlo funcionar".

```
lake build   ->  Build completed successfully (3444 jobs), exit 0
pytest       ->  364 passed in 10670.43s (2:57:50), exit 0
git status   ->  limpio, diff en tests/ vacio
```

Ese `git status` limpio es el resultado importante: el spec de Lean regenero
los 364 vectores commiteados **byte a byte**. Ver `notas-investigacion.md`
para el desglose por handler y las dos lecciones sobre el costo de correrla.

## Repos

- **Tu repo (todo vive aca):** `~/eth-crypto-study` — `github.com/EdVeralli/eth-crypto-study`.
  Autocontenido desde el 29 sept 2026: fuentes Lean, `lake build` en verde,
  `.venv` con los bindings compilados, los 364 vectores y los docs.
- **Repo original (solo lectura):** `~/cryptography-specs` — clon de
  `ethereum/cryptography-specs`, solo para traer commits de upstream.
- **Docs generados:** `~/eth-crypto-study/docs/` — mapa interactivo + notas de investigacion

## Estado actual

| Paso | Estado |
|---|---|
| `lake build` | Completo — 3444 jobs, exit 0, sin errores ni warnings |
| venv + `pip install -e '.[test]'` | Completo — extension C compilada y enlazada |
| `from eth_cryptography_specs import bls` | Funciona |
| Verificacion cruzada contra `py_ecc` | Pasa (`docs/bls_smoke.py`) |
| Suite completa de 364 vectores | **Paso — 0 diferencias contra git** |

## Como volver a usarlo

El venv ya existe en tu propio repo, no hay que recrearlo:

```bash
cd ~/eth-crypto-study
.venv/bin/python -c "from eth_cryptography_specs import bls, kzg; print(dir(kzg))"
.venv/bin/python docs/bls_smoke.py
```

Si se borra `.lake/`, rehacer el build (`lake exe cache get` y `lake build`).
Si se borra `.venv/`, rehacer solo el paso de pip — pero ojo: `pip install -e`
dispara `lake build` de nuevo via `setup.py`.

## Si vas a correr la suite de nuevo

Dos cosas aprendidas a golpes (detalle en `notas-investigacion.md`):

1. **Enchufada y con la tapa abierta.** Sin eso la Mac duerme y la suite no
   avanza: medimos 2 vectores en dos dias y medio. Con `caffeinate` salio en
   97 minutos.
2. **No extrapoles el ritmo.** La `lru_cache` de los fixtures hace que los
   primeros casos de cada handler paguen todo y el resto vuele.

```bash
cd ~/eth-crypto-study
caffeinate -i -s .venv/bin/python -m pytest -q          # completa, ~3 h de CPU
caffeinate -i -s .venv/bin/python -m pytest bindings/python/tests/kzg -k verify_kzg_proof   # un handler
```

Si ya hay un pytest corriendo y solo querés que no duerma, sin perder la
cache en memoria:

```bash
caffeinate -i -s -w <PID>    # el candado se suelta cuando el proceso termina
```

## Superficie de BLS expuesta a Python

La API es acotada — solo dos funciones y dos constantes:

```python
from eth_cryptography_specs import bls

bls.BYTES_PER_PUBKEY          # 48
bls.BYTES_PER_SIGNATURE       # 96
bls.eth_aggregate_pubkeys(pubkeys)                  # -> bytes (48)
bls.eth_fast_aggregate_verify(pubkeys, msg, sig)    # -> bool
```

**No hay firmado expuesto.** Para generar claves y firmas hay que usar
`py_ecc.bls.G2ProofOfPossession` (ya instalado como dependencia de test); el
spec en Lean solo cubre agregacion y verificacion, que es lo que necesita un
cliente de consenso.

## Proximos pasos posibles

Ya no queda nada de infraestructura. El estudio sigue piso por piso (tabla en
el README, seccion "Empeza por aca"); antes, terminar el repaso de los mapas
(ver "Donde quedamos" arriba).

## Documentacion generada

- `docs/mapa-completo.html` — big picture: spec vs teoremas, vectores, pisos de estudio
- `docs/architecture-map.html` — modulos por dentro y por que spec-first
- `docs/fp-paso-a-paso.html` — guia del piso 1, `Bls/Fp.lean` y sus teoremas
- `docs/notas-investigacion.md` — todo lo que aprendimos sobre el repo
- `docs/bls_smoke.py` — verificacion end-to-end de BLS contra py_ecc
- `docs/README-upstream.md` — README original del repo de Ethereum
