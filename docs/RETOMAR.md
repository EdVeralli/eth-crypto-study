# Retomar trabajo

_Ultima actualizacion: 2026-09-28_

## Donde quedamos

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

Ya no queda nada de infraestructura. Lo que sigue es estudio del codigo:

1. Seguir el orden de lectura de `notas-investigacion.md` sobre los `.lean`
2. Explorar la superficie de KZG desde Python (`eth_cryptography_specs.kzg`)
3. Mirar `Proofs/Kzg/CeremonyChecks.lean` — el teorema mas ambicioso, y el que
   todavia asume `ConcreteBlsLaws` sin probar
4. Buscar los `sorry` que queden en `Proofs/` y ver que falta demostrar

## Documentacion generada

- `docs/notas-investigacion.md` — todo lo que aprendimos sobre el repo
- `docs/architecture-map.html` — mapa interactivo (tambien en https://claude.ai/code/artifact/6ddc7716-0733-4d41-837f-469e76f7f6a1)
- `docs/bls_smoke.py` — verificacion end-to-end de BLS contra py_ecc
