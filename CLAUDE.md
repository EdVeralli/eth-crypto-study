# Reglas de trabajo

## Git: solo se pushea a repos de EdVeralli

- Este repo (`github.com/EdVeralli/eth-crypto-study`) es el único al que se
  commitea y se pushea.
- **Nunca** hacer `push`, subir ramas ni abrir PRs a repos que no sean de
  `EdVeralli` — `ethereum/cryptography-specs` incluido, aunque el `origin` del
  clon local apunte ahí y el token de `gh` tenga scope `repo`.
- Antes de cualquier push: `git remote -v` y confirmar que el destino está bajo
  `EdVeralli/`. Si no lo está, parar y preguntar.

## Los dos directorios

| Directorio | Qué es | Qué se puede hacer |
|---|---|---|
| `~/eth-crypto-study` | Repo propio y **autocontenido**: fuentes, build, venv, vectores, notas | Todo: leer, escribir, compilar, correr, commitear, pushear |
| `~/cryptography-specs` | Clon de `ethereum/cryptography-specs` | **Solo lectura**; únicamente para traer commits de upstream |

Esta carpeta es la única carpeta de trabajo necesaria. Tiene `lake build` en
verde (3444 jobs), su propio `.venv` con los bindings de Python compilados y los
364 vectores de prueba. No hace falta agregar el clon de lectura a la sesión.

**Ojo con la máquina.** Lo de arriba vale en la Mac. `.lake/` y `.venv/` están en
el `.gitignore`, así que en un clon nuevo **no existen**: ahí solo se puede trabajar
sobre la documentación, salvo que se instale `elan` y se rehaga el build. El clon de
solo lectura de `cryptography-specs` tampoco está en otra máquina, y para los docs no
hace falta. Ver `docs/RETOMAR.md`, sección "Como retomar en otra computadora".

**Los repos del ecosistema** (`leanerSTFSpec`, `verified-zkevm`, `gasper-lean4`,
`verified-consensus`) se clonan **de solo lectura** para analizarlos. Vale la misma
regla: nunca pushear ahí. Lo que escribimos sobre ellos vive en `docs/` de este repo.

```bash
lake build                            # verde
.venv/bin/python docs/bls_smoke.py    # ALL CHECKS PASSED
caffeinate -i -s .venv/bin/python -m pytest -q   # suite completa, ~3 h
```

## Dónde está el estado

- `README.md` — qué estamos haciendo y las tareas pendientes
- `docs/RETOMAR.md` — dónde quedamos y los comandos para volver a arrancar
- `docs/notas-investigacion.md` — todo lo aprendido sobre el repo original
- `docs/repos-comparados.md` — el cuadro comparativo de los cinco repos del
  ecosistema que nos pasó Pablo. **La sección 0 es la que más le importa a él**:
  cómo convive Lean con los otros lenguajes (Rust, Python, C) en cada repo.

Leer esos cuatro antes de proponer el próximo paso.

## Contexto del proyecto

Estudio de las especificaciones de criptografía de Ethereum escritas en Lean 4
(BLS12-381, KZG, XMSS). La etapa de infraestructura está cerrada: `lake build`
en verde, bindings de Python andando y los 364 vectores de prueba reproducidos
byte a byte. Lo que queda es estudio y verificación, listado en el README.
