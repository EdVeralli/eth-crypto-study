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
| `~/eth-crypto-study` | Repo propio: notas, docs, experimentos | Leer, escribir, commitear, pushear |
| `~/cryptography-specs` | Clon de `ethereum/cryptography-specs` | **Solo lectura** y build (`lake build`, `pytest`, `.venv`) |

El build de Lean y el venv de Python viven en `~/cryptography-specs` porque son
del proyecto original; los resultados y las notas se escriben acá.

## Dónde está el estado

- `README.md` — qué estamos haciendo y las tareas pendientes
- `docs/RETOMAR.md` — dónde quedamos y los comandos para volver a arrancar
- `docs/notas-investigacion.md` — todo lo aprendido sobre el repo original

Leer esos tres antes de proponer el próximo paso.

## Contexto del proyecto

Estudio de las especificaciones de criptografía de Ethereum escritas en Lean 4
(BLS12-381, KZG, XMSS). La etapa de infraestructura está cerrada: `lake build`
en verde, bindings de Python andando y los 364 vectores de prueba reproducidos
byte a byte. Lo que queda es estudio y verificación, listado en el README.
