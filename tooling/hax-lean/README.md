# Entorno Docker para la cadena de herramientas Rust → Lean

Traducir Rust a Lean con **hax + Charon + Aeneas**, desde una Mac.

## Por qué Docker y no la Mac directamente

hax publica binarios precompilados de Charon y Aeneas sólo para tres
plataformas. Está en su propio código:

```rust
pub const SUPPORTED_PLATFORMS: &[&str] = &["linux-x86_64", "linux-aarch64", "macos-aarch64"];
```

Y su manual lo dice sin vueltas: *"On any other platform there is nothing to
download, and hax reports so, naming the version it wanted; build `aeneas` and
`charon` yourself."*

O sea que en una **Mac Intel** (`uname -m` → `x86_64`) no hay binarios. Compilar
Aeneas a mano es OCaml, varias horas, en una plataforma que ellos no testean.
Un contenedor `linux/amd64` evita todo eso y, en una Mac Intel, **corre nativo,
sin emulación**.

## Construir

Necesitás Docker Desktop instalado. Después:

```bash
cd tooling/hax-lean
docker build --platform linux/amd64 -t hax-lean .
```

Tarda un rato largo la primera vez: compila `cargo-hax` (unos 5 minutos) y el
bloque de precalentado se baja Charon, Aeneas y la nightly de Rust que Charon
pide. Son varios GB entre todo — mirá que tengas disco.

## Usar

Montá la carpeta del crate que quieras traducir:

```bash
docker run --platform linux/amd64 -it \
  -v ~/mi-crate:/work \
  -v hax-cargo:/root/.cargo/registry \
  -v hax-cache:/root/.cache/hax \
  -v hax-elan:/root/.elan \
  hax-lean bash
```

Los volúmenes del final hacen que la segunda vez no vuelva a bajar nada.
Adentro:

```bash
cargo hax into lean          # traduce; deja el proyecto Lean en proofs/lean
cd proofs/lean
lake build                   # tipa lo generado
```

El proyecto que arma Aeneas **depende de Mathlib**, pero no hace falta compilarla ni
pedirla: lake se baja los artefactos ya compilados por su cuenta (*"Using cache (Azure)"*,
8542 archivos). Son unos **7,7 GB** que caen en `proofs/lean/.lake` y que conviene borrar
cuando terminás — el bind mount los escribe en tu disco, no en un volumen de Docker.

Dos avisos de la primera corrida: no uses `| tail`, porque te esconde todo el avance hasta
que termina; y si querés ver que progresa, miralo desde otra terminal con
`docker exec <id> du -sh /work/proofs/lean/.lake`.

## Lo que aprendimos probándolo (23 oct 2026)

Esto se verificó sobre Ubuntu 24.04 x86_64, con `cargo-hax 0.4.2`,
`charon nightly-2026.09.02` y `aeneas build-183e4f0`.

**Lo que anda.** La cadena de herramientas entera: hax se baja Charon y Aeneas solo, instala la
nightly que Charon pide, traduce, y arma un proyecto Lean completo con su
`lakefile.toml` y su `lean-toolchain`.

**Dos reglas que cuestan caro aprender por las malas:**

1. **El objetivo tiene que ser su propio crate.** El filtro `-i` de hax **no
   llega a Charon ni a Aeneas**: ellos procesan el crate entero *y sus
   dependencias*. Apuntar a un módulo dentro de un crate grande no sirve — un
   solo `dyn Error` en una dependencia dispara un error de *mixed declaration
   group* y detrás vienen cientos de errores internos en cascada, sin que se
   escriba un solo archivo.

2. **El obstáculo no es `std`.** `HashMap` se traduce solo; Aeneas trae sus
   propios modelos de las colecciones (la librería `CoreModels`, que aparece
   entre los imports), y la plantilla de cosas a modelar a mano puede salir
   vacía. Lo que no pasa son **los closures que se quedan con una referencia
   hacia adentro de una colección**: un `max_by_key` sobre una colección por
   referencia hace fallar a Aeneas con *"Can't end abstraction N as it is set as
   non-endable"*, que es su maquinaria de *borrows* dándose por vencida. El
   cuerpo de la función sale como `sorry` y la firma sale bien. Ojo con la
   formulación: **no es que los closures no pasen** — un `.map()` sobre un
   `Option` de números se traduce sin problema. Es el borrow lo que molesta, no
   el closure.

**Lo que sí pasa limpio:** código con `for i in 0..n`, indexación, aritmética
con `checked_*` y el operador `?`. Probado sobre un archivo real de ethlambda
(`justified_slots_ops.rs`, 89 líneas) puesto en un crate propio: **19
definiciones, cero `sorry`, cero errores, nada que modelar a mano, y `lake build`
en verde** (1737 jobs). Ese crate está acá al lado, en
[`ejemplo-jsops/`](ejemplo-jsops/), para que puedas repetirlo.

Dos detalles de forma que conviene saber antes de abrir el Lean generado:

- De esas 19 definiciones, **nueve son el código de ethlambda**; ocho son el tipo
  sustituto que escribimos para que el crate se sostenga solo, y dos son la
  maquinaria del closure.
- Cada `for` sale como **tres** definiciones: `<f>_loop.body`, `<f>_loop` y `<f>`.
  Demostrar algo sobre un loop va a ser demostrar un invariante del cuerpo y
  subir por inducción.
- `Verification/ProofObligations.lean` **viene vacío**: es un placeholder que hax
  crea una vez y no vuelve a tocar. No hay obligaciones automáticas derivadas de
  los `.expect()` — ese archivo es donde escribís vos.

El análisis completo de qué parte de ethlambda es candidata está en
[`docs/ethlambda-por-donde-empezar.md`](../../docs/ethlambda-por-donde-empezar.md).

## Estado de este Dockerfile

**Probado de punta a punta el 26 de octubre de 2026** en una MacBook Pro Intel:
la imagen construye, el contenedor traduce y el `lake build` cierra en verde.
