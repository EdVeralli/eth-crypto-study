# Entorno para traducir Rust a Lean con la cadena hax + Charon + Aeneas.
#
# Se construye para linux/amd64 a proposito: hax publica binarios para
# linux-x86_64, linux-aarch64 y macos-aarch64, pero NO para macOS Intel. En una
# Mac Intel este contenedor corre nativo, sin emulacion.
#
# Construir:  docker build --platform linux/amd64 -t hax-lean .
# Usar:       ver README.md

FROM --platform=linux/amd64 ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      build-essential clang cmake curl git ca-certificates pkg-config libssl-dev \
 && rm -rf /var/lib/apt/lists/*

# rustup. Charon lo necesita para instalarse su propia nightly en el momento de
# extraer: no alcanza con un rustc suelto.
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path
ENV PATH=/root/.cargo/bin:$PATH

# hax. Para el backend Lean no hace falta ningun otro componente: desde la
# version 0.4.0 corre Charon + Aeneas en vez del motor propio de hax, y los
# descarga solo. Compilarlo tarda unos 5 minutos, una sola vez.
RUN cargo install --locked cargo-hax

# elan, para compilar el proyecto Lean que sale de la traduccion.
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --no-modify-path
ENV PATH=/root/.elan/bin:$PATH

# Precalentado con una traduccion de juguete. Deja adentro de la imagen a
# Charon, a Aeneas y a la nightly de Rust que Charon pide. Sin esto, el primer
# `cargo hax into lean` de cada contenedor nuevo vuelve a bajar todo eso
# (son varios cientos de MB). Si preferis una imagen chica, borra este bloque.
RUN cargo new /tmp/warmup --lib \
 && printf 'pub fn square(x: u8) -> u8 { x * x }\n' > /tmp/warmup/src/lib.rs \
 && cd /tmp/warmup \
 && cargo hax into lean \
 && rm -rf /tmp/warmup

WORKDIR /work
CMD ["bash"]
