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
#
# LA VERSION VA FIJA, Y ES IMPORTANTE. Hasta el 11 nov 2026 esta linea decia
# `cargo install --locked cargo-hax` sin version, o sea la ultima. Todo lo que
# medimos y documentamos esta contra 0.4.2: los dos --opaque que hacen falta,
# los nombres que genera, los siete axiomas nativos, los 1742 jobs del build.
# Y 0.5.0 ya esta publicada, asi que sin fijar la version una imagen
# reconstruida HOY ya no reproduce el entorno. Las versiones de Charon y de
# Aeneas vienen determinadas por la de hax, que las baja sola: con 0.4.2 son
# charon nightly-2026.09.02 y aeneas build-183e4f0. La de Lean la fija el
# `lean-toolchain` de cada proyecto, que si esta versionado.
#
# Para subir de version: cambiala aca, volve a correr `regenerar.sh`, y
# re-medi todo antes de tocar la documentacion.
RUN cargo install --locked cargo-hax@0.4.2

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
