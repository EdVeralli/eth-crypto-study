#!/usr/bin/env bash
# Regenera la traduccion a Lean desde cero y la compila.
#
# Se corre ADENTRO del contenedor, desde /work:
#     bash regenerar.sh
#
# Dos cosas que hay que saber:
#
# 1. Los dos `--opaque` de fmt son imprescindibles. Sin ellos, cada
#    `#[derive(Debug)]` rompe con "[Error] Unreachable". No se puede sacar
#    el derive: `.expect()` lo necesita.
#
# 2. hax siembra los archivos de `Assumptions/` UNA vez desde sus templates
#    y despues no los toca, pero una extraccion fallida los borra. Las
#    copias buenas viven en `supuestos/` y `teoremas/`, que si se commitean.
#    Por eso se vuelven a copiar aca en cada corrida.
set -euo pipefail

cd "$(dirname "$0")"

echo "=== 1. extraccion ==="
cargo hax into lean \
  --charon-args="--opaque '{impl core::fmt::Debug for _}' \
                 --opaque '{impl core::fmt::Display for _}'"

echo "=== 2. restaurar lo escrito a mano ==="
cp supuestos/TypesExternal.lean supuestos/FunsExternal.lean \
   proofs/lean/MiniStf/Assumptions/
cp supuestos/RevisarAxiomas.lean proofs/lean/
cp teoremas/ProofObligations.lean proofs/lean/MiniStf/Verification/

echo "=== 3. compilar ==="
cd proofs/lean
lake build

echo "=== listo ==="
