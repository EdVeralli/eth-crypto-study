# Retomar trabajo

## Donde quedamos

Estamos analizando el repo `ethereum/cryptography-specs` (especificaciones
formales de criptografia para Ethereum en Lean 4). Ya entendimos la
arquitectura, la separacion spec/proof, y como se enlazan.

Queremos ejecutar BLS12-381 desde Python pero el build de Lean no termino.

## Repos

- **Repo original (solo lectura):** `~/cryptography-specs` — clon de `ethereum/cryptography-specs`
- **Tu repo personal:** `~/eth-crypto-study` — copia independiente en `github.com/EdVeralli/eth-crypto-study`
- **Docs generados:** `~/eth-crypto-study/docs/` — mapa interactivo + notas de investigacion

## Pasos para retomar

### 1. Compilar Lean (pendiente)

```bash
cd ~/cryptography-specs
lake exe cache get        # solo si se borro .lake/
lake build                # puede tardar 10-20 min
```

Hay 34 archivos .c.o.export parcialmente compilados del intento anterior.
Si .lake/ sobrevivio al reinicio, `lake build` continua desde ahi.

### 2. Instalar Python bindings

```bash
cd ~/cryptography-specs
python3 -m venv .venv
source .venv/bin/activate
pip install -e '.[test]'
```

### 3. Probar BLS desde Python

```python
from eth_cryptography_specs import bls
```

## Documentacion generada

- `docs/notas-investigacion.md` — todo lo que aprendimos sobre el repo
- `docs/architecture-map.html` — mapa interactivo (tambien en https://claude.ai/code/artifact/6ddc7716-0733-4d41-837f-469e76f7f6a1)
