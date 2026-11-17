# Restaurar el entorno después de formatear

Escrito el 11 nov 2026, antes de formatear la MacBook Pro (Intel).
Actualizado el 15 nov 2026 con lo que pasó al restaurar.

Esta guía está en el repo a propósito: después de formatear la vas a poder leer
en `github.com/EdVeralli/eth-crypto-study` desde cualquier navegador, antes de
tener nada instalado.

---

## 1. ANTES de formatear

Lo único que no está en ningún repo. Copialo a un pendrive o a donde sea:

```bash
cp ~/.ssh/id_rsa ~/.ssh/id_rsa.pub ~/.ssh/config /Volumes/TU_PENDRIVE/
```

- **`id_rsa` / `id_rsa.pub`** — la llave de GitHub. Tiene passphrase. Si no la
  respaldás, generás una nueva (paso 3) y hay que darla de alta en GitHub.
- **`config`** — las cuatro líneas del puerto 443. No están versionadas en
  ninguna parte y encontrarlas cuesta media hora.

Nota del 15 nov 2026: al final la llave `id_rsa` no se restauró. El 12 nov se
generó una nueva, `~/.ssh/id_ed25519` (sin passphrase), y se dio de alta en
GitHub. Y el `config` del 443 tampoco hizo falta ese día (ver el paso 3).

Y confirmá que los dos repos estén limpios y pusheados:

```bash
cd ~/eth-crypto-study && git status -sb && git log --oneline -1
cd ~/decoupled-consensus-apuntes && git status -sb && git log --oneline -1
```

Al 11 nov 2026 estaban en `bd06e19` y `926f43b`, los dos al día con origin.

⚠️ **Sólo se revisaron esas dos carpetas.** Si tenés trabajo en otro lugar del
disco, respaldalo aparte.

---

## 2. Qué instalar

| Qué | Para qué |
|---|---|
| **Xcode Command Line Tools** | trae `git`. `xcode-select --install` |
| **Docker Desktop** | la cadena de herramientas corre adentro de un contenedor |

Y nada más. Rust, Lean, hax, Charon y Aeneas **no se instalan en la Mac**: van
todos adentro de la imagen de Docker. Por eso el entorno es reproducible.

Aclaración del 15 nov 2026: eso vale para la cadena de herramientas de
`mini-stf`. El repo **raíz** (`lake build`, `.venv`, `docs/bls_smoke.py`,
`pytest`) sí necesita Lean y un Python >= 3.10 instalados en la Mac. Cómo se
hizo está en el paso 8.

---

## 3. SSH contra GitHub

Si respaldaste la llave:

```bash
mkdir -p ~/.ssh && chmod 700 ~/.ssh
cp /Volumes/TU_PENDRIVE/id_rsa ~/.ssh/
cp /Volumes/TU_PENDRIVE/id_rsa.pub ~/.ssh/
chmod 600 ~/.ssh/id_rsa
```

Si no la respaldaste, generá una nueva y dala de alta en GitHub
(Settings → SSH and GPG keys → New SSH key):

```bash
ssh-keygen -t ed25519 -C "edveralli@gmail.com"
cat ~/.ssh/id_ed25519.pub        # esto es lo que se pega en GitHub
```

**El archivo de configuración, sólo si la red bloquea el puerto 22.** En la red
de antes el 22 estaba bloqueado y sin esto el push no funcionaba. El 12 nov
2026 el 22 anduvo, así que este bloque no se agregó: `~/.ssh/config` apunta a
`github.com` por el puerto normal. Si `ssh -T` falla con
`port 22: Connection refused`, el arreglo es éste:

```bash
cat > ~/.ssh/config <<'EOF'
Host github.com
  Hostname ssh.github.com
  Port 443
  User git
EOF
chmod 600 ~/.ssh/config
```

Probalo antes de seguir:

```bash
ssh -T git@github.com
```

Tiene que responder `Hi EdVeralli! You've successfully authenticated`.

Lo que pasó el 12 nov 2026: la `id_rsa` no se restauró, se generó una
`id_ed25519` nueva sin passphrase, se registró en GitHub y `ssh -T` respondió
bien por el puerto 22.

---

## 4. Clonar

```bash
cd ~
git clone git@github.com:EdVeralli/eth-crypto-study.git
git clone git@github.com:EdVeralli/decoupled-consensus-apuntes.git
```

El segundo son los apuntes del paper "Decoupled consensus" — no necesita nada
más, son `.md` y `.html` que se abren con doble clic.

---

## 5. Armar la imagen de Docker

```bash
cd ~/eth-crypto-study/tooling/hax-lean
docker build --platform linux/amd64 -t hax-lean .
```

**Tarda bastante la primera vez** — compila `cargo-hax` y después precalienta
Charon, Aeneas y la nightly de Rust que Charon pide. Son varios GB. Mirá que
tengas disco.

El `--platform linux/amd64` no es opcional: hax no publica binarios para macOS
Intel. En esta Mac el contenedor corre nativo, sin emulación.

Y el Dockerfile fija `cargo-hax@0.4.2` a propósito. **No le saques la versión.**
Todo lo medido y documentado es contra 0.4.2, y 0.5.0 ya está publicada.

---

## 6. Regenerar el Lean

`proofs/` no está en el repo: son 124.386 archivos de Mathlib, Aeneas y hax
bajados por `lake`, varios GB. Al clonar no vas a ver una línea de Lean, y eso
es normal.

```bash
cd ~/eth-crypto-study/tooling/hax-lean
docker run --platform linux/amd64 -it \
  -v "$PWD/mini-stf:/work" \
  -v hax-cargo:/root/.cargo/registry \
  -v hax-cache:/root/.cache/hax \
  -v hax-elan:/root/.elan \
  hax-lean bash
```

Y adentro del contenedor:

```bash
cd /work && bash regenerar.sh
```

Ese script hace tres cosas y **la del medio no es opcional**: extrae, restaura
el Lean escrito a mano (que vive en `supuestos/` y `teoremas/`), y compila. Sin
el paso del medio, `lake build` se cae con identificadores desconocidos.

---

## 7. Verificar que quedó bien

Las tres cosas que tienen que dar:

```bash
# adentro del contenedor, en /work
cargo test
```
→ **9 pasan** (seis de ethlambda más tres nuestros)

```bash
cd /work/proofs/lean && lake build
```
→ **`Build completed successfully (1742 jobs)`**, sin ningún `sorry`. El primer
build sobre un clon limpio da 1743 (pasó al rearmar el 12 nov 2026) y los
siguientes 1742: un job de más la primera vez no es problema, lo que importa es
que termine en verde.

```bash
for f in state_transition process_slots process_block process_block_header \
         current_proposer is_proposer process_attestations is_valid_vote \
         try_finalize serialize_justifications attestation_data_matches_chain \
         slot_is_justifiable_after; do
  grep -qE "^def stf\.$f( |$)" /work/proofs/lean/MiniStf/Extraction/Funs.lean \
    && echo "ok    $f" || echo "FALTA $f"
done
```
→ **12 `ok`**, las doce funciones de la STF de ethlambda traducidas

No uses `grep -c "^def stf\."` para esto: cuenta todos los `def` (cuerpos de
loops, closures, instancias de `Debug`/`Display` y las diecinueve funciones
auxiliares nuestras) y da 66, no 12.

Si el `lake build` imprime las bases de axiomas, compará contra
`mini-stf/axiomas.txt`: treinta y nueve bloques, nueve nativos distintos en total, y
23 axiomas (3 estándar + 9 nativos + 11 modelos) para los siete teoremas sobre
`state_transition`.

---

## 8. Reconstruir el repo raíz (Lean y Python)

Esto no pasa por Docker. Es lo que hace falta para `lake build`, el `.venv`,
`docs/bls_smoke.py` y la suite de vectores del repo raíz. Se hizo el 12 nov 2026.

**Lean.** Instalar `elan` con el instalador oficial de `elan.lean-lang.org`.
Queda en `~/.elan`, y `~/.elan/bin` **no está en el `PATH` por defecto**:

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd ~/eth-crypto-study
lake exe cache get
lake build
```
→ **`Build completed successfully (3444 jobs)`**. El `lake exe cache get` baja
Mathlib ya compilado; sin eso son horas.

**Python.** El `python3` del sistema es 3.9.6 y el repo pide >= 3.10, así que
no sirve. Se instaló `uv` (queda en `~/.local/bin`, que tampoco está en el
`PATH` por defecto) y con él Python 3.12.16:

```bash
export PATH="$HOME/.local/bin:$PATH"
cd ~/eth-crypto-study
uv venv --python 3.12 .venv
uv pip install --python .venv "pytest==9.0.3" "ruamel.yaml==0.19.1" "py_ecc==8.0.0" "setuptools>=68" wheel
PATH="$HOME/.elan/bin:$PATH" uv pip install --python .venv --no-build-isolation -e .
.venv/bin/python docs/bls_smoke.py
```
→ **`ALL CHECKS PASSED`**. El tercer comando compila el binding y llama a
`lake`, por eso lleva `~/.elan/bin` en el `PATH`.

**La suite completa** (364 vectores, ~3 h):

```bash
caffeinate -i -s .venv/bin/python -m pytest -q
```

⚠️ **`caffeinate -s` sólo mantiene despierta la Mac enchufada a la corriente.**
Con batería se duerme igual y la suite queda parada. Ya pasó: la suite se
largó el 12 nov, se frenó porque la Mac se durmió con batería, y un reinicio
el 15 nov la cortó sin que hubiera terminado.

Se relanzó el 15 nov con la Mac enchufada y esa vez terminó:
**`364 passed in 7732.92s (2:08:52)`**. Con eso la Mac formateada quedó
verificada entera.

---

## 9. Trampas que ya nos comimos

Para no volver a descubrirlas:

- **Mensajes de commit largos.** Los heredoc de varias líneas se rompen en tu
  zsh (`dquote>`). Escribí el mensaje a un archivo y usá
  `git commit -F .git/mensaje-commit.txt`.
- **Confundir las consolas.** Cuando el prompt dice `root@...` estás adentro del
  contenedor, no en la Mac. `whoami` lo aclara.
- **El `--platform linux/amd64`** va en **todos** los `docker run`, no sólo en
  el `build`.
- **Una extracción fallida borra los archivos de `Assumptions/`.** Por eso
  `regenerar.sh` los vuelve a copiar siempre.
- **`caffeinate -s` no alcanza con batería.** Sólo impide que la Mac duerma
  mientras está enchufada. La suite de ~3 h hay que correrla enchufada y con la
  tapa abierta (ver el paso 8).
- **`lake` y `uv` no están en el `PATH`.** Viven en `~/.elan/bin` y
  `~/.local/bin`; en una terminal nueva hay que exportarlos o no se encuentran.

---

## 10. Dónde quedó el trabajo

**El paquete para LambdaClass está terminado** y vive en
`tooling/hax-lean/mini-stf/`. El punto de entrada es `PROPUESTA.md`
(castellano) o `PROPOSAL.md` (inglés) — los dos dicen lo mismo y se mantienen
al día juntos.

Qué tiene: la STF de ethlambda traducida a Lean con las doce funciones y cero
`sorry`, ocho de doce idénticas a las de ellos salvo comentarios, un bug que
encontramos en la reescritura con los dos tests que lo cubren, treinta y cinco
teoremas sobre su código —las siete proposiciones de transición de estado del
catálogo de formal-leanSpec, con las salvedades que dice la propuesta, y desde
el 17 nov los cuatro de la ventana de slots justificados y la ausencia de
pánico de ese módulo—, un punto donde su código se aparta de la especificación (el
empate de slots al justificar, con un test que lo muestra), y tres hallazgos de
la cadena de herramientas que no están documentados en ninguna parte.

**Lo único pendiente: enviárselo.** Al 11 nov no se les había mandado todavía.

Y si alguna vez se toca un archivo del paquete, hay que rehacer este chequeo,
porque las dos propuestas afirman las líneas de cada archivo y los números
envejecen solos:

```bash
cd ~/eth-crypto-study/tooling/hax-lean/mini-stf
git ls-files . | while read f; do printf "%6s  %s\n" "$(wc -l < "$f")" "$f"; done
```
