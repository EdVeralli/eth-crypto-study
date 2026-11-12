# Restaurar el entorno después de formatear

Escrito el 11 nov 2026, antes de formatear la MacBook Pro (Intel).

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

**Y en los dos casos, el archivo de configuración.** Sin esto el push no
funciona, porque el puerto 22 está bloqueado en tu red:

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
→ **8 pasan** (seis de ethlambda más dos nuestros)

```bash
cd /work/proofs/lean && lake build
```
→ **`Build completed successfully (1742 jobs)`**, sin ningún `sorry`. Al
rearmar el 12 nov 2026 dio 1743: un job de más no es problema, lo que importa
es que termine en verde.

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
`mini-stf/axiomas.txt`: siete nativos distintos, y 13 / 13 / 14 / 20 por
teorema.

---

## 8. Trampas que ya nos comimos

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

---

## 9. Dónde quedó el trabajo

**El paquete para LambdaClass está terminado** y vive en
`tooling/hax-lean/mini-stf/`. El punto de entrada es `PROPUESTA.md`
(castellano) o `PROPOSAL.md` (inglés) — los dos dicen lo mismo y se mantienen
al día juntos.

Qué tiene: la STF de ethlambda traducida a Lean con las doce funciones y cero
`sorry`, ocho de doce idénticas a las de ellos salvo comentarios, un bug que
encontramos en la reescritura con los dos tests que lo cubren, cuatro teoremas
sobre su código, y tres hallazgos de la cadena de herramientas que no están
documentados en ninguna parte.

**Lo único pendiente: enviárselo.** Al 11 nov no se les había mandado todavía.

Y si alguna vez se toca un archivo del paquete, hay que rehacer este chequeo,
porque las dos propuestas afirman las líneas de cada archivo y los números
envejecen solos:

```bash
cd ~/eth-crypto-study/tooling/hax-lean/mini-stf
git ls-files . | while read f; do printf "%6s  %s\n" "$(wc -l < "$f")" "$f"; done
```
