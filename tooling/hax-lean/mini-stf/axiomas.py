#!/usr/bin/env python3
"""Arma axiomas.txt a partir de la salida del build.

Uso, desde esta carpeta y FUERA del contenedor (adentro no hay python):

    python3 axiomas.py /ruta/al/build.log

`build.log` es la salida de `bash regenerar.sh`, que al final imprime un
`#print axioms` por cada teorema de teoremas/ProofObligations.lean.

El archivo que sale tiene dos partes, y las dos se generan del mismo log:

  1. cada teorema, con los axiomas que utiliza;
  2. cada axioma, con los teoremas donde aparece.
"""
import collections
import re
import sys
import textwrap

ESTANDAR = ("propext", "Classical.choice", "Quot.sound")

QUE_ES = {
    "ssz.FueraDeCapacidad.Insts.CoreFmtDebug.fmt":
        "la firma de `Debug::fmt` del error `FueraDeCapacidad`. La nombra "
        "cada `.expect()` sobre un `SszList` o un `SszBitlist`, para "
        "formatear el mensaje si aborta.",
    "core.Array.Insts.CoreHashHash.hash":
        "el hash de un array. Hace falta para usar `H256` como clave del "
        "`HashMap`.",
    "core.borrow.Borrow":
        "el trait `Borrow`, que pide la firma de `HashMap::get`.",
    "core.borrow.Borrow.Blanket":
        "la instancia general de `Borrow` (todo tipo se presta a si mismo).",
    "core.hash.BuildHasher":
        "el trait del fabricante de hashers del `HashMap`.",
    "std.collections.hash.map.HashMap.get":
        "la consulta al `HashMap` de raices a slots.",
    "std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher":
        "el hasher por defecto del `HashMap`.",
    "core.Array.Insts.CoreCmpOrd.cmp":
        "la comparacion de arrays: es el `<` entre dos `H256` que usa el "
        "ordenamiento de raices.",
    "std.collections.hash.map.HashMap.insert":
        "la insercion en el `HashMap` de raices a slots.",
    "std.collections.hash.map.HashMapKVRandomStateGlobal.new":
        "la creacion del `HashMap` de raices a slots.",
}

RAYA = "=" * 72
RAYITA = "-" * 72


def clase(ax):
    if ax in ESTANDAR:
        return "estandar"
    if "._native.decide.ax_" in ax:
        return "nativo"
    return "modelo"


def leer(log):
    texto = open(log).read()
    pares = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", texto, re.S)
    teoremas = []
    for nombre, lista in pares:
        axiomas = [a.strip() for a in lista.replace("\n", " ").split(",") if a.strip()]
        teoremas.append((nombre, axiomas))
    return teoremas


def envolver(nombres, sangria):
    return textwrap.wrap(", ".join(nombres), 72 - len(sangria),
                         initial_indent=sangria, subsequent_indent=sangria,
                         break_long_words=False, break_on_hyphens=False)


def parte_uno(teoremas):
    out = [RAYA, "PARTE 1 — QUE AXIOMAS UTILIZA CADA TEOREMA", RAYA, ""]
    for nombre, axiomas in teoremas:
        est = [a for a in ESTANDAR if a in axiomas]
        nat = sorted(a for a in axiomas if clase(a) == "nativo")
        mod = sorted(a for a in axiomas if clase(a) == "modelo")
        plural = "axioma" if len(axiomas) == 1 else "axiomas"
        out.append(f"TEOREMA {nombre}")
        out.append(f"  utiliza {len(axiomas)} {plural}:")
        out.append(f"    de Lean ({len(est)}): " + ", ".join(est))
        if nat:
            out.append(f"    nativos ({len(nat)}):")
            out += [f"      {a}" for a in nat]
        if mod:
            out.append(f"    modelos ({len(mod)}):")
            out += [f"      {a}" for a in mod]
        out.append("")
    return out


def parte_dos(teoremas):
    donde = collections.OrderedDict()
    for nombre, axiomas in teoremas:
        for a in axiomas:
            donde.setdefault(a, []).append(nombre)
    total = len(teoremas)

    def bloque(ax, que):
        ts = donde[ax]
        b = [f"AXIOMA {ax}", f"  aparece en {len(ts)} de {total} teoremas"]
        b += textwrap.wrap("que es: " + que, 70, initial_indent="  ",
                           subsequent_indent="    ")
        b.append("  teoremas donde aparece:")
        b += envolver(ts, "    ")
        b.append("")
        return b

    out = [RAYA, "PARTE 2 — EN QUE TEOREMAS APARECE CADA AXIOMA", RAYA, "",
           "Lo mismo que la parte 1, dado vuelta.", "",
           "OJO con como leerlo. Que un axioma aparezca en un teorema quiere decir",
           "que la demostracion pasa por codigo que lo NOMBRA. No quiere decir que la",
           "demostracion se apoye en lo que ese axioma hace. La diferencia esta",
           "explicada en la seccion \"La base de confianza\" de la propuesta.", "",
           RAYITA, "DE LEAN", RAYITA, ""]
    for a in ESTANDAR:
        ts = donde.get(a, [])
        faltan = [n for n, _ in teoremas if n not in ts]
        out.append(f"AXIOMA {a}")
        if faltan:
            out.append(f"  aparece en {len(ts)} de {total} teoremas: todos menos "
                       + ", ".join(faltan))
        else:
            out.append(f"  aparece en los {total} teoremas")
        out.append("")

    def por_uso(k):
        return sorted((a for a in donde if clase(a) == k),
                      key=lambda a: (-len(donde[a]), a))

    out += [RAYITA, "MODELOS (declaraciones sin contenido)", RAYITA, ""]
    for a in por_uso("modelo"):
        out += bloque(a, QUE_ES.get(a, "(sin descripcion: agregarla en axiomas.py)"))
    out += [RAYITA, "NATIVOS (cuentas que hizo el compilador)", RAYITA, ""]
    for a in por_uso("nativo"):
        f = a.replace("mini_stf.", "").split("._native")[0]
        out += bloque(a, f"una cota que el compilador calculo al traducir `{f}`.")

    solos = [n for n, ax in teoremas if all(clase(a) == "estandar" for a in ax)]
    out += [RAYITA, "TEOREMAS QUE SOLO USAN AXIOMAS DE LEAN", RAYITA, "",
            f"Son {len(solos)} de {total}.", ""]
    out += envolver(solos, "  ")
    out.append("")
    return out, donde


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    teoremas = leer(sys.argv[1])
    if not teoremas:
        sys.exit("no encontre ningun `depends on axioms` en ese log")
    if any("sorryAx" in ax for _, ax in teoremas):
        sys.exit("HAY sorryAx: algun teorema quedo sin demostrar")

    dos, donde = parte_dos(teoremas)
    nativos = sorted(a for a in donde if clase(a) == "nativo")
    mayor = max(len(ax) for _, ax in teoremas)

    cab = f"""BASE DE AXIOMAS DE CADA TEOREMA

Salida de los `#print axioms` de teoremas/ProofObligations.lean. La arma
axiomas.py a partir del log de `lake build`. Se entrega para que la base
de confianza se pueda leer sin tener que compilar.

Son {len(teoremas)} teoremas. Tiene dos partes:

  PARTE 1   cada teorema, con los axiomas que utiliza.
  PARTE 2   cada axioma, con los teoremas donde aparece.

Los axiomas son de tres clases:

  DE LEAN    los tres estandar (propext, Classical.choice, Quot.sound). Los
             usa cualquier demostracion clasica; no dicen nada sobre este
             codigo.
  NATIVOS    `_native.decide.ax_*`: el nucleo NO los chequeo, los computo el
             compilador. No salen de nuestro codigo ni del de ethlambda:
             salen de la biblioteca de tacticas de Aeneas
             (Tactic/Simproc/BvSimprocs.lean, Tactic/Step/StepArraySpec.lean),
             descargando cotas de arrays y escalares. No hay flag para
             apagarlos.
  MODELOS    declaraciones que existen solo para que las firmas chequeen.
             No tienen contenido: Lean no sabe que hacen.

Ningun teorema usa `sorryAx`, que es lo que apareceria si una demostracion
hubiera quedado incompleta.
"""
    cierre = [RAYA, "", f"NATIVOS DISTINTOS EN TODO EL BUILD: {len(nativos)}", ""]
    cierre += [f"  {a}" for a in nativos]
    cierre += ["", f"""Todos llegan a los teoremas sobre `state_transition` entera (`ST-3`,
`ST-4`, `ST-6`, `ST-7`, la conservacion del header, los invariantes de la
ventana y del historial, y la ausencia de panico), que dependen de
exactamente los mismos {mayor} axiomas que el `def` de `state_transition` sin
teorema de por medio (se ve con supuestos/RevisarAxiomas.lean). Los teoremas
sobre componentes dependen de menos.

Eran 24 hasta el 15 nov 2026 y 23 hasta el 17 nov: `core.mem.take` y
`core.bool.Bool.then` eran axiomas y pasaron a ser definiciones (ver
supuestos/FunsExternal.lean). Por eso `process_block_header` y todo lo que
pasa por ella tienen dos modelos menos que en la primera version de este
archivo."""]

    lineas = cab.split("\n") + parte_uno(teoremas) + dos + cierre
    open("axiomas.txt", "w").write("\n".join(lineas) + "\n")
    print(f"axiomas.txt: {len(teoremas)} teoremas, {len(donde)} axiomas distintos")


if __name__ == "__main__":
    main()
