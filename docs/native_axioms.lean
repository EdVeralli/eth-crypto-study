/-
Lista los teoremas del repo que dependen de *native axioms*: pasos en los que
Lean confia en codigo compilado (`native_decide`, `bv_decide`) en vez de
verificar con su kernel. Correr desde la raiz del repo:

    cd ~/eth-crypto-study
    lake env lean docs/native_axioms.lean

Tarda unos minutos porque carga Mathlib entero. Para un teorema suelto:
`#print axioms EthCryptographySpecs.Xmss.Blake2s.hash_abc`.
-/
import EthCryptographySpecs.Proofs
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n ci =>
    if (`EthCryptographySpecs).isPrefixOf n && ci matches .thmInfo _ && !n.isInternal
    then acc.push n else acc
  let mut afectados := 0
  for n in names.qsort (·.toString < ·.toString) do
    let axs ← collectAxioms n
    let nat := axs.filter (fun a => a.components.any (· == `_native))
    if nat.size > 0 then
      IO.println s!"{n}  ({nat.size} native axioms)"
      afectados := afectados + 1
  IO.println s!"TOTAL: {afectados} teoremas dependen de native axioms, de {names.size} revisados"
