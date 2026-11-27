module
meta import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.Translation
meta import OmegaChecks.InitInventory.RangeIndex
import OmegaChecks.InitInventory.RangeIndex

open Lean InitKernelPort OmegaChecks.InitBoundaries

/-- Use the strict range implementations when replaying the equivalence proofs. -/
public def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and JSON output"
  let sourceOwner := `Init.Data.Range.Polymorphic.NatLemmas
  let evidenceModule := `OmegaChecks.InitInventory.RangeIndex
  let source ← importModules #[{module := evidenceModule}] {} (level := .private)
  searchPathRef.set [lib]
  let strict ← importModules #[{module := sourceOwner.replacePrefix `Init `OmegaInit}] {} (level := .private)
  let mut kernel := strict.toKernelEnv
  let evidenceDecls := source.header.moduleData[(source.getModuleIdx? evidenceModule).get!]!.constants
  let includes (n : Name) := source.getModuleIdxFor? n == source.getModuleIdx? evidenceModule
  let mut pending := evidenceDecls.toList.filter (fun ci => ci.name != `OmegaChecks.InitBoundaries.RangeIndex.equivalences)
  while !pending.isEmpty do
    let mut rest := []
    for proof in pending do
      if proof.getUsedConstantsAsSet.toList.any (fun n => includes n && (kernel.find? (portName n)).isNone) then
        rest := proof :: rest
        continue
      let name := portName proof.name
      let some original := proof.value? (allowOpaque := true) | throw <| IO.userError s!"missing body {name}"
      let type := translate portName proof.type
      let value := translate portName original
      let definition ← match proof with
        | .thmInfo th => pure (Declaration.thmDecl {th with name, type, value, all := [name]})
        | .defnInfo d => pure (Declaration.defnDecl {d with name, type, value, all := [name]})
        | _ => throw <| IO.userError s!"unsupported evidence declaration {name}"
      let .ok next := kernel.addDeclCore 0 1000 definition none
        | throw <| IO.userError s!"failed to check translated evidence {name}"
      kernel := next
    if rest.length == pending.length then throw <| IO.userError "cyclic witness dependency"
    pending := rest
  let mut rows := #[]
  let mut roots := #[]
  for (name, condition, witness) in RangeIndex.equivalences do
    let some src := source.find? name | throw <| IO.userError s!"missing official {name}"
    let some proof := kernel.find? (portName witness) | throw <| IO.userError s!"missing {witness}"
    let expected := mkApp2 (mkConst `Omega.Iff) (translate portName src.type) (mkConst (portName condition))
    unless src.levelParams.isEmpty && proof.levelParams.isEmpty && source.getModuleIdxFor? name == source.getModuleIdx? sourceOwner && proof.type == expected do
      throw <| IO.userError s!"incorrect complete equivalence {name}"
    rows := rows.push #[sourceOwner.toString, name.toString, condition.toString, (portName witness).toString]
    roots := roots.push (portName witness)
  let count ← OmegaChecks.InitPort.replayStrict kernel roots
  IO.FS.writeFile output (toJson rows).compress
  IO.println s!"Fresh kernel replay of {roots.size} exact equivalences, {count} declarations, zero axioms."
