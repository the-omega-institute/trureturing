module
meta import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.Translation
meta import OmegaChecks.InitInventory.TransformerLaws
import OmegaChecks.InitInventory.TransformerLaws
meta import OmegaChecks.InitInventory.ConstraintReflection
import OmegaChecks.InitInventory.ConstraintReflection
meta import OmegaChecks.InitInventory.RangeIndex
import OmegaChecks.InitInventory.RangeIndex

open Lean InitKernelPort OmegaChecks.InitBoundaries

/-- Replay both directions at the full pinned types using the generated implementations. -/
public def main (args : List String) : IO Unit := do
  let lib :: output :: owners := args | throw <| IO.userError "expected strict library, JSON output and owners"
  let owners := if owners.isEmpty then [`Init.Data.Range.Polymorphic.NatLemmas] else owners.map String.toName
  let source ← importModules #[{module := `OmegaChecks.InitInventory.RangeIndex},
    {module := `OmegaChecks.InitInventory.ConstraintReflection, importAll := true},
    {module := `OmegaChecks.InitInventory.TransformerLaws, importAll := true}] {} (level := .private)
  searchPathRef.set [lib]
  let strict ← importModules (owners.toArray.map fun owner => {module := owner.replacePrefix `Init `OmegaInit}) {} (level := .private)
  let mut kernel := strict.toKernelEnv
  let laws := (``Lean.Omega.Constraint.combine_sat, ``ConstraintReflection.AndReflection,
    ``ConstraintReflection.equivalence) :: (RangeIndex.equivalences ++ TransformerLaws.ReturnImage.equivalences)
  let entries := laws.filter fun (name, _, _) =>
    owners.any fun owner => source.getModuleIdxFor? name == source.getModuleIdx? owner
  let mut rows := #[]
  let mut roots := #[]
  for (name, condition, witness) in entries do
    kernel ← OmegaChecks.InitPort.restoreEvidence source kernel witness
    let some ownerIdx := source.getModuleIdxFor? name | throw <| IO.userError s!"missing owner {name}"
    let sourceOwner := source.header.moduleNames[ownerIdx]!
    let some src := source.find? name | throw <| IO.userError s!"missing official {name}"
    let some proof := kernel.find? (portName witness) | throw <| IO.userError s!"missing {witness}"
    let some target := kernel.find? (portName condition) | throw <| IO.userError s!"missing {condition}"
    let levels := proof.levelParams.map Level.param
    let original := src.type.instantiateLevelParams src.levelParams levels
    let expected := mkApp2 (mkConst `Omega.Iff) (translate portName original) (mkConst (portName condition) levels)
    unless src.isTheorem && proof.isTheorem && src.levelParams.length == levels.length &&
        target.levelParams.length == levels.length && Kernel.isDefEqGuarded (.ofKernelEnv kernel) {} proof.type expected do
      throw <| IO.userError s!"incorrect complete equivalence {name}"
    rows := rows.push #[sourceOwner.toString, name.toString, condition.toString, (portName witness).toString]
    roots := roots.push (portName witness)
  let count ← OmegaChecks.InitPort.replayStrict kernel roots
  IO.FS.writeFile output (toJson rows).compress
  IO.println s!"Fresh kernel replay of {roots.size} exact equivalences, {count} declarations, zero axioms."
