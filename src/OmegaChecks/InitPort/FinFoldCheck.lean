module
meta import OmegaChecks.InitInventory.TransformerLaws
import OmegaChecks.InitInventory.TransformerLaws
meta import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.Translation
open Lean InitKernelPort

/-- Replay the complete implications at arbitrary source and target universe levels. -/
public def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and JSON output"
  let owner := `Init.Data.Fin.Fold
  let source ← importModules #[{module := `OmegaChecks.InitInventory.TransformerLaws, importAll := true}] {} (level := .private)
  searchPathRef.set [lib]
  let strict ← importModules #[{module := `OmegaInit.Data.Fin.Fold}] {} (level := .private)
  let mut kernel := strict.toKernelEnv
  let some fe := source.find? `funext | throw <| IO.userError "missing official function extensionality"
  let mut roots := #[]
  let mut rows := #[]
  for (name, root) in [(`Fin.foldlM_succ_last, `funextOfLeftSuccessor), (`Fin.foldrM_succ, `funextOfRightSuccessor),
      (`Fin.foldlM_add, `funextOfLeftAddition), (`Fin.foldrM_add, `funextOfRightAddition)] do
    let witness := `OmegaChecks.InitBoundaries.TransformerLaws.FiniteFold ++ root
    kernel ← OmegaChecks.InitPort.restoreEvidence source kernel witness
    let some proof := kernel.find? (portName witness) | throw <| IO.userError s!"missing evidence {witness}"
    let some rule := source.find? name | throw <| IO.userError s!"missing {name}"
    let [u,v] := proof.levelParams.map Level.param | throw <| IO.userError "expected two universe parameters"
    let w := Level.max (.succ .zero) (.max u v)
    let dom := translate portName (rule.type.instantiateLevelParams rule.levelParams [w,w])
    let cod := translate portName (fe.type.instantiateLevelParams fe.levelParams [u,v])
    let expected := Expr.forallE .anonymous dom cod .default
    unless rule.isTheorem && rule.levelParams.length == 2 && fe.levelParams.length == 2 &&
        source.getModuleIdxFor? name == source.getModuleIdx? owner &&
        Kernel.isDefEqGuarded (.ofKernelEnv kernel) {} expected proof.type do
      throw <| IO.userError s!"incorrect strict type {witness}"
    roots := roots.push (portName witness)
    rows := rows.push #[owner.toString, name.toString, "funext", (portName witness).toString]
  let count ← OmegaChecks.InitPort.replayStrict kernel roots
  IO.FS.writeFile output (toJson rows).compress
  IO.println s!"Replayed {roots.size} original finite fold implications, {count} declarations, zero axioms."
