module
meta import OmegaChecks.InitInventory.TransformerLaws
import OmegaChecks.InitInventory.TransformerLaws
meta import OmegaChecks.InitPort.StrictReplay
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.Translation
open Lean InitKernelPort

/-- Import the proof helpers from the inventory and use the existing strict declarations for Init. -/
private partial def restoreEvidence (source : Environment) (kernel : Kernel.Environment)
    (n : Name) : IO Kernel.Environment := do
  let name := portName n
  if (kernel.find? name).isSome then return kernel
  let some proof := source.find? n | throw <| IO.userError s!"missing source {n}"
  let some modIdx := source.getModuleIdxFor? n | throw <| IO.userError s!"missing module {n}"
  unless (`OmegaChecks.InitInventory).isPrefixOf source.header.moduleNames[modIdx.toNat]! do
    throw <| IO.userError s!"missing strict dependency {name}"
  let mut kernel := kernel
  for dep in proof.getUsedConstantsAsSet do
    kernel ← restoreEvidence source kernel dep
  let type := translate portName proof.type
  let some body := proof.value? (allowOpaque := true) | throw <| IO.userError s!"missing proof body {n}"
  let value := translate portName body
  let decl ← match proof with
    | .thmInfo t => pure (Declaration.thmDecl {t with name, type, value, all := [name]})
    | .defnInfo d => pure (Declaration.defnDecl {d with name, type, value, all := [name]})
    | _ => throw <| IO.userError s!"unsupported witness dependency {name}"
  let .ok next := kernel.addDeclCore 0 1000 decl none | throw <| IO.userError s!"failed to check evidence {name}"
  return next

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
    kernel ← restoreEvidence source kernel witness
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
