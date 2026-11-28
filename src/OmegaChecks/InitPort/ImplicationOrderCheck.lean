module
import all Lean.Environment
import all OmegaChecks.InitInventory.OriginalType
import all OmegaChecks.InitInventory.Reductions
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitInventory.Reductions
meta import OmegaChecks.InitInventory.OriginalType
meta import OmegaChecks.InitPort.StrictReplay

open Lean InitKernelPort OmegaChecks.InitPort OmegaChecks.InitBoundaries

public unsafe def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected a strict library"
  initSearchPath (← findSysroot)
  let evidence ← importModules #[{module := `OmegaChecks.InitInventory.Reductions, importAll := true}] {}
  let owner := `Init.Internal.Order.Basic
  let targetOwner := `OmegaInit.Internal.Order.Basic
  let visible ← importModules #[{module := owner}] {} (level := .exported)
  let source ← importModules #[{module := owner, importAll := true}] {}
  searchPathRef.set [lib]
  let strict ← importModules #[{module := targetOwner}] {} (level := .exported)
  let full ← importModules #[{module := targetOwner, importAll := true}] {}
  let some ax := source.find? ``propext | throw <| IO.userError "missing pinned propext"
  unless ax.isAxiom do throw <| IO.userError "expected the pinned propext axiom"
  let rules := InternalOrder.implicationOrders.filter fun (name, _) => name.getString! == "instOrder"
  let mut certificates : Array (Array String) := #[]
  let idx := (visible.getModuleIdx? owner).get!
  for name in visible.header.moduleData[idx]!.constNames do
    let some src := source.find? name | continue
    let n := portName src.name
    unless !isPrivateName src.name && !src.name.isInternalOrNum && !src.name.hasMacroScopes &&
        strict.getModuleIdxFor? n == strict.getModuleIdx? targetOwner do continue
    let some dst := strict.find? n | continue
    unless src.numLevelParams == dst.numLevelParams do continue
    let pinned := src.type.instantiateLevelParams src.levelParams (dst.levelParams.map Level.param)
    let expected := translate portName pinned
    let missing := expected.getUsedConstants.filter fun d => !strict.contains d
    let used := rules.filter fun (name, _) => missing.contains (portName name)
    unless !used.isEmpty && OmegaChecks.InitInventory.checkedOrderFields visible strict owner src pinned dst.type missing do continue
    for (name, proof) in used do
      unless typeNeedsConstant visible pinned name do
        throw <| IO.userError s!"could still form {src.name} without the pinned instance {name}"
      certificates := certificates.push #[owner.toString, src.name.toString, name.toString, proof.toString]
  if certificates.isEmpty then return
  let mut kernel := full.toKernelEnv
  let mut roots := #[]
  for (name, proof) in rules do
    let some order := source.find? name | throw <| IO.userError s!"missing pinned {name}"
    let some witness := evidence.find? proof | throw <| IO.userError s!"missing witness {proof}"
    -- For arbitrary candidate orders, compare their relation with the actual
    -- pinned relation for all propositions, in both directions of an equivalence.
    let expected ← (orderReductionType order ax).run' |>.toIO' {fileName := "<order relation>", fileMap := default} {env := source}
    unless source.getModuleIdxFor? name == source.getModuleIdx? owner &&
        Kernel.isDefEqGuarded source {} expected witness.type do
      throw <| IO.userError s!"witness {proof} does not preserve the pinned comparison relation"
    kernel ← restoreEvidence evidence kernel proof
    roots := roots.push (portName proof)
  let _ ← replayStrict kernel roots
  for certificate in certificates do IO.println (toJson certificate).compress
