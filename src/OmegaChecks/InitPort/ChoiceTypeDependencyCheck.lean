module
import all Lean.Environment
import all OmegaChecks.InitInventory.Reductions
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.StrictReplay

open Lean InitKernelPort OmegaChecks.InitPort OmegaChecks.InitBoundaries

/-- These two published equations use a polymorphic selector even though the strict
export has a constructive specialization. The witness consumes the selector's complete type. -/
private def sites : List (Name × Name × Name × Name) := [
  (`Init.Classical, `Classical.epsilon_singleton, `Classical.epsilon, ``choiceFromEpsilon),
  (`Init.Data.Range.Polymorphic.RangeIterator, `Std.Rxc.Iterator.instIteratorLoop.loop.eq_1,
    `WellFounded.extrinsicFix₃, ``choiceFromFix₃)]

public unsafe def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected a strict library"
  initSearchPath (← findSysroot)
  let officialPath ← searchPathRef.get
  let evidence ← importModules #[{module := `OmegaChecks.InitInventory.Reductions, importAll := true}] {}
  for (owner, name, dep, witness) in sites do
    let strictOwner := owner.replacePrefix `Init `OmegaInit
    if !(← (System.FilePath.mk lib / (strictOwner.toString.replace "." "/" ++ ".olean")).pathExists) then continue
    searchPathRef.set officialPath
    let visible ← importModules #[{module := owner}] {} (level := .exported)
    let some src := visible.find? name | throw <| IO.userError s!"missing official {name}"
    let official ← importModules #[{module := owner, importAll := true}] {}
    unless (official.find? name).any (·.isTheorem) &&
        visible.getModuleIdxFor? name == visible.getModuleIdx? owner &&
        (Kernel.check visible {} src.type).isOk && typeNeedsConstant visible src.type dep do
      throw <| IO.userError s!"the pinned public statement {name} does not require {dep}"
    let some operation := visible.find? dep | throw <| IO.userError s!"missing pinned {dep}"
    let some ax := visible.find? `Classical.choice | throw <| IO.userError "missing Classical.choice"
    let some proof := evidence.find? witness | throw <| IO.userError s!"missing {witness}"
    let levels := proof.levelParams.map Level.param
    let expected := Lean.mkForall `op .default (operation.type.instantiateLevelParams operation.levelParams levels)
      (ax.type.instantiateLevelParams ax.levelParams (levels.drop (levels.length - ax.numLevelParams)))
    unless ax.isAxiom && operation.numLevelParams == levels.length &&
        Kernel.isDefEqGuarded visible {} expected proof.type do
      throw <| IO.userError s!"{witness} must derive choice from the complete type of {dep}"
    searchPathRef.set [lib]
    let strict ← importModules #[{module := strictOwner}] {} (level := .exported)
    let some dst := strict.find? (portName name) | continue
    let full ← importModules #[{module := strictOwner, importAll := true}] {}
    let raw := translate portName src.type
    let missing := raw.getUsedConstants.filter fun d => !strict.contains d
    if missing.isEmpty then continue
    unless (full.find? dst.name).any (fun ci => ci.isTheorem && !ci.isUnsafe && !ci.isPartial) &&
        strict.getModuleIdxFor? dst.name == strict.getModuleIdx? strictOwner &&
        (Kernel.check strict {} dst.type).isOk && missing == #[portName dep] && !full.contains (portName dep) do
      throw <| IO.userError s!"unexpected declaration or missing operands at {dst.name}: {missing}"
    let kernel ← restoreEvidence evidence full.toKernelEnv witness
    let _ ← replayStrict kernel #[portName witness]
    IO.println (toJson #[owner.toString, name.toString, dep.toString, witness.toString]).compress
