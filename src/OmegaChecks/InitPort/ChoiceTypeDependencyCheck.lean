module
import all Lean.Environment
import all OmegaChecks.InitInventory.Reductions
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.StrictReplay

open Lean InitKernelPort OmegaChecks.InitPort OmegaChecks.InitBoundaries

/-- Each statement uses an operation whose full public type yields choice. -/
private def sites : List (Name × Name × Name × Name) := [
  (`Init.Grind.Injective, `Lean.Grind.leftInv_eq, `Lean.Grind.leftInv, ``choiceFromLeftInv),
  (`Init.Control.Lawful.MonadAttach.Lemmas, `WeaklyLawfulMonadAttach.bind_attach_of_nonempty,
    `Classical.ofNonempty, ``choiceFromOfNonempty),
  (`Init.Data.Iterators.Consumers.Access, `Std.Iter.atIdxSlow?.eq_1,
    `WellFounded.extrinsicFix₂, ``choiceFromFix₂),
  (`Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect, `Std.IterM.toListRev.go.eq_1,
    `WellFounded.extrinsicFix₂, ``choiceFromFix₂),
  (`Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect, `Std.IterM.toArray.go.eq_1,
    `WellFounded.extrinsicFix₂, ``choiceFromFix₂),
  (`Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop, `Std.IterM.DefaultConsumers.forIn'.eq_1,
    `WellFounded.extrinsicFix₃, ``choiceFromFix₃),
  (`Init.Data.Range.Polymorphic.RangeIterator, `Std.Rxo.Iterator.instIteratorLoop.loop.eq_1,
    `WellFounded.extrinsicFix₃, ``choiceFromFix₃),
  (`Init.Data.Range.Polymorphic.RangeIterator, `Std.Rxi.Iterator.instIteratorLoop.loop.eq_1,
    `WellFounded.extrinsicFix₃, ``choiceFromFix₃),
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
    -- A left inverse for α → Option (PLift α) selects from α at none.
    let opLevels ← if dep == ``Lean.Grind.leftInv then do
      let [u] := levels | throw <| IO.userError "expected one universe for left-inverse choice"
      pure [u, u.succ]
    else pure levels
    let expected := Lean.mkForall `op .default (operation.type.instantiateLevelParams operation.levelParams opLevels)
      (ax.type.instantiateLevelParams ax.levelParams (levels.drop (levels.length - ax.numLevelParams)))
    unless ax.isAxiom && operation.numLevelParams == opLevels.length &&
        Kernel.isDefEqGuarded visible {} expected proof.type do
      throw <| IO.userError s!"{witness} must derive choice from the complete type of {dep}"
    searchPathRef.set [lib]
    let strict ← importModules #[{module := strictOwner}] {} (level := .exported)
    let full ← importModules #[{module := strictOwner, importAll := true}] {}
    let raw := translate portName src.type
    let missing := raw.getUsedConstants.filter fun d => !strict.contains d
    if !missing.contains (portName dep) then continue
    unless !full.contains (portName dep) do throw <| IO.userError s!"private strict operand {dep}"
    if let some dst := strict.find? (portName name) then
      unless (full.find? dst.name).any (fun ci => ci.isTheorem && !ci.isUnsafe && !ci.isPartial) &&
          strict.getModuleIdxFor? dst.name == strict.getModuleIdx? strictOwner &&
          (Kernel.check strict {} dst.type).isOk && missing == #[portName dep] do
        throw <| IO.userError s!"unexpected specialization of {dst.name}: {missing}"
    else if full.contains (portName name) then
      throw <| IO.userError s!"private strict implementation of {name}"
    let kernel ← restoreEvidence evidence full.toKernelEnv witness
    let _ ← replayStrict kernel #[portName witness]
    IO.println (toJson #[owner.toString, name.toString, dep.toString, witness.toString]).compress
