module
import all OmegaChecks.InitInventory.Reductions
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitPort.StrictReplay

open Lean Meta InitKernelPort OmegaChecks.InitPort OmegaChecks.InitBoundaries

/-- Recover the public selector from the endpoint at arbitrary parameters. -/
private def recover (source op : ConstantInfo) : MetaM Unit := do
  let levels := source.levelParams.map Level.param
  forallTelescope source.type fun _ body => do
    let lhs ← if source.name == ``Order.flat_csup_is_sup then do
      unless body.getAppFn.isConstOf ``Order.is_sup do throwError "missing supremum law"
      pure body.appArg!
    else
      let some (_, left, _) := body.eq? | throwError "expected an equality"
      pure left
    unless lhs.getAppFn.isConstOf op.name && lhs.getAppArgs.all Expr.isFVar do
      throwError "specialized selector in {source.name}"
    let whole ← mkLambdaFVars lhs.getAppArgs lhs
    let env ← getEnv
    let ty ← ofExceptKernelException (Kernel.check env {} whole)
    unless !whole.hasFVar && Kernel.isDefEqGuarded env {} whole (mkConst op.name levels) &&
        Kernel.isDefEqGuarded env {} ty (op.type.instantiateLevelParams op.levelParams levels) do
      throwError "failed to recover unrestricted {op.name} from {source.name}"

/-- Abstract exactly the selector in the checked official observation and compare the
resulting reduction with the witness that will replay in the strict kernel. -/
private def checkReduction (op observation proof ax : ConstantInfo) : MetaM Unit := do
  let [u] := proof.levelParams.map Level.param | throwError "expected one choice universe"
  let levels := [if op.name == ``Order.flat_csup then u.succ else u]
  let pinned := mkConst op.name levels
  let behavior ← ofExceptKernelException (Kernel.check (← getEnv) {} (mkConst observation.name [u]))
  unless observation.isTheorem && observation.numLevelParams == 1 && (behavior.find? (· == pinned)).isSome do
    throwError "official observation does not use {pinned}"
  withLocalDeclD `select (op.type.instantiateLevelParams op.levelParams levels) fun select => do
    let condition := behavior.replace fun e => if e == pinned then some select else none
    let expected ← mkForallFVars #[select] (← mkArrow condition (ax.type.instantiateLevelParams ax.levelParams [u]))
    unless ax.isAxiom && Kernel.isDefEqGuarded (← getEnv) {} proof.type expected do
      throwError "{proof.name} must derive choice from {op.name} satisfying {observation.name}"

public def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected a strict library"
  initSearchPath (← findSysroot)
  let system ← searchPathRef.get
  let evidence ← importModules #[{module := `OmegaChecks.InitInventory.Reductions, importAll := true}] {}
  let some ax := evidence.find? ``Classical.choice | throw <| IO.userError "missing choice"
  for (owner, name, dep, law, witness, equivalence) in [
      (`Init.Data.Option.Lemmas, ``Option.choice_eq_some, ``Option.choice, ``Option.isSome_choice,
        ``OptionSelector.fromSome, ``OptionSelector.eqSomeIff),
      (`Init.Data.Option.Lemmas, ``Option.choice_eq_default, ``Option.choice, ``Option.isSome_choice,
        ``OptionSelector.fromSome, ``OptionSelector.eqDefaultIff),
      (`Init.Internal.Order.Basic, ``Order.flat_csup_eq, ``Order.flat_csup, ``InternalOrder.officialFlatPresence,
        ``InternalOrder.choiceFromFlatPresence, ``InternalOrder.FlatSelection.eqIffChainLaw),
      (`Init.Internal.Order.Basic, ``Order.flat_csup_is_sup, ``Order.flat_csup, ``InternalOrder.officialFlatPresence,
        ``InternalOrder.choiceFromFlatPresence, ``InternalOrder.FlatSelection.smallChainSelections)] do
    let target := owner.replacePrefix `Init `OmegaInit
    unless ← (modToFilePath lib target "olean").pathExists do continue
    searchPathRef.set system
    let pub ← importModules #[{module := owner}] {} (level := .exported)
    let pinned ← importModules #[{module := owner, importAll := true}] {}
    let some src := pinned.find? name | throw <| IO.userError s!"missing {name}"
    let some op := pub.find? dep | throw <| IO.userError s!"missing {dep}"
    let some obs := evidence.find? law | throw <| IO.userError s!"missing {law}"
    let some proof := evidence.find? witness | throw <| IO.userError s!"missing {witness}"
    unless src.isTheorem && !src.isUnsafe && !src.isPartial && (pub.find? name).any (·.type.equal src.type) &&
        pub.getModuleIdxFor? name == pub.getModuleIdx? owner && pub.getModuleIdxFor? dep == pub.getModuleIdx? owner &&
        (Kernel.check pub {} src.type).isOk && typeNeedsConstant pub src.type dep do
      throw <| IO.userError s!"invalid official public formation for {name}"
    ((recover src op).run').toIO' {fileName := "<selector endpoint>", fileMap := default} {env := pub}
    ((checkReduction op obs proof ax).run').toIO' {fileName := "<selector behavior>", fileMap := default} {env := evidence}
    searchPathRef.set [lib]
    let strict ← importModules #[{module := target}] {} (level := .exported)
    let full ← importModules #[{module := target, importAll := true}] {}
    if strict.contains (portName name) || strict.contains (portName dep) then continue
    let raw := translate portName src.type
    unless !full.contains (portName name) && !full.contains (portName dep) &&
        raw.getUsedConstants.contains (portName dep) && !(Kernel.check strict {} raw).isOk do
      throw <| IO.userError s!"invalid strict signature for {name}"
    let roots := #[witness, equivalence] ++
      (if dep == ``Order.flat_csup then #[``InternalOrder.FlatSelection.propSupLaw] else #[])
    let kernel ← roots.foldlM (restoreEvidence evidence) full.toKernelEnv
    let _ ← replayStrict kernel (roots.map portName)
    IO.println (toJson #[owner.toString, name.toString, dep.toString, law.toString, witness.toString]).compress
