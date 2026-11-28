module
import all OmegaChecks.InitInventory.Reductions
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitInventory.Reductions
meta import OmegaChecks.InitPort.StrictReplay

open Lean Meta InitKernelPort OmegaChecks.InitPort OmegaChecks.InitBoundaries

private def owner := `Init.Grind.Module.Envelope
private def instanceName := `Lean.Grind.IntModule.OfNatModule.ofNatModule

/-- Abstract the arguments at the actual occurrence in the published equation.
The resulting term must recover the entire polymorphic module instance. -/
private def checkOccurrence (source operation : ConstantInfo) : MetaM Unit := do
  let env ← getEnv
  let levels := source.levelParams.map Level.param
  forallTelescope source.type fun _ conclusion => do
    let some (_, _, right) := conclusion.eq? | throwError "expected an embedding equation"
    let some use := right.find? (fun e => e.isAppOfArity instanceName 2)
      | throwError "missing module instance at the right endpoint"
    let args := use.getAppArgs
    unless args.all Expr.isFVar do throwError "specialized module instance in {source.name}"
    let entire ← mkLambdaFVars args use
    let type ← ofExceptKernelException (Kernel.check env {} entire)
    unless !entire.hasFVar && Kernel.isDefEqGuarded env {} entire (mkConst instanceName levels) &&
        Kernel.isDefEqGuarded env {} type (operation.type.instantiateLevelParams operation.levelParams levels) do
      throwError "{source.name} does not use the complete instance"

/-- The public addition, scalar multiplication and zero equations project from
the canonical integer module. For the specified operations on natural-number
pairs its cancellation law would equate representatives (1,1) and (0,0).
The strict library exports specialized equations for their representative images. -/
public unsafe def main (args : List String) : IO Unit := do
  let [lib] := args | throw <| IO.userError "expected a strict library"
  initSearchPath (← findSysroot)
  let evidence ← importModules #[{module := `OmegaChecks.InitInventory.Reductions, importAll := true}] {}
  let visible ← importModules #[{module := owner}] {} (level := .exported)
  let original ← importModules #[{module := owner, importAll := true},
    {module := `Init.GrindInstances.Ring.Nat, importAll := true}] {}
  let some operation := original.find? instanceName | throw <| IO.userError "missing pinned module instance"
  let some refuter := RepresentativeQuotient.refuter? owner instanceName
    | throw <| IO.userError "missing cancellation counterexample"
  RepresentativeQuotient.certify original evidence operation refuter
  let targetOwner := owner.replacePrefix `Init `OmegaInit
  searchPathRef.set [lib]
  let strict ← importModules #[{module := targetOwner}] {} (level := .exported)
  let full ← importModules #[{module := targetOwner, importAll := true}] {}
  if full.contains (portName instanceName) then return
  let mut roots := #[]
  for suffix in ["toQ_add", "toQ_smul", "toQ_zero"] do
    let name := instanceName.getPrefix.str suffix
    let some src := visible.find? name | throw <| IO.userError s!"missing {name}"
    let some dst := strict.find? (portName name) | continue
    let pinned := translate portName src.type
    unless (original.find? name).any (fun c => c.isTheorem && c.type.equal src.type) &&
        visible.getModuleIdxFor? name == visible.getModuleIdx? owner &&
        (Kernel.check visible {} src.type).isOk && typeNeedsConstant visible src.type instanceName &&
        strict.getModuleIdxFor? dst.name == strict.getModuleIdx? targetOwner &&
        (full.find? dst.name).any (fun c => c.isTheorem && !c.isUnsafe && !c.isPartial) &&
        (Kernel.check strict {} dst.type).isOk &&
        pinned.getUsedConstants.filter (!strict.contains ·) == #[portName instanceName] do
      throw <| IO.userError s!"invalid pinned instance dependency for {name}"
    ((checkOccurrence src operation).run').toIO' {fileName := "<module embedding>", fileMap := default} {env := visible}
    roots := roots.push dst.name
  let _ ← replayStrict full.toKernelEnv roots
  for root in roots do
    IO.println (toJson #[owner.toString, (originalName root).toString, instanceName.toString, refuter.toString]).compress
