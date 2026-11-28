module
import all OmegaChecks.InitInventory.Reductions
import OmegaChecks.InitInventory.EnvelopePublicTypes
import OmegaChecks.InitPort.StrictReplay
meta import OmegaChecks.InitInventory.Reductions
meta import OmegaChecks.InitInventory.EnvelopePublicTypes
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

/-- These comparisons retain a universal relation-respect argument even after public reduction.
Its type is equivalent at universe zero to propositional extensionality. -/
private def checkOrder (original visible evidence strict full : Environment) : IO Unit := do
  let proof := `Lean.Grind.IntModule.OfNatModule.instLEQOfOrderedAdd._proof_3
  let forward := ``EnvelopeOrder.propextFromModuleLift
  let reverse := ``EnvelopeOrder.moduleLiftFromPropext
  let targetOwner := owner.replacePrefix `Init `OmegaInit
  let some coherence := visible.find? proof | throw <| IO.userError "missing pinned coherence"
  let some ext := evidence.find? ``propext | throw <| IO.userError "missing extensionality type"
  let needed := coherence.type.instantiateLevelParams coherence.levelParams [.zero]
  let conversion := mkConst reverse [.zero]
  let .ok result := Kernel.check evidence {} conversion | throw <| IO.userError "invalid coherence witness"
  unless Kernel.isDefEqGuarded evidence {} result (.forallE .anonymous ext.type needed .default) do
    throw <| IO.userError "wrong extensionality-to-coherence theorem"
  let mut kernel := full.toKernelEnv
  for witness in [forward, reverse] do
    kernel ← restoreEvidence evidence kernel witness
  let _ ← replayStrict kernel #[portName forward, portName reverse]
  for suffix in ["mk_le_mk", "toQ_le", "toQ_lt"] do
    let name := instanceName.getPrefix.str suffix
    let some src := original.find? name | throw <| IO.userError s!"missing pinned {name}"
    let some dst := strict.find? (portName name) | continue
    let pinned := src.type.instantiateLevelParams src.levelParams (dst.levelParams.map Level.param)
    let instanceSuffix := if suffix == "toQ_lt" then "instLTQOfOrderedAdd" else "instLEQOfOrderedAdd"
    let instanceName := proof.getPrefix.getPrefix.str instanceSuffix
    let translated := translate portName pinned
    if (Kernel.check strict {} translated).isOk && Kernel.isDefEqGuarded strict {} translated dst.type then continue
    let missing := translated.getUsedConstants.filter (!strict.contains ·)
    unless missing == #[portName instanceName] && typeNeedsConstant visible src.type instanceName &&
        strict.getModuleIdxFor? dst.name == strict.getModuleIdx? targetOwner &&
        (full.find? dst.name).any (fun c => c.isTheorem && !c.isUnsafe && !c.isPartial) &&
        (Kernel.check strict {} dst.type).isOk &&
        OmegaChecks.InitInventory.EnvelopePublicTypes.representativeTypeMatches original strict pinned dst.type do
      throw <| IO.userError s!"unverified representative comparison {name}"
    unless (← OmegaChecks.InitInventory.EnvelopePublicTypes.orderCoherenceGap? visible strict evidence owner src).isSome do
      throw <| IO.userError s!"missing public coherence requirement for {name}"
    let _ ← replayStrict kernel #[dst.name]
    IO.println (toJson #[owner.toString, name.toString, instanceName.toString, proof.toString,
      forward.toString, reverse.toString]).compress

/-- The public addition, scalar multiplication and zero equations project from
the canonical integer module. For the specified operations on natural-number
pairs its cancellation law would equate representatives (1,1) and (0,0).
The strict library exports specialized equations for their representative images. -/
public unsafe def main (args : List String) : IO Unit := do
  let lib :: options := args | throw <| IO.userError "expected a strict library"
  unless options.isEmpty || options == ["order"] do throw <| IO.userError "unknown envelope check"
  initSearchPath (← findSysroot)
  let evidence ← importModules #[{module := `OmegaChecks.InitInventory.Reductions, importAll := true}] {}
  let visible ← importModules #[{module := owner}] {} (level := .exported)
  let original ← importModules #[{module := owner, importAll := true},
    {module := `Init.GrindInstances.Ring.Nat, importAll := true}] {}
  let targetOwner := owner.replacePrefix `Init `OmegaInit
  searchPathRef.set [lib]
  let strict ← importModules #[{module := targetOwner}] {} (level := .exported)
  let fullImports : Array Import := #[{module := targetOwner, importAll := true}]
  let fullImports := if options == ["order"] then fullImports.push {module := `OmegaInit.Data.Bool, importAll := true}
    else fullImports
  let full ← importModules fullImports {}
  if options == ["order"] then return ← checkOrder original visible evidence strict full
  if full.contains (portName instanceName) then return
  let some operation := original.find? instanceName | throw <| IO.userError "missing pinned module instance"
  let some refuter := RepresentativeQuotient.refuter? owner instanceName
    | throw <| IO.userError "missing cancellation counterexample"
  RepresentativeQuotient.certify original evidence operation refuter
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
