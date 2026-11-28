module
import all OmegaChecks.InitInventory.Reductions
import OmegaChecks.InitInventory.EnvelopePublicTypes
import OmegaChecks.InitPort.EnvelopeNaturalPremises
meta import OmegaChecks.InitInventory.Reductions
meta import OmegaChecks.InitInventory.EnvelopePublicTypes
meta import OmegaChecks.InitPort.EnvelopeNaturalPremises

open Lean Meta InitKernelPort OmegaChecks.InitPort OmegaChecks.InitBoundaries

private def owner := `Init.Grind.Module.Envelope
private def instanceName := `Lean.Grind.IntModule.OfNatModule.ofNatModule
private def congruenceOwner := `Init.Grind.Module.OfNatModule

/-- Abstract the arguments at the actual occurrence in the published equation.
The resulting term must recover the entire polymorphic module instance. -/
private def checkOccurrence (source operation : ConstantInfo) : MetaM Unit := do
  let env ← getEnv
  let levels := source.levelParams.map Level.param
  forallTelescope source.type fun _ conclusion => do
    let index ← if source.name == instanceName.getPrefix.str "instNoNatZeroDivisorsQOfAddRightCancel" then do
      unless conclusion.isAppOfArity ``Grind.NoNatZeroDivisors 2 do throwError "expected the scalar cancellation class"
      let index := conclusion.appArg!
      unless index.isAppOfArity ``Grind.IntModule.toNatModule 2 && index.appArg!.isAppOfArity instanceName 2 do
        throwError "expected the natural module projection of the canonical integer module"
      pure index
    else do
      let some (_, _, right) := conclusion.eq? | throwError "expected an embedding equation"
      if source.name == instanceName.getPrefix.str "add_congr" ||
        source.name == instanceName.getPrefix.str "smul_congr" then do
        let op := if source.name.getString! == "add_congr" then ``HAdd.hAdd else ``HSMul.hSMul
        unless right.isAppOfArity op 6 && right.getAppArgs[4]!.isFVar && right.appArg!.isFVar do
          throwError "expected the quotient operation at the arbitrary arguments"
        pure right.getAppArgs[3]!
      else pure right
    let some use := index.find? (fun e => e.isAppOfArity instanceName 2)
      | throwError "missing module instance at the right endpoint"
    let args := use.getAppArgs
    unless args.all Expr.isFVar do throwError "specialized module instance in {source.name}"
    let entire ← mkLambdaFVars args use
    let type ← ofExceptKernelException (Kernel.check env {} entire)
    unless !entire.hasFVar && Kernel.isDefEqGuarded env {} entire (mkConst instanceName levels) &&
        Kernel.isDefEqGuarded env {} type (operation.type.instantiateLevelParams operation.levelParams levels) do
      throwError "{source.name} does not use the complete instance"

/-- A congruence is callable when its original type forms in the exported library.
For the two missing types inspect the instance in the arithmetic endpoint itself. -/
private def congruences (lib : System.FilePath) (systemPath : SearchPath) (operation : ConstantInfo)
    (refuter : Name) : IO Unit := do
  let target := congruenceOwner.replacePrefix `Init `OmegaInit
  unless ← (modToFilePath lib target "olean").pathExists do return
  searchPathRef.set systemPath
  let visible ← importModules #[{module := congruenceOwner}] {} (level := .exported)
  let pinned ← importModules #[{module := congruenceOwner, importAll := true}] {}
  searchPathRef.set [lib]
  let strict ← importModules #[{module := target}] {} (level := .exported)
  let full ← importModules #[{module := target, importAll := true}] {}
  for suffix in ["add_congr", "smul_congr"] do
    let n := instanceName.getPrefix.str suffix
    if strict.contains (portName n) then continue
    let some src := pinned.find? n | throw <| IO.userError s!"missing {n}"
    let translated := translate portName src.type
    unless src.isTheorem && !src.isUnsafe && !src.isPartial && src.numLevelParams == 1 &&
        (visible.find? n).any (·.type.equal src.type) && visible.getModuleIdxFor? n == visible.getModuleIdx? congruenceOwner &&
        (Kernel.check visible {} src.type).isOk && typeNeedsConstant visible src.type instanceName &&
        translated.getUsedConstants.filter (!strict.contains ·) == #[portName instanceName] &&
        !full.contains (portName instanceName) && !(Kernel.check strict {} translated).isOk do
      throw <| IO.userError s!"invalid quotient arithmetic endpoint {n}"
    ((checkOccurrence src operation).run').toIO' {fileName := "<module congruence>", fileMap := default} {env := visible}
    IO.println (toJson #[congruenceOwner.toString, n.toString, instanceName.toString, refuter.toString]).compress

private def scalarCancellation (lib : System.FilePath) (original visible evidence strict : Environment)
    (operation : ConstantInfo) (refuter : Name) : IO Unit := do
  let n := instanceName.getPrefix.str "instNoNatZeroDivisorsQOfAddRightCancel"
  let natRing := `OmegaInit.GrindInstances.Ring.Nat
  if strict.contains (portName n) || !(← (modToFilePath lib natRing "olean").pathExists) then return
  let full ← importModules #[{module := owner.replacePrefix `Init `OmegaInit, importAll := true},
    {module := natRing, importAll := true}, {module := `OmegaInit.GrindInstances.Nat, importAll := true}] {}
  let some src := original.find? n | throw <| IO.userError s!"missing {n}"
  let translated := translate portName src.type
  unless src.isTheorem && !src.isUnsafe && !src.isPartial && src.numLevelParams == 1 &&
      (visible.find? n).any (·.type.equal src.type) && visible.getModuleIdxFor? n == visible.getModuleIdx? owner &&
      (Kernel.check visible {} src.type).isOk && typeNeedsConstant visible src.type instanceName &&
      translated.getUsedConstants.filter (!strict.contains ·) == #[portName instanceName] &&
      !full.contains (portName instanceName) && !(Kernel.check strict {} translated).isOk do
    throw <| IO.userError s!"invalid scalar cancellation type {n}"
  ((checkOccurrence src operation).run').toIO' {fileName := "<module class index>", fileMap := default} {env := visible}
  let some observation := EnvelopeCancellation.observation? owner instanceName | throw <| IO.userError "missing module test"
  let some (.thmInfo proof) := evidence.find? observation | throw <| IO.userError "missing module cancellation proof"
  let some sample := proof.value.find? (·.isAppOfArity instanceName 2) | throw <| IO.userError "missing module in test"
  let canonical := mkApp2 (mkConst instanceName [.zero]) (mkConst ``Nat) EnvelopeNaturalPremises.natModule
  unless Kernel.isDefEqGuarded evidence {} sample canonical do throw <| IO.userError "different natural module in test"
  let ty ← ((EnvelopeNaturalPremises.specialize full src).run').toIO'
    {fileName := "<scalar cancellation premises>", fileMap := default} {env := original}
  let some use := ty.appArg!.find? (·.isAppOfArity instanceName 2) | throw <| IO.userError "missing module at Nat"
  unless Kernel.isDefEqGuarded original {} use canonical do throw <| IO.userError "different module in the class index"
  IO.println (toJson #[owner.toString, n.toString, instanceName.toString, refuter.toString]).compress

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
    {module := `Init.GrindInstances.Ring.Nat, importAll := true}, {module := `Init.GrindInstances.Nat, importAll := true}] {}
  let targetOwner := owner.replacePrefix `Init `OmegaInit
  let systemPath ← searchPathRef.get
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
  scalarCancellation lib original visible evidence strict operation refuter
  congruences lib systemPath operation refuter
