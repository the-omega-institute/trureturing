import LeanInformationAudit.Registry
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog

/- L0 原型 -/
namespace LeanInformationAudit.ContractPrototype
open Lean Meta

structure CompanionInput where
  input : RegistrationInput
  bridge : Expr
  target : Expr
  variation : Option Expr
  positive : Option Expr

structure Snapshot where
  registrations : Array (Name × RegistrationInput) := #[]
  enrollments : Array (Name × TemplateEnrollmentInput) := #[]
  seals : Array (Name × SealInput) := #[]
  roots : Array (Name × RootCatalogContract) := #[]
  expected : Array (Name × ExpectedOccurrence) := #[]
  companions : Array (Name × CompanionInput) := #[]
  scanned : Nat := 0
  hits : Nat := 0
  elapsedMs : Nat := 0

private def closed (e : Expr) : Bool :=
  !e.hasFVar && !e.hasMVar && !e.hasLooseBVars && !e.hasLevelMVar

private def fields (name : Name) (e : Expr) (count : Nat) : MetaM (Array Expr) := do
  let value ← whnfD e
  unless value.getAppFn.constName? == some (name.str "mk") do
    throwError "unclassified_form:contract.constructor:{name}"
  let args := value.getAppArgs
  unless args.size ≥ count do throwError "incomplete_closure:contract.fields:{name}"
  return args.extract (args.size - count) args.size

private def metadata (α : Type) (name : Name) (e : Expr) : MetaM α := do
  unless closed e do throwError "incomplete_closure:contract.metadata_open:{name}"
  unsafe evalExpr α (mkConst name) e

private def ref (e : Expr) : MetaM (Name × Expr) := do
  let fs ← fields ``Contract.Ref e 2
  let name ← metadata Name ``Name fs[0]!
  let value := fs[1]!
  unless closed value do throwError "incomplete_closure:contract.reference_open:{name}"
  unless name.isAnonymous do
    unless value.getAppFn.constName? == some name do
      throwError "unclassified_form:contract.reference_identity:{name}"
    discard <| getConstInfo name
  return (name, value)

private def optional (e : Expr) : MetaM (Option Expr) := do
  let e ← whnfD e
  if e.isAppOf ``Option.none then return none
  if e.isAppOf ``Option.some then return some e.getAppArgs.back!
  throwError "unclassified_form:contract.option"

private def optionalRef (e : Expr) : MetaM (Option (Name × Expr)) := do
  (← optional e).mapM ref

private def arrayValues (e : Expr) : MetaM (Array Expr) := do
  if let some values ← getArrayLit? e then return values
  let e ← whnfD e
  unless e.isAppOf ``Array.mk do throwError "unclassified_form:contract.array"
  let some values ← getListLit? e.getAppArgs.back!
    | throwError "unclassified_form:contract.array_list"
  return values

private def sourceSelection (e : Expr) : MetaM SourceSelection := do
  let s ← metadata Contract.SourceSelection ``Contract.SourceSelection e
  return {
    owner := s.owner
    definition := s.definition.map fun d => { owner := d.owner, name := d.name, path := d.path }
    coordinates := s.coordinates
    readouts := s.readouts.map fun r => {
      path := r.path, stateBinder := r.stateBinder, functionOperand := r.functionOperand
      stateOperand := r.stateOperand, booleanPredicate := r.booleanPredicate }
  }

private def continuation (e : Expr) : MetaM (Bool × Option Expr) := do
  let e ← whnfD e
  if e.isAppOf ``Contract.Continuation.absent then return (false, none)
  if e.isAppOf ``Contract.Continuation.unknown then return (true, none)
  if e.isAppOf ``Contract.Continuation.evidence then
    return (false, some (← ref e.getAppArgs.back!).2)
  throwError "unclassified_form:contract.continuation"

private def checkTarget (name : Name) (value : Expr) : MetaM ConstantInfo := do
  unless value.isConst && value.constName! == name do
    throwError "unclassified_form:contract.target_identity:{name}"
  let info ← getConstInfo name
  unless info.isTheorem && closed info.type do
    throwError "unclassified_form:contract.target_theorem:{name}"
  unless ← isDefEq (← inferType value)
      (info.type.instantiateLevelParams info.levelParams value.constLevels!) do
    throwError "unclassified_form:contract.target_statement:{name}"
  return info

private def registration (owner : Name) (info : DefinitionVal) (source : String)
    (roots : Array (Name × RootCatalogContract)) : MetaM CompanionInput := do
  let fs ← fields ``Contract.Registration info.value 14
  let theoremName ← metadata Name ``Name fs[0]!
  let typeArgs := info.type.getAppArgs
  unless typeArgs.size ≥ 2 do throwError "incomplete_closure:contract.target"
  discard <| checkTarget theoremName typeArgs[1]!
  let (arenaName, _) ← ref fs[1]!
  let (objectArenaName, _) ← ref fs[2]!
  unless !arenaName.isAnonymous && !objectArenaName.isAnonymous do
    throwError "unclassified_form:contract.arena_identity"
  let catalog ← metadata Name ``Name fs[3]!
  let localNames ← metadata Bool ``Bool fs[4]!
  let implementation ← whnfD fs[5]!
  let implementationArgs := implementation.getAppArgs
  let bridgeField := if implementation.isAppOf ``Contract.Implementation.witness then
    implementationArgs[implementationArgs.size - 2]! else implementationArgs.back!
  let (suppliedName, bridge) ← ref bridgeField
  let bridgeType ← whnfR (← inferType bridge)
  let sourceBound := bridgeType.isAppOfArity
    `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration 2
  let occurrence := !sourceBound && !localNames
  let family ← optionalRef fs[12]!
  let env ← getEnv
  let localName (suffix : String) :=
    match (roots.find? (fun (module, _) => module == owner)).bind (·.2.companionPrefix) with
    | some companionPrefix => companionPrefix ++ theoremName.str suffix
    | none => localCompanionName env owner theoremName suffix
  let unitName := if sourceBound then
      catalogQualifiedName owner arenaName .anonymous theoremName theoremUnitSuffix
    else if localNames then localName theoremUnitSuffix
    else catalogQualifiedName owner objectArenaName catalog theoremName theoremUnitSuffix
  let realizationName := if sourceBound || (localNames && !suppliedName.isAnonymous) then suppliedName
    else if localNames then localName primitiveRealizationSuffix
    else catalogQualifiedName owner objectArenaName catalog theoremName primitiveRealizationSuffix
  unless !realizationName.isAnonymous do throwError "unclassified_form:contract.bridge_identity"
  let descriptor ← optional fs[6]!
  let witness := implementation.isAppOf ``Contract.Implementation.witness
  let primitives := if sourceBound then none else some
    implementationArgs[implementationArgs.size - (if witness then 3 else 2)]!
  let positive := if witness then some implementationArgs.back! else none
  let variation ← optionalRef fs[7]!
  let sensitivity ← optionalRef fs[8]!
  let origin ← optional fs[9]!
  let selection ← (← optional fs[10]!).mapM sourceSelection
  let (openContinuation, residual) ← continuation fs[11]!
  let options ← metadata Options ``Options fs[13]!
  let entry : InformationRegistryEntry := {
    theoremName, unitName, arenaName, realizationName
    catalogId := if occurrence then catalog else .anonymous
    registrationModuleName := owner
    objectArenaName := if sourceBound || occurrence then objectArenaName else .anonymous
    localRegistrationNames := localNames
    sourceBound, resolvedArenaName := if sourceBound then arenaName else .anonymous
    variationWitness := variation.map Prod.fst |>.getD .anonymous
    sensitivityWitness := sensitivity.map Prod.fst |>.getD .anonymous }
  let declaration := if descriptor.isSome || selection.isSome || origin.isSome ||
      openContinuation || residual.isSome then some {
      theoremName, arena := if occurrence then objectArenaName else arenaName
      descriptor, sourceRecord := if sourceBound then some suppliedName else family.map Prod.fst
      escapeInput := {
        sourceSelection := selection
        finiteBridge := if family.isSome then some suppliedName else none
        fromObject := origin, continuation := residual, openContinuation }
      : TemplateBinding.ResolvedDeclaration } else none
  return {
    input := {
      entry, sourceText := source, options, suppliedPrimitives := primitives, declaration
      realizationSource := if !sourceBound && realizationName != suppliedName &&
          !suppliedName.isAnonymous then some suppliedName else none }
    bridge, target := typeArgs[1]!, variation := variation.map Prod.snd, positive }

private def expectedRow (e : Expr) : MetaM SnapshotOccurrence := do
  let fs ← fields ``Contract.ExpectedOccurrence e 6
  let theoremName ← metadata Name ``Name fs[2]!
  let info ← checkTarget theoremName fs[1]!
  let objectArenaName ← metadata Name ``Name fs[3]!
  discard <| getConstInfo objectArenaName
  let statementIdentity ← do
    unsafe evalExpr (Option String) (← inferType fs[4]!) fs[4]!
  let registrationModuleName ← metadata Name ``Name fs[5]!
  return {
    theoremName, objectArenaName
    statementIdentity := statementIdentity.getD ""
    capturedStatement := if statementIdentity.isSome then none else some info.type
    registrationModuleName }

private def rootCatalog (e : Expr) : MetaM RootCatalogContract := do
  let outer ← fields ``Contract.RootCatalog e 1
  let fs ← fields ``Contract.RootCatalogData outer[0]! 5
  let rootId ← metadata Name ``Name fs[0]!
  let expected ← (← arrayValues fs[1]!).mapM expectedRow
  let source ← (← arrayValues fs[2]!).mapM expectedRow
  let baseline ← (← arrayValues fs[3]!).mapM expectedRow
  let companionPrefix ← do
    unsafe evalExpr (Option Name) (← inferType fs[4]!) fs[4]!
  return { rootId, expected, source, baseline, companionPrefix }

private def enrollment (owner : Name) (info : DefinitionVal) (source : String) :
    MetaM TemplateEnrollmentInput := do
  let fs ← fields ``Contract.TemplateEnrollment info.value 4
  let name ← metadata Name ``Name fs[0]!
  let args := info.type.getAppArgs
  unless args.size ≥ 2 && args[1]!.getAppFn.constName? == some name do
    throwError "unclassified_form:contract.template_identity:{name}"
  discard <| getConstInfo name
  let version ← metadata Nat ``Nat fs[1]!
  let constructors ← (← arrayValues fs[2]!).mapM fun e => do
    let fs ← fields ``Contract.TypeRef e 2
    let name ← metadata Name ``Name fs[0]!
    unless fs[1]!.getAppFn.constName? == some name do
      throwError "unclassified_form:contract.constructor_identity:{name}"
    discard <| getConstInfo name
    return name
  let options ← metadata Options ``Options fs[3]!
  return { owner, name, version, constructors, sourceText := source, options }

private def contractHeads : Array Name := #[
  ``Contract.Registration, ``Contract.TemplateEnrollment, ``Contract.RootCatalog,
  ``Contract.ExpectedDeclaration, ``Contract.Seal]

/-- Discover once from the actual owners in the requested Reg import union.
Only metadata is evaluated; mathematical terms remain original compiler Expr. -/
def discover (moduleNames : Array Name) : MetaM Snapshot := do
  let started ← IO.monoNanosNow
  let original ← getEnv
  let env := original.setExporting false
  let mut reachable : NameSet := {}
  for root in moduleNames do
    for owner in reachableModules env root do reachable := reachable.insert owner
  let mut result : Snapshot := {}
  setEnv env
  try
    for idx in [:env.header.moduleNames.size] do
      let owner := env.header.moduleNames[idx]!
      unless reachable.contains owner && (`Reg).isPrefixOf owner do continue
      let mut candidates : Array (Nat × Nat × Name × DefinitionVal) := #[]
      for name in env.header.moduleData[idx]!.constNames do
        result := { result with scanned := result.scanned + 1 }
        let some info := env.find? name | throwError "incomplete_closure:contract.constant:{name}"
        unless contractHeads.contains (info.type.getAppFn.constName?.getD .anonymous) do continue
        unless (env.getModuleIdxFor? name).map (·.toNat) == some idx do
          throwError "incomplete_closure:contract.owner:{name}"
        let .defnInfo value := info | throwError "unclassified_form:contract.definition:{name}"
        unless value.safety == .safe && closed value.type && closed value.value do
          throwError "unclassified_form:contract.open_definition:{name}"
        let some ranges ← findDeclarationRanges? name
          | throwError "incomplete_closure:contract.source_range:{name}"
        candidates := candidates.push (ranges.range.pos.line, ranges.range.pos.column, name, value)
      unless candidates.isEmpty do
        let source ← IO.FS.readFile (← ArenaProvenance.moduleSource owner)
        candidates := candidates.qsort fun a b =>
          a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 ||
            (a.2.1 == b.2.1 && Name.quickLt a.2.2.1 b.2.2.1)))
        for (_, _, _, info) in candidates do
          if info.type.getAppFn.constName? == some ``Contract.RootCatalog then
            result := { result with roots := result.roots.push (owner, ← rootCatalog info.value) }
        for (_, _, _, info) in candidates do
          let head := info.type.getAppFn.constName!
          if head == ``Contract.Registration then
            let payload ← registration owner info source result.roots
            result := { result with
              registrations := result.registrations.push (owner, payload.input)
              companions := result.companions.push (owner, payload) }
          else if head == ``Contract.TemplateEnrollment then
            result := { result with enrollments := result.enrollments.push (owner, ← enrollment owner info source) }
          else if head == ``Contract.RootCatalog then
            pure ()
          else if head == ``Contract.ExpectedDeclaration then
            let fs ← fields ``Contract.ExpectedDeclaration info.value 2
            let expectedRoot ← metadata Name ``Name fs[0]!
            let row ← expectedRow fs[1]!
            result := { result with expected := result.expected.push (owner, {
              rootId := expectedRoot, theoremName := row.theoremName, objectArenaName := row.objectArenaName
              statementIdentity := row.statementIdentity, capturedStatement := row.capturedStatement
              registrationModuleName := row.registrationModuleName }) }
          else
            let fs ← fields ``Contract.Seal info.value 2
            result := { result with seals := result.seals.push (owner, {
              rootId := ← metadata Name ``Name fs[0]!
              options := ← metadata Options ``Options fs[1]! }) }
          result := { result with hits := result.hits + 1 }
    result := { result with elapsedMs := ((← IO.monoNanosNow) - started) / 1000000 }
    if (← IO.getEnv "STRATALINT_INSPECTOR_PROFILE") == some "1" then
      (← IO.getStderr).putStrLn s!"LEAN_INSPECTOR_PROFILE contract_scanned={result.scanned} contract_hits={result.hits} discovery_ms={result.elapsedMs}"
    return result
  finally setEnv original

end LeanInformationAudit.ContractPrototype
