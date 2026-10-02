import LeanInformationAudit.ContractPrototype.NameMapping

/- L0 原型 -/
namespace LeanInformationAudit.ContractPrototype.Equivalence
open Lean Meta TemplateAudit

def inEnvironment (env : Environment) (action : MetaM α) : MetaM α := do
  let saved ← getEnv
  setEnv (env.setExporting false)
  try withCurrHeartbeats action finally setEnv saved

private def result (value : Except String α) : MetaM α :=
  match value with
  | .ok value => pure value
  | .error message => throwError message

private def identity (source : Bool) (levels : List Name) (value : Expr) : MetaM String := withCurrHeartbeats do
  return (← result (← if source then compactIdentity levels value else rawIdentity levels value)).1

private def check (label : String) (actual expected : String) : MetaM Unit := do
  unless actual == expected do
    throwError "contract.equivalence:{label}: recomputed={actual} reported={expected}"

private def setJsonField (json : Json) (key : String) (value : Json) : MetaM Json := do
  let fields ← result json.getObj?
  unless (fields.toArray.any (·.1 == key)) do
    throwError "contract.equivalence:source_field_missing:{key}"
  return Json.mkObj (fields.toArray.toList.map fun (name, old) =>
    (name, if name == key then value else old))

def dependency (oldEnv newEnv : Environment) (mapping : NameMapping)
    (source : Bool) (input : DependencyIdentity) (rawDefinition : Bool := false) :
    MetaM DependencyIdentity := do
  let fingerprint := fun levels value => do
    if rawDefinition then return (← result (compactRawIdentity levels value)).1
    identity source levels value
  let oldInfo ← inEnvironment oldEnv <| getConstInfo input.name
  let oldType ← inEnvironment oldEnv <| fingerprint oldInfo.levelParams oldInfo.type
  check s!"dependency.old.type:{input.name}" oldType input.typeIdentity
  let oldBody ← inEnvironment oldEnv do
    if !rawDefinition && ((← isProp oldInfo.type) || (source && !Repository.isModule input.owner)) then return ""
    match oldInfo.value? with
    | none => pure ""
    | some value => fingerprint oldInfo.levelParams value
  check s!"dependency.old.body:{input.name}" oldBody input.bodyIdentity
  let name := renameName mapping input.name
  let owner := renameName mapping input.owner
  let mappedType := renameExpr mapping oldInfo.type
  let typeIdentity ← inEnvironment newEnv <| fingerprint oldInfo.levelParams mappedType
  let bodyIdentity ← inEnvironment newEnv do
    if !rawDefinition && ((← isProp mappedType) || (source && !Repository.isModule owner)) then return ""
    match oldInfo.value? with
    | none => pure ""
    | some value => fingerprint oldInfo.levelParams (renameExpr mapping value)
  return { name, owner, typeIdentity, bodyIdentity }

private def alignDependencies (mapped actual : Array DependencyIdentity) : MetaM (Array DependencyIdentity) := do
  unless mapped.size == actual.size do throwError "contract.equivalence:dependency_count"
  unless mapped.map (·.name) == actual.map (·.name) do
    throwError "contract.equivalence:dependency_enumeration"
  actual.mapM fun expected => do
    let candidates := mapped.filter (·.name == expected.name)
    unless candidates.size == 1 do throwError "contract.equivalence:dependency_membership:{expected.name}"
    let value := candidates[0]!
    unless value.owner == expected.owner do throwError "contract.equivalence:dependency_owner:{value.name}"
    check s!"dependency.mapped.type:{value.name}" value.typeIdentity expected.typeIdentity
    check s!"dependency.mapped.body:{value.name}" value.bodyIdentity expected.bodyIdentity
    return value

private partial def renamePlan (mapping : NameMapping) : PlanNode → PlanNode
  | .atom e => .atom (renameExpr mapping e)
  | .supplied e => .supplied (renameExpr mapping e)
  | .expanded e p => .expanded (renameExpr mapping e) (renamePlan mapping p)
  | .proofLeaf e => .proofLeaf (renameExpr mapping e)
  | .typeNode p => .typeNode (renamePlan mapping p)
  | .audit a b => .audit (renamePlan mapping a) (renamePlan mapping b)
  | .app a b => .app (renamePlan mapping a) (renamePlan mapping b)
  | .lam a b info => .lam (renamePlan mapping a) (renamePlan mapping b) info
  | .forallE a b info => .forallE (renamePlan mapping a) (renamePlan mapping b) info
  | .letE a b c nondep => .letE (renamePlan mapping a) (renamePlan mapping b) (renamePlan mapping c) nondep
  | .mdata data p => .mdata data (renamePlan mapping p)
  | .proj name index p => .proj (renameName mapping name) index (renamePlan mapping p)

def planIdentity (oldEnv newEnv : Environment) (mapping : NameMapping)
    (descriptor : Expr) (expected : String) : MetaM String := do
  let some name := descriptor.getAppFn.constName? | throwError "contract.equivalence:descriptor_head"
  let oldPlan ← result (selectedPlan oldEnv name)
  let oldInfo ← inEnvironment oldEnv <| getConstInfo oldPlan.name
  let oldType ← inEnvironment oldEnv <| identity false oldInfo.levelParams oldInfo.type
  let some oldBody := oldInfo.value? | throwError "contract.equivalence:template_value"
  let oldBodyId ← inEnvironment oldEnv <| identity false oldInfo.levelParams oldBody
  check "plan.old.type" oldType oldPlan.typeIdentity
  check "plan.old.body" oldBodyId oldPlan.bodyIdentity
  let (oldBytes, oldWork) ← result (planEncodingWithWork oldPlan)
  check "plan.old.identity" (Sha256.hex oldBytes) oldPlan.planIdentity
  let typeIdentity ← inEnvironment newEnv <| identity false oldInfo.levelParams
    (renameExpr mapping oldInfo.type)
  let bodyIdentity ← inEnvironment newEnv <| identity false oldInfo.levelParams
    (renameExpr mapping oldBody)
  let dependencies ← oldPlan.dependencies.mapM fun input =>
    dependency oldEnv newEnv mapping false input
  let mapped : TemplatePlanData := { oldPlan with
    name := renameName mapping oldPlan.name
    definitionOwner := renameName mapping oldPlan.definitionOwner
    enrollmentOwner := renameName mapping oldPlan.enrollmentOwner
    typeIdentity, bodyIdentity, dependencies
    slots := oldPlan.slots.map fun slot => { slot with type := renameExpr mapping slot.type }
    constructorTypes := oldPlan.constructorTypes.map (renameName mapping)
    plan := renamePlan mapping oldPlan.plan, typePlan := renamePlan mapping oldPlan.typePlan }
  let (_, mappedWork) ← result (planEncodingWithWork mapped)
  unless 2 * oldWork ≤ oldPlan.chargedWork do throwError "contract.equivalence:plan_work"
  let mapped := { mapped with chargedWork := oldPlan.chargedWork - 2 * oldWork + 2 * mappedWork }
  let (bytes, finalWork) ← result (planEncodingWithWork mapped)
  unless finalWork == mappedWork do throwError "contract.equivalence:plan_serialization_work"
  let computed := Sha256.hex bytes
  check "plan.mapped.identity" computed expected
  let newPlan ← result (selectedPlan newEnv mapped.name)
  unless newPlan.chargedWork == mapped.chargedWork && newPlan.serializedBytes == bytes.size do
    throwError "contract.equivalence:plan_mapped_cost"
  return computed

private def actual (env : Environment) (event : TemplateOccurrenceEvent) (source : Bool) : MetaM Expr :=
  inEnvironment env do
    let info ← getConstInfo event.realizationName
    let raw ← if source then do
        let some value := info.value? | throwError "contract.equivalence:source_record_value"
        let value := (value.instantiateLevelParams info.levelParams
          (event.levelParams.map Level.param)).consumeMData
        unless value.isAppOfArity
            `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.mk 7 do
          throwError "contract.equivalence:source_record_literal"
        pure value.getAppArgs[2]!
      else if info.type.isAppOfArity
          `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization 3 ||
          info.type.isAppOfArity escapeForwardBridge 3 ||
          info.type.isAppOfArity escapeWitnessBridge 3 then pure info.type.getAppArgs[2]!
      else match info.value? with
        | some value => pure value
        | none => throwError "contract.equivalence:actual_value"
    if source || info.levelParams.isEmpty then return raw
    unless info.levelParams.length == event.levelParams.length do
      throwError "contract.equivalence:actual_universes"
    return raw.instantiateLevelParams info.levelParams (event.levelParams.map Level.param)

def mapEscape (oldEnv _newEnv : Environment) (mapping : NameMapping)
    (record : BindingRecord) : MetaM EscapeRecordEvidence := do
  if record.escape.bridgeKind == "source-equivalence" then return record.escape
  let raw ← uniqueInput (RegistrationInputs.owned oldEnv) record.occurrence.key
  let fromObject ← record.escape.fromObject.mapM fun origin => do
    let some value := raw.declaration.bind (·.escapeInput.fromObject)
      | throwError "contract.equivalence:escape_origin"
    let type ← inEnvironment oldEnv <| inferType value
    let oldType ← result (rawStatementIdentity record.occurrence.levelParams type)
    let oldObject ← result (rawStatementIdentity record.occurrence.levelParams value)
    check "escape.old.type" oldType.1 origin.typeIdentity
    check "escape.old.object" oldObject.1 origin.objectIdentity
    let typeId ← result (rawStatementIdentity record.occurrence.levelParams (renameExpr mapping type))
    let objectId ← result (rawStatementIdentity record.occurrence.levelParams (renameExpr mapping value))
    return { origin with
      name := renameName mapping origin.name
      typeIdentity := typeId.1, objectIdentity := objectId.1 }
  let continuation ← record.escape.continuation.mapM fun residual => do
    let mut residual := { residual with
      declarationName := residual.declarationName.map (renameName mapping)
      chainName := residual.chainName.map (renameName mapping) }
    if let some originalName := record.escape.continuation.bind (·.declarationName) then
      let info ← inEnvironment oldEnv <| getConstInfo originalName
      let oldId ← result (rawStatementIdentity info.levelParams info.type)
      check "escape.old.continuation" oldId.1 (residual.statementIdentity.getD "")
      let newId ← result (rawStatementIdentity info.levelParams (renameExpr mapping info.type))
      residual := { residual with statementIdentity := some newId.1 }
    return residual
  return { record.escape with fromObject, continuation }

/-- Join the current occurrence and claim before inspecting the supplied state.
The supplied record cannot fill any missing current input or assessment field. -/
def verifyCurrentRecord (side : String) (env : Environment) (record : BindingRecord) :
    MetaM Unit := inEnvironment env do
  let key := record.occurrence.key
  let events := (TemplateBinding.ownedEvents env).filter (·.2.key == key)
  let claims := (TemplateBinding.ownedClaims env).filter (·.2.key == key)
  let joined ← result (TemplateBinding.joinClaims events claims)
  unless joined.size == 1 do throwError "contract.equivalence:{side}.current_event_count"
  let (event, claim) := joined[0]!
  TemplateBinding.validateEvent event
  check s!"{side}.current_event_source" event.registrationSourceIdentity
    record.occurrence.registrationSourceIdentity
  let supplied := record.occurrence
  unless event.key == supplied.key && event.unitName == supplied.unitName &&
      event.realizationName == supplied.realizationName && event.statement.equal supplied.statement &&
      event.levelParams == supplied.levelParams && event.statementIdentity == supplied.statementIdentity &&
      event.arena.equal supplied.arena && event.registrationSource == supplied.registrationSource do
    throwError "contract.equivalence:{side}.current_event"
  let current ← withCurrHeartbeats <| TemplateBinding.assess event claim
  let descriptorsEqual := match current.descriptor, record.descriptor with
    | none, none => true
    | some a, some b => a.equal b
    | _, _ => false
  unless descriptorsEqual do throwError "contract.equivalence:{side}.current_descriptor"
  unless current.bindingOwner == record.bindingOwner do
    throwError "contract.equivalence:{side}.current_binding_owner"
  unless current.escape == record.escape do throwError "contract.equivalence:{side}.current_escape"
  unless current.schemaVersion == record.schemaVersion &&
      current.compatibilityVersion == record.compatibilityVersion do
    throwError "contract.equivalence:{side}.current_version"
  if let (.declaredValidated a, .declaredValidated b) := (current.result, record.result) then
    unless a.escape == b.escape do throwError "contract.equivalence:{side}.current_certificate_escape"
  unless (← TemplateBinding.recordJson current) == (← TemplateBinding.recordJson record) do
    throwError "contract.equivalence:{side}.current_result"

/-- Recompute both sides against their own current environments before mapping.
The current production assessment independently fixes membership, source-scope
and escape identities; the same encoders check every certificate field. -/
def verifyCurrentCertificate (side : String) (env : Environment) (record : BindingRecord)
    (certificate : TemplateBindingCertificate) : MetaM Unit := inEnvironment env do
  TemplateBinding.validateEvent record.occurrence
  unless certificate.key == record.occurrence.key do throwError "contract.equivalence:{side}.certificate_key"
  let source := certificate.sourceBinding.isSome
  let some descriptor := record.descriptor | throwError "contract.equivalence:{side}.descriptor_missing"
  check s!"descriptor.{side}" (← identity source record.occurrence.levelParams descriptor)
    certificate.descriptorIdentity
  check s!"actual.{side}" (← identity source record.occurrence.levelParams
    (← actual env record.occurrence source)) certificate.actualIdentity
  let some template := descriptor.getAppFn.constName? | throwError "contract.equivalence:{side}.template"
  let plan ← result (selectedPlan env template)
  let info ← getConstInfo template
  check s!"plan.{side}.type" (← identity false info.levelParams info.type) plan.typeIdentity
  let some body := info.value? | throwError "contract.equivalence:{side}.template_body"
  check s!"plan.{side}.body" (← identity false info.levelParams body) plan.bodyIdentity
  for input in plan.dependencies do discard <| dependency env env #[] false input
  let (bytes, _) ← result (planEncodingWithWork plan)
  check s!"plan.{side}" (Sha256.hex bytes) certificate.planIdentity
  let definitionName := certificate.sourceBinding.bind fun binding =>
    (binding.getObjVal? "definition_entry").toOption.bind fun entry =>
      (entry.getObjValAs? String "name").toOption
  for input in certificate.argumentInputs do
    discard <| dependency env env #[] source input
  for input in certificate.extractionInputs do
    discard <| dependency env env #[] source input (definitionName == some input.name.toString)
  if let some binding := certificate.sourceBinding then
    let registration := mkConst record.occurrence.realizationName
      (record.occurrence.levelParams.map Level.param)
    check s!"source.registration.{side}" (← identity true record.occurrence.levelParams registration)
      (← result (binding.getObjValAs? String "registration_identity"))
  check s!"evidence.{side}" (← result (bindingIdentity record.occurrence.statementIdentity certificate 524288)).1
    certificate.evidenceRef

/-- Repository data bodies include opaque implementations. Proof bodies and
pinned upstream implementations are omitted by the same rule in every phase. -/
private def actualDependencyBody (info : ConstantInfo) (owner : Name) : MetaM (Option Expr) := do
  if (← isProp info.type) || !Repository.isModule owner then return none
  return info.value? (allowOpaque := true)

/-- Actuals and supplied roots keep their raw expression shape after proof erasure.
Repository data/type dependencies are followed; proof bodies are omitted and
upstream implementations remain pinned. The fixed walk has no candidate rules. -/
def actualDependencies (env : Environment) (event : TemplateOccurrenceEvent)
    (value : Expr) (extraRoots : Array Expr := #[]) :
    MetaM (Array DependencyIdentity) := inEnvironment env do
  let mut roots := (← eraseProofs value).1.getUsedConstants ++ (← inspectionRoots event)
  for value in extraRoots do roots := roots ++ (← eraseProofs value).1.getUsedConstants
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  let mut remaining := 524288
  while let name :: rest := pending do
    pending := rest
    if name == ``lcProof || seen.contains name then continue
    Core.checkMaxHeartbeats "contract actual dependency closure"
    if remaining == 0 then throwError "contract.equivalence:actual_dependency_budget"
    remaining := remaining - 1
    seen := seen.insert name
    let info ← getConstInfo name
    let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
    let (type, work) ← eraseProofs info.type remaining
    remaining := remaining - work
    pending := type.getUsedConstants.toList ++ pending
    if let some body ← actualDependencyBody info owner then
      let (body, work) ← eraseProofs body remaining
      remaining := remaining - work
      pending := body.getUsedConstants.toList ++ pending
  (seen.toArray.qsort Name.quickLt).mapM fun name => withCurrHeartbeats do
    let info ← getConstInfo name
    let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
    let typeIdentity ← identity false info.levelParams info.type
    let bodyIdentity ← (← actualDependencyBody info owner).mapM (identity false info.levelParams)
    let bodyIdentity := bodyIdentity.getD ""
    return { name, owner, typeIdentity, bodyIdentity }

/-- Independently extract both actuals and their fixed data/type closures.
Repository data bodies are compared, proof bodies and pinned upstream bodies
are omitted, and supplied descriptor roots follow the same traversal. -/
def verifyActualDependencies (label : String) (oldEnv newEnv : Environment)
    (mapping : NameMapping) (oldEvent newEvent : TemplateOccurrenceEvent) (source : Bool)
    (oldRoots newRoots : Array Expr := #[]) : MetaM Unit := do
  let oldActual ← actual oldEnv oldEvent source
  let newActual ← actual newEnv newEvent source
  let expected ← inEnvironment newEnv <| identity source oldEvent.levelParams
    (renameExpr mapping oldActual)
  let observed ← inEnvironment newEnv <| identity source newEvent.levelParams newActual
  check s!"{label}.actual" observed expected
  let oldDependencies ← actualDependencies oldEnv oldEvent oldActual oldRoots
  let newDependencies ← actualDependencies newEnv newEvent newActual newRoots
  let mappedDependencies ← oldDependencies.mapM fun input => do
    -- The closure fingerprints upstream types but omits pinned upstream bodies.
    let info ← inEnvironment oldEnv <| getConstInfo input.name
    let typeIdentity ← inEnvironment newEnv <| identity false info.levelParams (renameExpr mapping info.type)
    let body ← inEnvironment oldEnv <| actualDependencyBody info input.owner
    let bodyIdentity ← inEnvironment newEnv <| body.mapM fun value =>
      identity false info.levelParams (renameExpr mapping value)
    let bodyIdentity := bodyIdentity.getD ""
    return { input with
      name := renameName mapping input.name
      owner := renameName mapping input.owner
      typeIdentity, bodyIdentity }
  let mappedDependencies := mappedDependencies.qsort (fun a b => Name.quickLt a.name b.name)
  discard <| alignDependencies mappedDependencies newDependencies

/-- Verify every certificate identity by the production encoder. Dependency
membership and producer enumeration are checked after declaration renaming.
Source scopes and their D5 definitions must remain unchanged in this L0 check. -/
def verifyRecord (oldEnv newEnv : Environment) (authorization : Authorization)
    (oldRecord newRecord : BindingRecord) : MetaM Json := do
  verifyCurrentRecord "old" oldEnv oldRecord
  verifyCurrentRecord "new" newEnv newRecord
  let .declaredValidated oldCert := oldRecord.result
    | throwError "contract.equivalence:original_not_validated"
  let .declaredValidated newCert := newRecord.result
    | throwError "contract.equivalence:prototype_not_validated"
  verifyCurrentCertificate "old" oldEnv oldRecord oldCert
  verifyCurrentCertificate "new" newEnv newRecord newCert
  let mapping ← completeMapping oldEnv newEnv authorization oldRecord newRecord
  let some descriptor := oldRecord.descriptor | throwError "contract.equivalence:descriptor_missing"
  let some newDescriptor := newRecord.descriptor | throwError "contract.equivalence:prototype_descriptor_missing"
  let some oldTemplate := descriptor.getAppFn.constName? | throwError "contract.equivalence:descriptor_head"
  let some newTemplate := newDescriptor.getAppFn.constName? | throwError "contract.equivalence:prototype_descriptor_head"
  let oldPlan ← result (selectedPlan oldEnv oldTemplate)
  let newPlan ← result (selectedPlan newEnv newTemplate)
  unless renameName mapping oldTemplate == newTemplate &&
      renameName mapping oldPlan.enrollmentOwner == newPlan.enrollmentOwner &&
      renameName mapping oldPlan.definitionOwner == newPlan.definitionOwner do
    throwError "contract.equivalence:unauthorized_template_or_owner"
  let source := oldCert.sourceBinding.isSome
  unless source == newCert.sourceBinding.isSome do throwError "contract.equivalence:source_kind"
  unless (renameExpr mapping oldRecord.occurrence.statement).equal newRecord.occurrence.statement do
    throwError "contract.equivalence:statement_mapping"
  unless (renameExpr mapping oldRecord.occurrence.arena).equal newRecord.occurrence.arena do
    throwError "contract.equivalence:arena_mapping"
  check "statement_identity" oldRecord.occurrence.statementIdentity newRecord.occurrence.statementIdentity
  let oldDescriptor ← inEnvironment oldEnv <| identity source oldRecord.occurrence.levelParams descriptor
  check "descriptor.old" oldDescriptor oldCert.descriptorIdentity
  let descriptorIdentity ← inEnvironment newEnv <| identity source oldRecord.occurrence.levelParams
    (renameExpr mapping descriptor)
  check "descriptor.mapped" descriptorIdentity newCert.descriptorIdentity
  let rawActual ← actual oldEnv oldRecord.occurrence source
  let oldActual ← inEnvironment oldEnv <| identity source oldRecord.occurrence.levelParams rawActual
  check "actual.old" oldActual oldCert.actualIdentity
  let actualIdentity ← inEnvironment newEnv <| identity source oldRecord.occurrence.levelParams
    (renameExpr mapping rawActual)
  check "actual.mapped" actualIdentity newCert.actualIdentity
  let planIdentity ← planIdentity oldEnv newEnv mapping descriptor newCert.planIdentity
  let arguments ← oldCert.argumentInputs.mapM fun input =>
    dependency oldEnv newEnv mapping source input
  let definitionName := oldCert.sourceBinding.bind fun binding =>
    (binding.getObjVal? "definition_entry").toOption.bind fun entry =>
      (entry.getObjValAs? String "name").toOption
  let extractions ← oldCert.extractionInputs.mapM fun input =>
    dependency oldEnv newEnv mapping source input (definitionName == some input.name.toString)
  let extractions := if source then extractions else
    (NameSet.ofArray (extractions.map (·.name))).toArray.map fun name =>
      (extractions.find? (·.name == name)).get!
  let argumentInputs ← alignDependencies arguments newCert.argumentInputs
  let extractionInputs ← alignDependencies extractions newCert.extractionInputs
  let mut escape ← mapEscape oldEnv newEnv mapping oldRecord
  let sourceBinding ← oldCert.sourceBinding.mapM fun binding => do
    let recordExpr := mkConst oldRecord.occurrence.realizationName
      (oldRecord.occurrence.levelParams.map Level.param)
    let oldRegistration ← inEnvironment oldEnv <| identity true oldRecord.occurrence.levelParams recordExpr
    check "source.registration.old" oldRegistration (← result (binding.getObjValAs? String "registration_identity"))
    let registrationIdentity ← inEnvironment newEnv <| identity true oldRecord.occurrence.levelParams
      (renameExpr mapping recordExpr)
    let binding ← setJsonField (renameSourceBinding mapping binding) "registration_identity" (toJson registrationIdentity)
    unless some binding == newCert.sourceBinding do throwError "contract.equivalence:source_binding_mapping"
    return binding
  if source then
    escape := { escape with fromObject := escape.fromObject.map fun origin => {
      origin with name := renameName mapping origin.name, objectIdentity := actualIdentity } }
  unless escape == newCert.escape do throwError "contract.equivalence:escape_mapping"
  let key : TemplateOccurrenceKey := {
    root := renameName mapping oldCert.key.root
    registrationModule := renameName mapping oldCert.key.registrationModule
    theoremName := renameName mapping oldCert.key.theoremName
    objectArena := renameName mapping oldCert.key.objectArena
    catalog := renameName mapping oldCert.key.catalog }
  unless key == newCert.key do throwError "contract.equivalence:key_mapping"
  let certificate := { oldCert with
    key, planIdentity, descriptorIdentity, actualIdentity
    argumentInputs, extractionInputs, escape, sourceBinding }
  let oldEvidence ← result (bindingIdentity oldRecord.occurrence.statementIdentity oldCert 524288)
  check "evidence.old" oldEvidence.1 oldCert.evidenceRef
  let mappedEvidence ← result (bindingIdentity newRecord.occurrence.statementIdentity certificate 524288)
  check "evidence.mapped" mappedEvidence.1 newCert.evidenceRef
  let mappedRecord := { oldRecord with
    occurrence := { oldRecord.occurrence with
      key
      unitName := renameName mapping oldRecord.occurrence.unitName
      realizationName := renameName mapping oldRecord.occurrence.realizationName
      registrationSource := TemplateAudit.sourcePath key.registrationModule }
    bindingOwner := oldRecord.bindingOwner.map (renameName mapping)
    escape, result := .declaredValidated { certificate with evidenceRef := mappedEvidence.1 } }
  let mappedJson ← inEnvironment newEnv <| TemplateBinding.recordJson mappedRecord
  let newJson ← inEnvironment newEnv <| TemplateBinding.recordJson newRecord
  unless mappedJson == newJson do throwError "contract.equivalence:complete_record_mapping"
  return Json.mkObj [
    ("theorem", toJson key.theoremName.toString), ("verified", toJson true),
    ("descriptor_identity", toJson descriptorIdentity), ("actual_identity", toJson actualIdentity),
    ("plan_identity", toJson planIdentity), ("evidence_ref", toJson mappedEvidence.1),
    ("argument_inputs", toJson argumentInputs.size), ("extraction_inputs", toJson extractionInputs.size),
    ("name_mapping", toJson (mapping.map fun (a, b) => (a.toString, b.toString)))]

/-- Missing readout evidence stays undeclared. No certificate or diagnostic
normalization can make it look like a validated registration. -/
def verifyMissingRecord (oldEnv newEnv : Environment) (authorization : Authorization)
    (oldRecord newRecord : BindingRecord) : MetaM Json := do
  verifyCurrentRecord "old" oldEnv oldRecord
  verifyCurrentRecord "new" newEnv newRecord
  unless (oldRecord.result matches .undeclared) && (newRecord.result matches .undeclared) &&
      oldRecord.descriptor.isNone && newRecord.descriptor.isNone do
    throwError "contract.equivalence:missing_record_state"
  let mapping ← completeMapping oldEnv newEnv authorization oldRecord newRecord
  inEnvironment oldEnv <| TemplateBinding.validateEvent oldRecord.occurrence
  inEnvironment newEnv <| TemplateBinding.validateEvent newRecord.occurrence
  let source := oldRecord.escape.bridgeKind == "source-equivalence"
  unless source == (newRecord.escape.bridgeKind == "source-equivalence") do
    throwError "contract.equivalence:undeclared_source_kind"
  verifyActualDependencies "undeclared" oldEnv newEnv mapping
    oldRecord.occurrence newRecord.occurrence source
  let occurrence := oldRecord.occurrence
  let key := occurrence.key
  let key : TemplateOccurrenceKey := {
    root := renameName mapping key.root, registrationModule := renameName mapping key.registrationModule
    theoremName := renameName mapping key.theoremName, objectArena := renameName mapping key.objectArena
    catalog := renameName mapping key.catalog }
  unless renameExpr mapping occurrence.statement == newRecord.occurrence.statement &&
      renameExpr mapping occurrence.arena == newRecord.occurrence.arena &&
      occurrence.levelParams == newRecord.occurrence.levelParams do
    throwError "contract.equivalence:missing_record_expressions"
  let mapped := { oldRecord with
    occurrence := { occurrence with
      key
      unitName := renameName mapping occurrence.unitName
      realizationName := renameName mapping occurrence.realizationName
      registrationSource := TemplateAudit.sourcePath key.registrationModule }
    bindingOwner := oldRecord.bindingOwner.map (renameName mapping)
    escape := ← mapEscape oldEnv newEnv mapping oldRecord }
  unless (← inEnvironment newEnv <| TemplateBinding.recordJson mapped) ==
      (← inEnvironment newEnv <| TemplateBinding.recordJson newRecord) do
    throwError "contract.equivalence:complete_missing_record"
  return Json.mkObj [("verified", toJson true), ("state", toJson "undeclared"),
    ("theorem", toJson key.theoremName.toString)]

end LeanInformationAudit.ContractPrototype.Equivalence
