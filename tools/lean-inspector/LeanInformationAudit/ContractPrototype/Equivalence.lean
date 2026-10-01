import LeanInformationAudit.ContractPrototype.Replay

/- L0 原型 -/
namespace LeanInformationAudit.ContractPrototype.Equivalence
open Lean Meta TemplateAudit

abbrev NameMapping := Array (Name × Name)

/-- Explicit mappings take priority; namespace prefixes extend componentwise. -/
partial def renameName (mapping : NameMapping) (name : Name) : Name :=
  match mapping.find? (·.1 == name) with
  | some (_, replacement) => replacement
  | none => match name with
    | .str parent component => .str (renameName mapping parent) component
    | .num parent index => .num (renameName mapping parent) index
    | .anonymous => .anonymous

/-- Preserve universes, binders, application shape and metadata. Only declaration
references and projection type names change. No normalization is performed. -/
partial def renameExpr (mapping : NameMapping) : Expr → Expr
  | .const name levels => .const (renameName mapping name) levels
  | .app fn argument => .app (renameExpr mapping fn) (renameExpr mapping argument)
  | .lam name domain body info => .lam name (renameExpr mapping domain) (renameExpr mapping body) info
  | .forallE name domain body info => .forallE name (renameExpr mapping domain) (renameExpr mapping body) info
  | .letE name type value body nondep => .letE name (renameExpr mapping type)
      (renameExpr mapping value) (renameExpr mapping body) nondep
  | .mdata data body => .mdata data (renameExpr mapping body)
  | .proj name index body => .proj (renameName mapping name) index (renameExpr mapping body)
  | other => other

def inEnvironment (env : Environment) (action : MetaM α) : MetaM α := do
  let saved ← getEnv
  setEnv (env.setExporting false)
  try action finally setEnv saved

private def result (value : Except String α) : MetaM α :=
  match value with
  | .ok value => pure value
  | .error message => throwError message

private def identity (source : Bool) (levels : List Name) (value : Expr) : MetaM String := do
  return (← result (← if source then compactIdentity levels value else rawIdentity levels value)).1

private def check (label : String) (actual expected : String) : MetaM Unit := do
  unless actual == expected do
    throwError "contract.equivalence:{label}: recomputed={actual} reported={expected}"

private partial def renameJson (mapping : NameMapping) : Json → Json
  | .str value => .str (Id.run do
      if let some (_, target) := mapping.find? (·.1.toString == value) then
        return target.toString
      let prefixes := mapping.filter fun (source, _) => value.startsWith (source.toString ++ ".")
      let ordered := prefixes.qsort fun a b => a.1.toString.length > b.1.toString.length
      if let some (source, target) := ordered[0]? then
        return target.toString ++ (value.drop source.toString.length).toString
      return value)
  | .arr values => .arr (values.map (renameJson mapping))
  | .obj fields => Json.mkObj (fields.toArray.toList.map fun (key, value) =>
      (key, renameJson mapping value))
  | value => value

private def setJsonField (json : Json) (key : String) (value : Json) : MetaM Json := do
  let fields ← result json.getObj?
  unless (fields.toArray.any (·.1 == key)) do
    throwError "contract.equivalence:source_field_missing:{key}"
  return Json.mkObj (fields.toArray.toList.map fun (name, old) =>
    (name, if name == key then value else old))

/-- Resolve copied private declarations by actual module and unique user name;
private spellings and generated companions are never guessed from strings. -/
def completeMapping (oldEnv newEnv : Environment) (prefixes : NameMapping)
    (oldRecord newRecord : BindingRecord) : MetaM NameMapping := do
  let mut mapping := prefixes ++ #[
    (oldRecord.occurrence.unitName, newRecord.occurrence.unitName),
    (oldRecord.occurrence.realizationName, newRecord.occurrence.realizationName)]
  for idx in [:oldEnv.header.moduleNames.size] do
    let owner := oldEnv.header.moduleNames[idx]!
    let newOwner := renameName prefixes owner
    if owner == newOwner then continue
    let some newIdx := newEnv.getModuleIdx? newOwner
      | throwError "contract.equivalence:mapped_owner_missing:{newOwner}"
    for name in oldEnv.header.moduleData[idx]!.constNames do
      unless isPrivateName name do continue
      let user := renameName prefixes (privateToUserName name)
      let candidates := newEnv.header.moduleData[newIdx.toNat]!.constNames.filter
        (fun candidate => privateToUserName candidate == user)
      if candidates.isEmpty then continue
      unless candidates.size == 1 do throwError "contract.equivalence:private_ambiguity:{name}"
      mapping := mapping.push (name, candidates[0]!)
  return mapping

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
  let raw := (RegistrationInputs.owned oldEnv).find? fun (owner, input) =>
    owner == record.occurrence.key.registrationModule && input.entry.theoremName == record.occurrence.key.theoremName
  let fromObject ← record.escape.fromObject.mapM fun origin => do
    let some (_, input) := raw | throwError "contract.equivalence:escape_input"
    let some value := input.declaration.bind (·.escapeInput.fromObject)
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

/-- Verify every certificate identity by the production encoder. Dependency
membership and producer enumeration are checked after declaration renaming.
Source scopes and their D5 definitions must remain unchanged in this L0 check. -/
def verifyRecord (oldEnv newEnv : Environment) (prefixes : NameMapping)
    (oldRecord newRecord : BindingRecord) : MetaM Json := do
  let .declaredValidated oldCert := oldRecord.result
    | throwError "contract.equivalence:original_not_validated"
  let .declaredValidated newCert := newRecord.result
    | throwError "contract.equivalence:prototype_not_validated"
  let mapping ← completeMapping oldEnv newEnv prefixes oldRecord newRecord
  let some descriptor := oldRecord.descriptor | throwError "contract.equivalence:descriptor_missing"
  let some newDescriptor := newRecord.descriptor | throwError "contract.equivalence:prototype_descriptor_missing"
  let some oldTemplate := descriptor.getAppFn.constName? | throwError "contract.equivalence:descriptor_head"
  let some newTemplate := newDescriptor.getAppFn.constName? | throwError "contract.equivalence:prototype_descriptor_head"
  let oldPlan ← result (selectedPlan oldEnv oldTemplate)
  let newPlan ← result (selectedPlan newEnv newTemplate)
  let mapping := mapping ++ #[(oldPlan.enrollmentOwner, newPlan.enrollmentOwner),
    (oldPlan.definitionOwner, newPlan.definitionOwner), (oldTemplate, newTemplate)]
  let source := oldCert.sourceBinding.isSome
  unless source == newCert.sourceBinding.isSome do throwError "contract.equivalence:source_kind"
  unless (renameExpr mapping oldRecord.occurrence.statement).equal newRecord.occurrence.statement do
    throwError "contract.equivalence:statement_mapping"
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
    let binding ← setJsonField (renameJson mapping binding) "registration_identity" (toJson registrationIdentity)
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

end LeanInformationAudit.ContractPrototype.Equivalence
