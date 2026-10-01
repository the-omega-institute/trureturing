import LeanInformationAudit.ContractPrototype.Equivalence

/- L0 原型 -/
namespace LeanInformationAudit.ContractPrototype.CatalogEquivalence
open Lean Meta TemplateAudit
open Equivalence

private def inEnvironment (env : Environment) (action : MetaM α) : MetaM α := do
  let saved ← getEnv
  setEnv (env.setExporting false)
  try action finally setEnv saved

private def result (value : Except String α) : MetaM α :=
  match value with
  | .ok value => pure value
  | .error message => throwError message

private def require (condition : Bool) (label : String) : MetaM Unit := do
  unless condition do throwError "contract.catalog_equivalence:{label}"

private def fingerprint (levels : List Name) (value : Expr) : MetaM String := do
  return (← result (← rawIdentity levels value)).1

private def identity (env : Environment) (name : Name) : MetaM (String × String) :=
  inEnvironment env do
    let info ← getConstInfo name
    let type ← fingerprint info.levelParams info.type
    let body ← if ← isProp info.type then pure "" else
      match info.value? with
      | none => pure ""
      | some value => fingerprint info.levelParams value
    return (type, body)

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
  | .letE a b c nondep => .letE (renamePlan mapping a) (renamePlan mapping b)
      (renamePlan mapping c) nondep
  | .mdata data p => .mdata data (renamePlan mapping p)
  | .proj name index p => .proj (renameName mapping name) index (renamePlan mapping p)

private def dependency (oldEnv newEnv : Environment) (mapping : NameMapping)
    (input : DependencyIdentity) : MetaM DependencyIdentity := do
  let (oldType, oldBody) ← identity oldEnv input.name
  require (oldType == input.typeIdentity && oldBody == input.bodyIdentity)
    s!"dependency.original_hash:{input.name}"
  let info ← inEnvironment oldEnv <| getConstInfo input.name
  let typeIdentity ← inEnvironment newEnv <|
    fingerprint info.levelParams (renameExpr mapping info.type)
  let bodyIdentity ← inEnvironment newEnv do
    if ← isProp info.type then return ""
    match info.value? with
    | none => return ""
    | some value => fingerprint info.levelParams (renameExpr mapping value)
  let name := renameName mapping input.name
  let owner := renameName mapping input.owner
  let (actualType, actualBody) ← identity newEnv name
  require (actualType == typeIdentity && actualBody == bodyIdentity)
    s!"dependency.mapped_hash:{name}"
  let actualOwner := (RegistrationReifier.declaringModuleOf newEnv name).getD newEnv.header.mainModule
  require (actualOwner == owner) s!"dependency.mapped_owner:{name}"
  return { name, owner, typeIdentity, bodyIdentity }

private def mappingJson (mapping : NameMapping) : Json :=
  Json.arr <| mapping.map fun (a, b) => Json.mkObj [
    ("original", toJson a.toString), ("prototype", toJson b.toString)]

/-- Compare every production plan byte, retaining the compiler's constructor
grammar, dependency enumeration, rules, quota and both serialization passes. -/
def verifyTemplate (oldEnv newEnv : Environment) (prefixes : NameMapping)
    (oldName newName : Name) : MetaM Json := do
  let oldPlan ← result (selectedPlan oldEnv oldName)
  let newPlan ← result (selectedPlan newEnv newName)
  let mapping := prefixes ++ #[(oldName, newName),
    (oldPlan.definitionOwner, newPlan.definitionOwner),
    (oldPlan.enrollmentOwner, newPlan.enrollmentOwner)]
  let oldInfo ← inEnvironment oldEnv <| getConstInfo oldName
  let newInfo ← inEnvironment newEnv <| getConstInfo newName
  require (renameExpr mapping oldInfo.type == newInfo.type) "template.raw_type"
  let some oldBody := oldInfo.value? | throwError "contract.catalog_equivalence:template.original_body"
  let some newBody := newInfo.value? | throwError "contract.catalog_equivalence:template.prototype_body"
  require (renameExpr mapping oldBody == newBody) "template.raw_body"
  let typeIdentity ← inEnvironment oldEnv <| fingerprint oldInfo.levelParams oldInfo.type
  let bodyIdentity ← inEnvironment oldEnv <| fingerprint oldInfo.levelParams oldBody
  require (typeIdentity == oldPlan.typeIdentity && bodyIdentity == oldPlan.bodyIdentity)
    "template.original_type_body_hash"
  let (oldBytes, oldWork) ← result (planEncodingWithWork oldPlan)
  require (Sha256.hex oldBytes == oldPlan.planIdentity && oldBytes.size == oldPlan.serializedBytes)
    "template.original_plan_hash_bytes"
  let typeIdentity ← inEnvironment newEnv <|
    fingerprint oldInfo.levelParams (renameExpr mapping oldInfo.type)
  let bodyIdentity ← inEnvironment newEnv <|
    fingerprint oldInfo.levelParams (renameExpr mapping oldBody)
  let dependencies ← oldPlan.dependencies.mapM (dependency oldEnv newEnv mapping)
  let mapped : TemplatePlanData := { oldPlan with
    name := renameName mapping oldPlan.name
    definitionOwner := renameName mapping oldPlan.definitionOwner
    enrollmentOwner := renameName mapping oldPlan.enrollmentOwner
    typeIdentity, bodyIdentity, dependencies
    slots := oldPlan.slots.map fun slot => { slot with type := renameExpr mapping slot.type }
    constructorTypes := oldPlan.constructorTypes.map (renameName mapping)
    plan := renamePlan mapping oldPlan.plan, typePlan := renamePlan mapping oldPlan.typePlan }
  let (_, mappedWork) ← result (planEncodingWithWork mapped)
  require (2 * oldWork ≤ oldPlan.chargedWork) "template.original_work"
  let mapped := { mapped with chargedWork := oldPlan.chargedWork - 2 * oldWork + 2 * mappedWork }
  let (mappedBytes, finalWork) ← result (planEncodingWithWork mapped)
  let (newBytes, newWork) ← result (planEncodingWithWork newPlan)
  require (finalWork == mappedWork && newWork == mappedWork) "template.serialization_work"
  require (mappedBytes == newBytes) "template.production_encoded_bytes"
  require (Sha256.hex mappedBytes == newPlan.planIdentity && newBytes.size == newPlan.serializedBytes)
    "template.prototype_plan_hash_bytes"
  require (mapped.chargedWork == newPlan.chargedWork) "template.charged_work"
  return Json.mkObj [("status", toJson "equal"), ("all_production_plan_bytes", toJson true),
    ("constructor_count", toJson newPlan.constructorTypes.size),
    ("dependency_count", toJson newPlan.dependencies.size),
    ("original_plan_identity", toJson oldPlan.planIdentity),
    ("prototype_plan_identity", toJson newPlan.planIdentity),
    ("original_charged_work", toJson oldPlan.chargedWork),
    ("prototype_charged_work", toJson newPlan.chargedWork),
    ("original_serialization_work", toJson oldWork),
    ("prototype_serialization_work", toJson mappedWork), ("name_mapping", mappingJson mapping)]

private def verifyRows (oldEnv newEnv : Environment) (mapping : NameMapping)
    (oldRoot newRoot : Name) (label : String)
    (oldRows newRows : Array SnapshotOccurrence) : MetaM Json := do
  require (oldRows.size == newRows.size) s!"root.{label}.row_count"
  let oldEffective := snapshotExpectations oldRoot oldRows
  let newEffective := snapshotExpectations newRoot newRows
  let mut extraCapture := 0
  for index in [:oldRows.size] do
    let a := oldRows[index]!
    let b := newRows[index]!
    let oldType ← inEnvironment oldEnv do return (← getConstInfo a.theoremName).type
    let newType ← inEnvironment newEnv do return (← getConstInfo b.theoremName).type
    require (renameExpr mapping oldType == newType) s!"root.{label}.raw_theorem_type:{index}"
    if let some captured := a.capturedStatement then
      require (captured == oldType) s!"root.{label}.original_captured_type:{index}"
    if let some captured := b.capturedStatement then
      require (captured == newType) s!"root.{label}.prototype_captured_type:{index}"
    let oldIdentity := oldEffective[index]!.statementIdentity
    let newIdentity := newEffective[index]!.statementIdentity
    require (oldIdentity == theoremStatementIdentity oldEnv a.theoremName)
      s!"root.{label}.original_statement_identity:{index}"
    require (newIdentity == theoremStatementIdentity newEnv b.theoremName)
      s!"root.{label}.prototype_statement_identity:{index}"
    require (renameName mapping a.objectArenaName == b.objectArenaName &&
      renameName mapping a.theoremName == b.theoremName &&
      renameName mapping a.registrationModuleName == b.registrationModuleName &&
      oldIdentity == newIdentity) s!"root.{label}.effective_fields:{index}"
    if a.capturedStatement.isNone && b.capturedStatement.isSome then
      extraCapture := extraCapture + 1
    else
      require (a.capturedStatement.isSome == b.capturedStatement.isSome)
        s!"root.{label}.captured_presence:{index}"
  return Json.mkObj [("rows", toJson oldRows.size), ("effective_fields_equal", toJson true),
    ("additional_raw_type_captures", toJson extraCapture)]

/-- The producer uses an explicit statement identity in preference to a captured
raw type. Retained extra captures are checked against the actual theorem type. -/
def verifyRoot (oldEnv newEnv : Environment) (mapping : NameMapping)
    (oldRoot newRoot : Name) : MetaM Json := do
  let some a := RootCatalogs.find? oldEnv oldRoot
    | throwError "contract.catalog_equivalence:root.original_missing"
  let some b := RootCatalogs.find? newEnv newRoot
    | throwError "contract.catalog_equivalence:root.prototype_missing"
  require (renameName mapping a.rootId == b.rootId) "root.root_id"
  require (a.companionPrefix.map (renameName mapping) == b.companionPrefix) "root.companion_prefix"
  let expected ← verifyRows oldEnv newEnv mapping oldRoot newRoot "expected" a.expected b.expected
  let source ← verifyRows oldEnv newEnv mapping oldRoot newRoot "source" a.source b.source
  let baseline ← verifyRows oldEnv newEnv mapping oldRoot newRoot "baseline" a.baseline b.baseline
  return Json.mkObj [("status", toJson "equal"), ("root_id", toJson true),
    ("companion_prefix", toJson true), ("expected", expected), ("source", source),
    ("baseline", baseline), ("name_mapping", mappingJson mapping)]

private def kernelAddress (env : Environment) (record : SealArenaRecord)
    (row : SealTheoremRecord) : MetaM String := inEnvironment env do
  let catalog ← mkConstWithFreshMVarLevels record.catalog.catalogName
  let type ← inferType catalog
  require (type.isAppOf `D5.S3.ConceptDynamics.InformationEscape.Catalog) "seal.catalog_type"
  let arena := type.appArg!
  let stateFintype ← mkAppM `D5.S3.ConceptDynamics.InformationEscape.Arena.stateFintype #[arena]
  let bundle ← mkAppM `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.primitives
    #[← mkConstWithFreshMVarLevels row.unitName]
  primitiveKernelAddress stateFintype bundle

private partial def renameJson (mapping : NameMapping) : Json → Json
  | .str value => .str ((mapping.find? (·.1.toString == value)).map
      (·.2.toString) |>.getD value)
  | .arr values => .arr (values.map (renameJson mapping))
  | .obj fields => Json.mkObj (fields.toArray.toList.map fun (key, value) =>
      (key, renameJson mapping value))
  | value => value

/-- Both complete artifacts are serialized through the production validator.
Every primitive-kernel hash is independently recomputed from the typed unit. -/
def verifySeal (oldEnv newEnv : Environment) (prefixes : NameMapping)
    (oldRoot newRoot : Name) : MetaM Json := do
  let oldRecords := SealRecords.forRoot oldEnv oldRoot
  let newRecords := SealRecords.forRoot newEnv newRoot
  require (!oldRecords.isEmpty && oldRecords.size == newRecords.size) "seal.arena_count"
  let mut mapping := prefixes
  let mut kernelChecks := 0
  for index in [:oldRecords.size] do
    let a := oldRecords[index]!
    let b := newRecords[index]!
    require (renameName mapping a.catalog.rootId == b.catalog.rootId &&
      renameName mapping a.catalog.catalogId == b.catalog.catalogId &&
      renameName mapping a.catalog.arenaName == b.catalog.arenaName)
      s!"seal.catalog_identity:{index}"
    require (a.theorems.size == b.theorems.size) s!"seal.theorem_count:{index}"
    mapping := mapping ++ #[(a.catalog.catalogName, b.catalog.catalogName),
      (a.verdict.name, b.verdict.name)]
    for rowIndex in [:a.theorems.size] do
      let oldRow := a.theorems[rowIndex]!
      let newRow := b.theorems[rowIndex]!
      require (renameName mapping oldRow.theoremName == newRow.theoremName &&
        renameName mapping oldRow.registrationModuleName == newRow.registrationModuleName &&
        oldRow.index == newRow.index) s!"seal.occurrence_identity:{index}:{rowIndex}"
      mapping := mapping ++ #[(oldRow.unitName, newRow.unitName),
        (oldRow.realizationName, newRow.realizationName),
        (oldRow.certificateName, newRow.certificateName)]
      let oldAddress ← kernelAddress oldEnv a oldRow
      let newAddress ← kernelAddress newEnv b newRow
      require (oldAddress == oldRow.primitiveKernelAddress &&
        newAddress == newRow.primitiveKernelAddress && oldAddress == newAddress)
        s!"seal.primitive_kernel_address:{index}:{rowIndex}"
      kernelChecks := kernelChecks + 2
  let oldJson ← result <| Json.parse (← inEnvironment oldEnv <| serializeSealArtifact oldRecords)
  let newJson ← result <| Json.parse (← inEnvironment newEnv <| serializeSealArtifact newRecords)
  require (renameJson mapping oldJson == newJson) "seal.complete_production_json"
  return Json.mkObj [("status", toJson "equal"), ("complete_production_json", toJson true),
    ("arenas", toJson oldRecords.size), ("primitive_kernel_hash_recomputations", toJson kernelChecks),
    ("name_mapping", mappingJson mapping)]

end LeanInformationAudit.ContractPrototype.CatalogEquivalence
