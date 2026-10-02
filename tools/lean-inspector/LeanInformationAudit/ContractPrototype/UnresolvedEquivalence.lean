import LeanInformationAudit.ContractPrototype.Equivalence

/- L0 原型 -/
namespace LeanInformationAudit.ContractPrototype.UnresolvedEquivalence
open Lean Meta TemplateAudit Equivalence

private def result (value : Except String α) : MetaM α :=
  match value with
  | .ok value => pure value
  | .error message => throwError message

private def check (label : String) (actual expected : String) : MetaM Unit := do
  unless actual == expected do
    throwError "contract.unresolved_equivalence:{label}: recomputed={actual} reported={expected}"

/-- Resolve compiler names by their actual spelling, including numeric private
components. Parsing a printed private name as a dotted string loses that identity. -/
private def constantName (env : Environment) (text : String) : MetaM Name := do
  let parsed := text.toName
  if parsed.toString == text && env.contains parsed then return parsed
  let imported := env.header.moduleData.flatMap (·.constNames)
  let generated := (GeneratedDeclarations.entries env).map Prod.fst
  let candidates := (imported ++ generated).filter (·.toString == text)
    |>.toList.eraseDups.toArray
  unless candidates.size == 1 do
    throwError "contract.unresolved_equivalence:constant_identity:{text}"
  return candidates[0]!

private def dependencyInput (env : Environment) (json : Json) : MetaM DependencyIdentity := do
  let name ← constantName env (← result (json.getObjValAs? String "name"))
  let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
  check s!"dependency.owner:{name}" owner.toString (← result (json.getObjValAs? String "owner"))
  let typeIdentity ← result (json.getObjValAs? String "type_identity")
  let bodyIdentity ← result (json.getObjValAs? String "body_identity")
  return { name, owner, typeIdentity, bodyIdentity }

private def setField (json : Json) (key : String) (value : Json) : MetaM Json := do
  let fields ← result json.getObj?
  unless fields.toArray.any (·.1 == key) do
    throwError "contract.unresolved_equivalence:missing_field:{key}"
  return Json.mkObj (fields.toArray.toList.map fun (name, old) =>
    (name, if name == key then value else old))

private def diagnosticParts (diagnostic : String) : MetaM (String × Json) := do
  let parts := diagnostic.splitOn " provenance="
  unless parts.length == 2 do throwError "contract.unresolved_equivalence:diagnostic_provenance"
  return (parts[0]!, ← result (Json.parse parts[1]!))

private def argumentNames (env : Environment) (descriptor : Expr) : MetaM (Array Name) :=
  inEnvironment env do
    let mut names : NameSet := {}
    for argument in descriptor.getAppArgs do
      for name in (← eraseProofs argument).1.getUsedConstants do
        unless name == ``lcProof do names := names.insert name
    return names.toArray.qsort Name.quickLt

private def mappedInputs (oldEnv newEnv : Environment) (mapping : NameMapping)
    (provenance : Json) (field : String) (expected : Array Name) (sort : Bool) : MetaM Json := do
  let raw ← result (provenance.getObjValAs? (Array Json) field)
  let original ← raw.mapM (dependencyInput oldEnv)
  unless original.map (·.name) == expected do
    throwError "contract.unresolved_equivalence:input_roots:{field}"
  unless raw == original.map TemplateBinding.dependencyJson do
    throwError "contract.unresolved_equivalence:input_fields:{field}"
  let mapped ← original.mapM fun input => dependency oldEnv newEnv mapping false input
  let mapped := if sort then mapped.qsort (fun a b => Name.quickLt a.name b.name) else mapped
  return Json.arr (mapped.map TemplateBinding.dependencyJson)

private def keyMapping (mapping : NameMapping) (key : TemplateOccurrenceKey) : TemplateOccurrenceKey := {
  root := renameName mapping key.root
  registrationModule := renameName mapping key.registrationModule
  theoremName := renameName mapping key.theoremName
  objectArena := renameName mapping key.objectArena
  catalog := renameName mapping key.catalog }

private def diagnosticPrefix (key : TemplateOccurrenceKey) (kind rule site : String) : String :=
  s!"IE-C050 ClosedTruthReadout key={key.root}/{key.catalog}/{key.theoremName} " ++
    s!"reason={kind} rule={rule} site=" ++ (toJson site).compress ++
    " readout=" ++ (toJson site).compress

def requireSupportedDiagnostic (diagnostic : String) : MetaM Unit := do
  let parts := diagnostic.splitOn " provenance="
  unless parts.length == 2 do throwError "contract.unresolved_equivalence:unsupported_form:missing_provenance"
  let .ok provenance := Json.parse parts[1]!
    | throwError "contract.unresolved_equivalence:unsupported_form:invalid_provenance"
  let .ok site := provenance.getObjValAs? String "site"
    | throwError "contract.unresolved_equivalence:unsupported_form:null_or_missing_site"
  let .ok rule := provenance.getObjValAs? String "rule"
    | throwError "contract.unresolved_equivalence:unsupported_form:missing_rule"
  let .ok fields := provenance.getObj?
    | throwError "contract.unresolved_equivalence:unsupported_form:provenance_object"
  let keys := #["argument_inputs", "extraction_inputs", "plan_identity", "rule", "site", "template_key"]
  unless fields.toArray.size == keys.size && fields.toArray.all (fun (key, _) => keys.contains key) do
    throwError "contract.unresolved_equivalence:unsupported_form:provenance_fields"
  for field in #["plan_identity", "template_key"] do
    let .ok value := provenance.getObjValAs? String field
      | throwError "contract.unresolved_equivalence:unsupported_form:identity_field:{field}"
    if value.isEmpty then throwError "contract.unresolved_equivalence:unsupported_form:empty_identity:{field}"
  for field in #["argument_inputs", "extraction_inputs"] do
    let .ok inputs := provenance.getObjValAs? (Array Json) field
      | throwError "contract.unresolved_equivalence:unsupported_form:input_array:{field}"
    for input in inputs do
      let .ok fields := input.getObj?
        | throwError "contract.unresolved_equivalence:unsupported_form:input_object"
      let keys := #["name", "owner", "type_identity", "body_identity"]
      unless fields.toArray.size == keys.size && fields.toArray.all (fun (key, _) => keys.contains key) do
        throwError "contract.unresolved_equivalence:unsupported_form:input_fields"
      for key in keys do
        unless (input.getObjValAs? String key).isOk do
          throwError "contract.unresolved_equivalence:unsupported_form:input_identity:{key}"
  unless !site.isEmpty && rule == "E5.unsaturated_definition" &&
      parts[0]!.startsWith "IE-C050 ClosedTruthReadout key=" &&
      (parts[0]!.contains " reason=unclassified_form " ||
        parts[0]!.contains " reason=forbidden_dependency ") do
    throwError "contract.unresolved_equivalence:unsupported_form:unnamed_or_resource_site"

/-- Verify the named-site unresolved diagnostic and the entire exported record.
Every dependency and template-plan hash is recomputed by the production encoders;
failure provenance remains evidence about rejected inputs, never a certificate. -/
def verifyRecord (oldEnv newEnv : Environment) (authorization : Authorization)
    (oldRecord newRecord : BindingRecord) : MetaM Json := do
  let .declaredUnresolved oldDiagnostic := oldRecord.result
    | throwError "contract.unresolved_equivalence:original_not_unresolved"
  let .declaredUnresolved newDiagnostic := newRecord.result
    | throwError "contract.unresolved_equivalence:prototype_not_unresolved"
  requireSupportedDiagnostic oldDiagnostic
  requireSupportedDiagnostic newDiagnostic
  let some descriptor := oldRecord.descriptor
    | throwError "contract.unresolved_equivalence:unsupported_form:descriptor_missing"
  let some newDescriptor := newRecord.descriptor
    | throwError "contract.unresolved_equivalence:unsupported_form:prototype_descriptor_missing"
  let some template := descriptor.getAppFn.constName?
    | throwError "contract.unresolved_equivalence:template_head"
  let some newTemplate := newDescriptor.getAppFn.constName?
    | throwError "contract.unresolved_equivalence:prototype_template_head"
  let oldPlan ← result (selectedPlan oldEnv template)
  let newPlan ← result (selectedPlan newEnv newTemplate)
  let mapping ← completeMapping oldEnv newEnv authorization oldRecord newRecord
  unless renameName mapping template == newTemplate &&
      renameName mapping oldPlan.enrollmentOwner == newPlan.enrollmentOwner &&
      renameName mapping oldPlan.definitionOwner == newPlan.definitionOwner do
    throwError "contract.unresolved_equivalence:unauthorized_template_or_owner"
  unless (renameExpr mapping descriptor).equal newDescriptor &&
      (renameExpr mapping oldRecord.occurrence.statement).equal newRecord.occurrence.statement &&
      (renameExpr mapping oldRecord.occurrence.arena).equal newRecord.occurrence.arena &&
      oldRecord.occurrence.levelParams == newRecord.occurrence.levelParams do
    throwError "contract.unresolved_equivalence:expression_mapping"
  let oldStatement ← result (rawStatementIdentity oldRecord.occurrence.levelParams oldRecord.occurrence.statement)
  let newStatement ← result (rawStatementIdentity newRecord.occurrence.levelParams newRecord.occurrence.statement)
  check "statement.old" oldStatement.1 oldRecord.occurrence.statementIdentity
  check "statement.new" newStatement.1 newRecord.occurrence.statementIdentity
  check "statement.mapping" oldStatement.1 newStatement.1
  let (oldPrefix, oldProvenance) ← diagnosticParts oldDiagnostic
  let (_, newProvenance) ← diagnosticParts newDiagnostic
  let rule ← result (oldProvenance.getObjValAs? String "rule")
  let site ← result (oldProvenance.getObjValAs? String "site")
  let siteName ← constantName oldEnv site
  let newSite := (renameName mapping siteName).toString
  let reasons := oldPrefix.splitOn " reason="
  unless reasons.length == 2 do throwError "contract.unresolved_equivalence:diagnostic_reason"
  let kinds := reasons[1]!.splitOn " rule="
  unless kinds.length == 2 do throwError "contract.unresolved_equivalence:diagnostic_rule"
  let kind := kinds[0]!
  check "diagnostic.old.prefix" (diagnosticPrefix oldRecord.occurrence.key kind rule site) oldPrefix
  check "diagnostic.old.template" template.toString
    (← result (oldProvenance.getObjValAs? String "template_key"))
  check "diagnostic.old.plan" oldPlan.planIdentity
    (← result (oldProvenance.getObjValAs? String "plan_identity"))
  let planIdentity ← Equivalence.planIdentity oldEnv newEnv mapping descriptor
    (← result (newProvenance.getObjValAs? String "plan_identity"))
  let arguments ← mappedInputs oldEnv newEnv mapping oldProvenance "argument_inputs"
    (← argumentNames oldEnv descriptor) true
  let extractions ← mappedInputs oldEnv newEnv mapping oldProvenance "extraction_inputs"
    #[oldRecord.occurrence.realizationName] false
  let mut provenance ← setField oldProvenance "argument_inputs" arguments
  provenance ← setField provenance "extraction_inputs" extractions
  provenance ← setField provenance "plan_identity" (toJson planIdentity)
  provenance ← setField provenance "site" (toJson newSite)
  provenance ← setField provenance "template_key" (toJson newTemplate.toString)
  unless provenance == newProvenance do throwError "contract.unresolved_equivalence:complete_provenance_mapping"
  let key := keyMapping mapping oldRecord.occurrence.key
  unless key == newRecord.occurrence.key do throwError "contract.unresolved_equivalence:key_mapping"
  let diagnostic := diagnosticPrefix key kind rule newSite ++ " provenance=" ++ provenance.compress
  check "diagnostic.complete" diagnostic newDiagnostic
  let escape ← mapEscape oldEnv newEnv mapping oldRecord
  unless escape == newRecord.escape do throwError "contract.unresolved_equivalence:escape_mapping"
  let mappedRecord := { oldRecord with
    occurrence := { oldRecord.occurrence with
      key, arena := renameExpr mapping oldRecord.occurrence.arena
      unitName := renameName mapping oldRecord.occurrence.unitName
      realizationName := renameName mapping oldRecord.occurrence.realizationName
      registrationSource := TemplateAudit.sourcePath key.registrationModule }
    bindingOwner := oldRecord.bindingOwner.map (renameName mapping)
    escape, result := .declaredUnresolved diagnostic }
  let mappedJson ← inEnvironment newEnv <| TemplateBinding.recordJson mappedRecord
  let newJson ← inEnvironment newEnv <| TemplateBinding.recordJson newRecord
  unless mappedJson == newJson do throwError "contract.unresolved_equivalence:complete_record_mapping"
  return Json.mkObj [
    ("theorem", toJson key.theoremName.toString), ("verified", toJson true),
    ("state", toJson "declared_unresolved"), ("certificate", Json.null),
    ("diagnostic", toJson diagnostic), ("plan_identity", toJson planIdentity),
    ("name_mapping", toJson (mapping.map fun (a, b) => (a.toString, b.toString)))]

end LeanInformationAudit.ContractPrototype.UnresolvedEquivalence
