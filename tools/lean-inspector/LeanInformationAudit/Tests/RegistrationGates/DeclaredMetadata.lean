import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates

namespace LeanInformationAudit.Tests.DeclaredMetadata
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def capturedProjection (f : Bool → Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  let _ := TemplateBindingCertificate.evidenceRef
  cutRealization f

def capturedQuery (f : Bool → Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  let _ := TemplateBinding.records
  cutRealization f

def emptyCertificate : TemplateBindingCertificate := default
def emptyPlan : TemplateAudit.TemplatePlanData := default

def capturedValue (f : Bool → Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  let _ : Nat := emptyPlan.schemaVersion
  cutRealization f

theorem target : (137 : Nat) = 137 := rfl

run_meta do
  let cases : Array (String × Name) := #[
    ("argument_plan_identity_rejected", ``TemplateAudit.TemplatePlanData.planIdentity),
    ("argument_binding_certificate_rejected", ``TemplateBindingCertificate.evidenceRef),
    ("argument_binding_claim_rejected", ``TemplateBindingClaim.descriptor),
    ("argument_binding_record_rejected", ``BindingRecord.result),
    ("argument_validated_tag_rejected", ``TemplateBindingResult.declaredValidated),
    ("argument_plan_query_rejected", ``TemplateAudit.selectedPlan),
    ("argument_record_query_rejected", ``TemplateBinding.records),
    ("argument_inventory_query_rejected", ``TemplateBinding.inventory),
    ("argument_p1_certificate_rejected", ``AutoDerivedSemanticCertificate.statementIdentity)]
  for (label, name) in cases do
    let saved ← getEnv
    let _ ← getConstInfo name
    let result ← RegistrationGates.templateArgumentsCurrent ``target #[mkConst name] 524288
    let ok := result matches .error "forbidden_dependency:dtr.argument_audit"
    setEnv saved
    logInfo m!"[{if ok then "PASS" else "FAIL"}] {label} result={repr result}"
  let result ← RegistrationGates.templateArgumentsCurrent ``target #[mkConst ``Bool.true] 524288
  logInfo m!"[{if result.isOk then "PASS" else "FAIL"}] independent_metadata_control_accepted"
  let projected := Expr.proj ``TemplateBindingCertificate 0 (mkConst ``emptyCertificate)
  let result ← RegistrationGates.templateArgumentsCurrent ``target #[projected] 524288
  let ok := result matches .error "forbidden_dependency:dtr.argument_audit"
  logInfo m!"[{if ok then "PASS" else "FAIL"}] argument_raw_certificate_projection_rejected result={repr result}"

elab "observe_metadata_enrollment" : command => do
  for (label, name) in #[
      ("body_binding_projection_rejected", ``capturedProjection),
      ("body_binding_query_rejected", ``capturedQuery)] do
    let saved ← get
    let result ← TemplateAudit.enroll name
    let noEvidence := !(TemplateAudit.selectedPlan (← getEnv) name).isOk
    let ok := result matches .error "forbidden_dependency:E6.registered_identity"
    set saved
    logInfo m!"[{if ok && noEvidence then "PASS" else "FAIL"}] {label} result={repr result}"
  let saved ← get
  let name := (← getEnv).header.mainModule.str "rawProjection"
  let .defnInfo info ← getConstInfo ``capturedValue | throwError "setup: value definition missing"
  let value := info.value.replace fun e =>
    if e.isAppOfArity ``TemplateAudit.TemplatePlanData.schemaVersion 1 then
      some (.proj ``TemplateAudit.TemplatePlanData 0 e.getAppArgs[0]!)
    else none
  unless (value.find? fun e => e matches .proj ..).isSome do
    throwError "setup: raw projection not constructed"
  liftTermElabM <| addDecl <| .defnDecl {
    name, levelParams := info.levelParams, type := info.type, value,
    hints := .abbrev, safety := .safe }
  let result ← TemplateAudit.enroll name
  let ok := result matches .error "forbidden_dependency:E6.registered_identity"
  let noEvidence := !(TemplateAudit.selectedPlan (← getEnv) name).isOk
  set saved
  logInfo m!"[{if ok && noEvidence then "PASS" else "FAIL"}] body_raw_plan_projection_rejected result={repr result}"

observe_metadata_enrollment

end LeanInformationAudit.Tests.DeclaredMetadata
