import LeanInformationAudit.Tests.Assessment
import LeanInformationAudit.Tests.RegistrationGates.IndexWork.Selected

test_imported_assessment

namespace LeanInformationAudit.Tests.DeclaredFraming
open Lean Meta Elab Command TemplateAudit

private def rejectedInput (input : TemplateEnrollmentInput) (reason : String) :
    CommandElabM Unit := do
  let saved ← getEnv
  modifyEnv (TemplateEnrollmentInputs.add · input)
  let changed ← getEnv
  let rejected ← try
    liftCoreM <| replayRegistrationInputs
      (← RegistrationAssessmentInput.capture saved.header.mainModule)
    pure false
  catch error => pure ((← error.toMessageData.toString) == reason)
  unless rejected && sameRegistrationEnvironment changed (← getEnv) do
    throwError "[FAIL] raw input rejection or transaction: {reason}"
  setEnv saved
  logInfo m!"[PASS] {reason}"

run_cmd do
  let env ← getEnv
  let owner := env.header.mainModule
  let sourceText ← IO.FS.readFile (sourcePath owner)
  let options ← getOptions
  let name := `DTRIndex.A.selected
  let .ok selected := selectedPlan env name | throwError "setup: selected enrollment absent"
  let originals := TemplateEnrollmentInputs.owned env
  unless originals.any (fun (actual, input) =>
      actual == selected.enrollmentOwner && input.owner == actual && input.name == name) do
    throwError "[FAIL] enrollment_native_owner"
  let wrongOwner : TemplateEnrollmentInput :=
    { owner := `WrongOwner, name, version := 1, constructors := #[], sourceText, options }
  rejectedInput wrongOwner "incomplete_closure:E7.import_owner"
  let changedSource : TemplateEnrollmentInput :=
    { owner, name, version := 1, constructors := #[], sourceText := sourceText ++ " changed", options }
  rejectedInput changedSource "incomplete_closure:dtr.input_source"
  let .ok bytes := planEncoding selected | throwError "setup: plan encoding absent"
  unless bytes.size == selected.serializedBytes && Sha256.hex bytes == selected.planIdentity do
    throwError "[FAIL] current_plan_identity"
  let reset := resetTemplatePlans env
  unless !(selectedPlan reset name).isOk &&
      (TemplateEnrollmentInputs.owned reset).size == originals.size do
    throwError "[FAIL] transient_plans_do_not_replace_raw_inputs"
  setEnv reset
  liftCoreM <| replayRegistrationInputs (← RegistrationAssessmentInput.capture owner)
  let .ok rebuilt := selectedPlan (← getEnv) name | throwError "[FAIL] raw_input_reassessment"
  unless rebuilt.planIdentity == selected.planIdentity do
    throwError "[FAIL] raw_input_reassessment_identity"
  setEnv env
  logInfo "[PASS] enrollment_native_owner current_plan_identity \
    transient_plans_do_not_replace_raw_inputs raw_input_reassessment_identity"

end LeanInformationAudit.Tests.DeclaredFraming
