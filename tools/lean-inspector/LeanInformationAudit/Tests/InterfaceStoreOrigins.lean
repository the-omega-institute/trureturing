import LeanInformationAudit.Tests.Assessment
import LeanInformationAudit.Tests.RegistrationGates.DeclaredRegistration
import LeanInformationAudit.Census.Stream

test_imported_assessment

open Lean LeanInformationAudit LeanInformationAudit.TemplateBinding Lean.Elab.Command

-- The raw olean reader reports native input containers, without loading a
-- persisted verdict or interpreting the asserted registration owner as origin.
run_cmd do
  let env ← getEnv
  let source := `LeanInformationAudit.Tests.RegistrationGates.DeclaredSource
  let producer := `LeanInformationAudit.Tests.RegistrationGates.DeclaredRegistration
  let theoremName := `LeanInformationAudit.Tests.DeclaredSource.original
  for owner in #[source, producer] do
    let some index := env.getModuleIdx? owner | throwError "[FAIL] origin_fixture_missing"
    let rows := CensusStream.registryRecords owner.toString env.header.moduleData[index.toNat]!
    let bindings ← ofExcept <| rows.getObjValAs? (Array Json) "bindings"
    let matching := bindings.filter fun row =>
      (row.getObjVal? "key").toOption == some (nameJson theoremName)
    unless matching.size == (if owner == source then 0 else 2) &&
        matching.all (fun row => (row.getObjValAs? String "module").toOption ==
          some owner.toString) do throwError "[FAIL] native_binding_origins"
  let raw := RegistrationInputs.owned env
  let some (actualOwner, firstInput) := raw[0]? | throwError "[FAIL] raw_registration_owner"
  unless raw.size == 1 && actualOwner == producer &&
      firstInput.entry.registrationModuleName == producer do
    throwError "[FAIL] raw_registration_owner"
  let assessed ← liftTermElabM <| assessJoined
    (← RegistrationAssessmentInput.capture env.header.mainModule)
  unless assessed.size == 1 && assessed[0]!.bindingOwner == some producer &&
      (assessed[0]!.result matches .declaredValidated _) do
    throwError "[FAIL] report_rebuilds_binding"
  logInfo "[PASS] native_binding_origins raw_registration_owner report_rebuilds_binding"

run_cmd liftCoreM do
  let env ← getEnv
  let some (_, original) := (RegistrationInputs.owned env).find? (fun (_, input) =>
      input.entry.registrationModuleName == `LeanInformationAudit.Tests.RegistrationGates.DeclaredRegistration)
    | throwError "missing raw registration fixture"
  for (label, forged) in [
      ("dtr.input_owner", { original with entry :=
        { original.entry with registrationModuleName := `wrongOwner } }),
      ("dtr.input_source", { original with
        entry := { original.entry with registrationModuleName := (← getEnv).header.mainModule }
        sourceText := "forged source" })] do
    setEnv (RegistrationInputs.add env forged)
    let rejected ← try
      replayRegistrationInputs (← RegistrationAssessmentInput.capture env.header.mainModule)
      pure false
    catch error => pure ((← error.toMessageData.toString).contains label)
    unless rejected do throwError "[FAIL] raw input rejection: {label}"
    setEnv env
    logInfo m!"[PASS] raw_input_rejected {label}"

-- A transient result is a product, never an input to rebuilding the report.
run_cmd do
  let saved ← getEnv
  let original ← liftTermElabM <| assessJoined
    (← RegistrationAssessmentInput.capture saved.header.mainModule)
  let some row := original[0]? | throwError "[FAIL] missing_assessed_row"
  modifyEnv fun env => addRecord env { row with result := .undeclared, descriptor := none }
  liftCoreM <| replayRegistrationInputs
    (← RegistrationAssessmentInput.capture saved.header.mainModule)
  let rebuilt ← liftTermElabM <| assessJoined
    (← RegistrationAssessmentInput.capture saved.header.mainModule)
  let some rebuiltRow := rebuilt[0]? | throwError "[FAIL] transient_verdict_missing"
  unless rebuilt.size == 1 && (rebuiltRow.result matches .declaredValidated _) do
    throwError "[FAIL] transient_verdict_cannot_override_raw_input"
  setEnv saved
  logInfo "[PASS] transient_verdict_cannot_override_raw_input"
