import LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecar
import LeanInformationAudit.Census.Stream

open Lean LeanInformationAudit

-- Existing independently compiled source and sidecar exercise the raw olean reader.
run_cmd do
  let env ← getEnv
  let source := `LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecarSource
  let sidecar := `LeanInformationAudit.Tests.RegistrationGates.DeclaredSidecar
  let theoremName := `LeanInformationAudit.Tests.DeclaredSidecarSource.original
  for owner in #[source, sidecar] do
    let some index := env.getModuleIdx? owner
      | throwError "[FAIL] existing_origin_fixture_missing"
    let rows := CensusStream.registryRecords owner.toString env.header.moduleData[index.toNat]!
    let bindings ← ofExcept <| rows.getObjValAs? (Array Json) "bindings"
    let matching := bindings.filter fun row =>
      (row.getObjVal? "key").toOption == some (nameJson theoremName)
    unless matching.size == 1 do throwError "[FAIL] native_binding_origin_count"
    unless (matching[0]!.getObjValAs? String "module").toOption == some owner.toString do
      throwError "[FAIL] native_binding_origin_label"
  logInfo "[PASS] native_binding_origin_count native_binding_origin_label"
