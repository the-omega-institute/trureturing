import D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
import D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations
import D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations
import D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
import D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

open Lean

-- Check published diagnostics as well as command exit status. A successful
-- compilation containing a failed provenance registration is a regression.
run_cmd do
  let env := (← getEnv).setExporting false
  let modules : Array (Name × Nat) := #[
    (`D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrations, 3),
    (`D5.S3.ConceptDynamics.InformationEscape.PointwiseDisequalityRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations, 2),
    (`D5.S3.ConceptDynamics.InformationEscape.TemplateShadow, 10)]
  for (moduleName, expected) in modules do
    let some index := env.getModuleIdx? moduleName
      | throwError "[FAIL] DevConservation: missing {moduleName}"
    let mut count : Nat := 0
    let mut findings : Nat := 0
    for name in env.header.moduleData[index]!.constNames do
      unless name.getString! == "__information_registration_diagnostic" do continue
      count := count + 1
      let some (.defnInfo info) := env.find? name
        | throwError "[FAIL] DevConservation: missing diagnostic {name}"
      let .lit (.strVal message) := info.value
        | throwError "[FAIL] DevConservation: nonliteral diagnostic {name}"
      if message.startsWith "IE-C050 " then
        findings := findings + 1
        logError m!"[FAIL] DevConservation/{moduleName}: {message}"
    unless count == expected && findings == 0 do
      throwError "[FAIL] DevConservation/{moduleName}: expected {expected}; count={count}; IE-C050={findings}"
    logInfo m!"[PASS] DevConservation/{moduleName}: registrations={count} IE-C050=0"
