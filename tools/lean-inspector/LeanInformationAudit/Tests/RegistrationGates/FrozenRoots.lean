import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration
import LeanInformationAudit.Tests.Seal.M3

open Lean

-- Inspect published diagnostics even when registration itself compiles successfully.
run_cmd do
  let env := (← getEnv).setExporting false
  let roots : Array (Name × Nat) := #[
    (`D5.S3.ConceptDynamics.InformationEscape.InformationRoot, 11),
    (`D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot, 0),
    (`D5.S3.ConceptDynamics.InformationEscape.TemplateShadow, 10),
    (`D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration, 2),
    (`LeanInformationAudit.Tests.Seal.M3, 7)]
  let mut total : Nat := 0
  for (root, expected) in roots do
    let some idx := env.getModuleIdx? root
      | throwError "[FAIL] FrozenRootsCompile: module not loaded: {root}"
    let mut checked : Nat := 0
    let mut findings : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      unless name.getString! == "__information_registration_diagnostic" do continue
      let some (.defnInfo info) := env.find? name
        | throwError "[FAIL] FrozenRootsCompile: missing metadata: {name}"
      let .lit (.strVal message) := info.value
        | throwError "[FAIL] FrozenRootsCompile: malformed metadata: {name}"
      checked := checked + 1
      if message.startsWith "IE-C050 " then
        findings := findings + 1
        logInfo m!"{message}"
    total := total + findings
    logInfo m!"FrozenRootsCompile root={root} registrations={checked} IE-C050={findings}"
    unless checked == expected do
      logError m!"[FAIL] FrozenRootMetadataCount: {root}: {checked} != {expected}"
  unless total == 0 do
    throwError "[FAIL] FrozenRootsCompile: {total} IE-C050 findings"
  logInfo "[PASS] FrozenRootsCompile"
