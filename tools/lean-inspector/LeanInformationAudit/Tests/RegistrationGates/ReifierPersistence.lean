import D5.S3.ConceptDynamics.InformationEscape.ReifierTemplates
import LeanInformationAudit.Tests.RegistrationGates.ReifierShadow
import LeanInformationAudit.Tests.RegistrationGates.ReifierChecks
import LeanInformationAudit.Tests.RegistrationPersistence

open Lean Meta LeanInformationAudit in
run_meta do
  let env ← getEnv
  let entries := (InformationRegistry.entries env).filter (·.derivedCertificate.isSome)
  unless entries.size == 7 do throwError "expected seven imported derived certificates"
  for entry in entries do
    unless env.isImportedConst entry.unitName do throwError "unit was not imported"
    match ← validatePersistedEntry env entry with
    | .error reason => throwError reason
    | .ok () => pure ()
    let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName)
    unless info.value?.any (·.equal (mkStrLit "")) do throwError "nonempty imported diagnostic"
  logInfo "P1_IMPORTED_CERTIFICATES_CHECKED count=7"

open Lean Meta LeanInformationAudit in
run_meta do
  let env ← getEnv
  let some entry := InformationRegistry.find? env
      ``LeanInformationAudit.Tests.ReifierChecks.exportedClean
    | throwError "provider_export: missing imported row"
  let some cert := entry.derivedCertificate | throwError "provider_export: missing certificate"
  unless cert.descriptor.getAppFn.isConstOf RegistrationReifier.pointwiseProvider do
    throwError "provider_export: export resolved to a wrapper"
  for name in #[entry.unitName, entry.realizationName, entry.variationWitness,
      entry.sensitivityWitness, cert.nondegenerate,
      RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName] do
    unless env.isImportedConst name do
      throwError "provider_export: missing imported generated declaration {name}"
  match ← validatePersistedEntry env entry with
  | .error reason => throwError reason
  | .ok () => logInfo "P1_A7 provider_export imported_row_and_generated_declarations accepted"
