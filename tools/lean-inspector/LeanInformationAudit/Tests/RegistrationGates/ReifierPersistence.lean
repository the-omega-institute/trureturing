import LeanInformationAudit.Tests.RegistrationGates.ReifierShadow
import LeanInformationAudit.Tests.RegistrationGates.ReifierChecks
import LeanInformationAudit.Tests.RegistrationPersistence

open Lean Meta LeanInformationAudit in
run_meta do
  let env ← getEnv
  let entries := (InformationRegistry.entries env).filter (·.derivedCertificate.isSome)
  unless entries.size == 4 do throwError "expected four imported derived certificates"
  for entry in entries do
    unless env.isImportedConst entry.unitName do throwError "unit was not imported"
    match ← validatePersistedEntry env entry with
    | .error reason => throwError reason
    | .ok () => pure ()
    let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName)
    unless info.value?.any (·.equal (mkStrLit "")) do throwError "nonempty imported diagnostic"
  logInfo "P1_IMPORTED_CERTIFICATES_CHECKED count=4"
