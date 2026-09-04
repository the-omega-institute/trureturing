import LeanInformationAudit.Tests.RegistrationErrors

open Lean

namespace LeanInformationAudit.Tests.RegistrationPersistence

/-- info: 2 -/
#guard_msgs in
run_cmd do
  let entries := InformationRegistry.entries (← getEnv)
  logInfo m!"{entries.size}"

#guard_msgs in
run_cmd do
  let env ← getEnv
  unless InformationRegistry.hasTheorem env
      `LeanInformationAudit.Tests.RegistrationErrors.nativeExample do
    throwError "missing persisted native registration"
  unless InformationRegistry.hasTheorem env
      `LeanInformationAudit.Tests.RegistrationErrors.legacyExample do
    throwError "missing persisted legacy registration"
  let some legacyEntry := InformationRegistry.find? env
      `LeanInformationAudit.Tests.RegistrationErrors.legacyExample
    | throwError "legacy registration lookup failed"
  unless legacyEntry.unitName ==
      `LeanInformationAudit.Tests.RegistrationErrors.legacyExample.__information_unit do
    throwError "legacy registration lookup returned the wrong unit"

end LeanInformationAudit.Tests.RegistrationPersistence
