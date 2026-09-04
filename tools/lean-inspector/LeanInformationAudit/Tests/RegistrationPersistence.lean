import LeanInformationAudit.Tests.RegistrationErrors

open Lean

namespace LeanInformationAudit.Tests.RegistrationPersistence

/-- info: 3 -/
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
  unless InformationRegistry.hasTheorem env
      `LeanInformationAudit.Tests.RegistrationErrors.ImportedFixture.importedExample do
    throwError "missing persisted imported registration"
  let some legacyEntry := InformationRegistry.find? env
      `LeanInformationAudit.Tests.RegistrationErrors.legacyExample
    | throwError "legacy registration lookup failed"
  unless legacyEntry.unitName ==
      `LeanInformationAudit.Tests.RegistrationErrors.legacyExample.__information_unit do
    throwError "legacy registration lookup returned the wrong unit"
  let some importedEntry := InformationRegistry.find? env
      `LeanInformationAudit.Tests.RegistrationErrors.ImportedFixture.importedExample
    | throwError "imported registration lookup failed"
  unless importedEntry.unitName ==
      `LeanInformationAudit.Tests.RegistrationErrors.ImportedFixture.importedExample.__information_unit do
    throwError "imported registration lookup returned the wrong unit"
  unless env.contains importedEntry.unitName do
    throwError "resolved companion declaration is missing"

end LeanInformationAudit.Tests.RegistrationPersistence
