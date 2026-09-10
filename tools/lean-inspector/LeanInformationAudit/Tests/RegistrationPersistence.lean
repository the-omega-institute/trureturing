import LeanInformationAudit.Tests.RegistrationErrors

open Lean

set_option linter.style.longLine false

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
  let importedUnitName :=
    `LeanInformationAudit.Tests.RegistrationErrors.ImportedFixture.importedExample
      |>.str "__information_unit"
  unless importedEntry.unitName == importedUnitName do
    throwError "imported registration lookup returned the wrong unit"
  unless env.contains importedEntry.unitName do
    throwError "resolved companion declaration is missing"

#guard_msgs in
run_cmd do
  let env ← getEnv
  let some entry := InformationRegistry.find? env
      `LeanInformationAudit.Tests.RegistrationErrors.nativeExample
    | throwError "missing persisted native registration"
  match ← Lean.Elab.Command.liftTermElabM <| validatePersistedEntry env entry with
  | .ok () => pure ()
  | .error message => throwError message

/-- error: IE-C002 DuplicateRegistration object_arena=LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena theorem_name=LeanInformationAudit.Tests.RegistrationErrors.legacyExample registration_modules=["LeanInformationAudit.Tests.RegistrationErrors","LeanInformationAudit.Tests.RegistrationPersistence"] count=2 -/
#guard_msgs (error) in
register_information_theorem
  LeanInformationAudit.Tests.RegistrationErrors.legacyExample
  in LeanInformationAudit.Tests.RegistrationErrors.fixtureLawArena
  primitives LeanInformationAudit.Tests.RegistrationErrors.fixtureBundle
  realization LeanInformationAudit.Tests.RegistrationErrors.legacyRealization

end LeanInformationAudit.Tests.RegistrationPersistence
