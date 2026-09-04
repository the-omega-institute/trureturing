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

end LeanInformationAudit.Tests.RegistrationPersistence
