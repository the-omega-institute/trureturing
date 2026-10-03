import Reg.Catalogs.PointwiseOrderRegistrations
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

section
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let entries := (InformationRegistry.entries env).filter fun entry =>
    #[`Reg.D5.S1.Words.Powers.GoldenDesubstitution].contains entry.registrationModuleName
  unless entries.size == 2 do throwError "relocated production occurrence count"
  for entry in entries do
    let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName)
    let some (.lit (.strVal diagnostic)) := info.value?
      | throwError "registration diagnostic is not a literal"
    if diagnostic.isEmpty then
      logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0],readout[1]]"
    else
      logWarning diagnostic
end
