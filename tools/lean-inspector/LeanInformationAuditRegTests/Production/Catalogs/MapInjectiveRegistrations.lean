import Reg.Catalogs.MapInjectiveRegistrations
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand

section
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let entries := (InformationRegistry.entries env).filter fun entry =>
    #[`Reg.D5.S0.History.Coding.EventCodeIntertranslation, `Reg.D5.S3.QuantumContext.ProjectionValuationObstruction].contains entry.registrationModuleName
  unless entries.size == 3 do throwError "relocated production occurrence count"
  for entry in entries do
    let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName)
    let some (.lit (.strVal diagnostic)) := info.value?
      | throwError "registration diagnostic is not a literal"
    if diagnostic.isEmpty then
      logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0]]"
    else
      logWarning diagnostic
end
