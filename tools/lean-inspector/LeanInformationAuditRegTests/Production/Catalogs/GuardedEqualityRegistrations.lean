import Reg.Catalogs.GuardedEqualityRegistrations
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand

section
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let entries := (InformationRegistry.entries env).filter fun entry =>
    #[`Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification, `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups].contains entry.registrationModuleName
  unless entries.size == 2 do throwError "relocated production occurrence count"
  for entry in entries do
    let name := RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName
    let info ← getConstInfo name
    let some (.lit (.strVal diagnostic)) := info.value?
      | throwError "registration diagnostic is not a literal"
    if diagnostic.isEmpty then
      logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} \
        support=[readout[0],readout[1],readout[2]]"
    else
      logWarning diagnostic
end
