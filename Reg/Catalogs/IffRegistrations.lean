import Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
import Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.Catalogs.IffRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled,
      statementIdentity := "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff,
      statementIdentity := "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f",
      registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled,
      statementIdentity := "sha256:48183359aa256091e3dfc2a80a5352b99a62f3ff03446236a0e6d9bd82fa988e",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff,
      statementIdentity := "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f",
      registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }]
  companionPrefix := some `Reg.Catalogs.IffRegistrations }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#seal_information_theory


section
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let entries := (InformationRegistry.entries env).filter fun entry =>
    #[`Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain, `Reg.D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling].contains entry.registrationModuleName
  unless entries.size == 2 do throwError "relocated production occurrence count"
  for entry in entries do
    if true then
      let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName)
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0],readout[1]]"
      else
        logWarning diagnostic
end
