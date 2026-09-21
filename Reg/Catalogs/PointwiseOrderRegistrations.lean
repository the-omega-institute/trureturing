import Reg.D5.S1.Words.Powers.GoldenDesubstitution
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.Catalogs.PointwiseOrderRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_pos,
      statementIdentity := "sha256:c7c23089a7484f261005f23167c5b1588d1b6c64d15914dbdc36e4fe672715db",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_le_two,
      statementIdentity := "sha256:17684442190c21bc68cd745b6c7fb89435f2c2c21f60801dbbb02dbc9e3b6eec",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_pos,
      statementIdentity := "sha256:c7c23089a7484f261005f23167c5b1588d1b6c64d15914dbdc36e4fe672715db",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena, theoremName := `D5.S1.Words.Powers.substLength_le_two,
      statementIdentity := "sha256:17684442190c21bc68cd745b6c7fb89435f2c2c21f60801dbbb02dbc9e3b6eec",
      registrationModuleName := `Reg.D5.S1.Words.Powers.GoldenDesubstitution }]
  companionPrefix := some `Reg.Catalogs.PointwiseOrderRegistrations }

#seal_information_theory


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
