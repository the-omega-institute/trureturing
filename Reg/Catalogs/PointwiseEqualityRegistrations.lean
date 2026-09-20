import Reg.D5.S0.Tower.DBonacci.Substitution
import Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.Catalogs.PointwiseEqualityRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena, theoremName := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible,
      statementIdentity := "sha256:b30ce4d291640ad8d50484250e17905625944a4356233ef3b10bb285576eb0e0",
      registrationModuleName := `Reg.D5.S0.Tower.DBonacci.Substitution },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena, theoremName := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction,
      statementIdentity := "sha256:3cedb82534e585ab1c5cb122ef9b78447ce5288c441f3c5cde230fe1ea477fcc",
      registrationModuleName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena, theoremName := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible,
      statementIdentity := "sha256:b30ce4d291640ad8d50484250e17905625944a4356233ef3b10bb285576eb0e0",
      registrationModuleName := `Reg.D5.S0.Tower.DBonacci.Substitution },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.recenterArena, theoremName := `D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates.recenter_direction,
      statementIdentity := "sha256:3cedb82534e585ab1c5cb122ef9b78447ce5288c441f3c5cde230fe1ea477fcc",
      registrationModuleName := `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates }]
  companionPrefix := some `Reg.Catalogs.PointwiseEqualityRegistrations }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#seal_information_theory


section
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let entries := (InformationRegistry.entries env).filter fun entry =>
    #[`Reg.D5.S0.Tower.DBonacci.Substitution, `Reg.D5.S3.StatisticalMechanics.HardCore.SquareGridCoordinates].contains entry.registrationModuleName
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
