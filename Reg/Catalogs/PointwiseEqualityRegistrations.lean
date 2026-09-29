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

#seal_information_theory


section
open LeanInformationAudit
end
