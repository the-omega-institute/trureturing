import Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification
import Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.Catalogs.GuardedEqualityRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena, theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model,
      statementIdentity := "sha256:ff72989c2b45d52570a4d716b0ba5064b872ce6bd51d804858fc59ab4b2c0e58",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena, theoremName := `D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer,
      statementIdentity := "sha256:a2696beef1ce0e3cb782708559f90acd25415caf6cf673804746e92d6fbcc2a1",
      registrationModuleName := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.positiveFirstArena, theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification.positive_first_experiment_identifies_model,
      statementIdentity := "sha256:ff72989c2b45d52570a4d716b0ba5064b872ce6bd51d804858fc59ab4b2c0e58",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena, theoremName := `D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer,
      statementIdentity := "sha256:a2696beef1ce0e3cb782708559f90acd25415caf6cf673804746e92d6fbcc2a1",
      registrationModuleName := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups }]
  companionPrefix := some `Reg.Catalogs.GuardedEqualityRegistrations }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#seal_information_theory


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
