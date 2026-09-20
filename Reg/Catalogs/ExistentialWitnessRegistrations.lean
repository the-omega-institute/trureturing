import Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape
import Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.Catalogs.ExistentialWitnessRegistrations
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena, theoremName := `D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint,
      statementIdentity := "sha256:6229f4053788af2b620d04f5df8b8ead8963f1ffb30952697ec73dca847c6886",
      registrationModuleName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena, theoremName := `D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts,
      statementIdentity := "sha256:9fe223b46afd61e89e3883878aabd3f4184a39542015b7c4e40ec8c599a7c46c",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.capturedArena, theoremName := `D5.S0.Diagonal.Lawvere.QualitativeEscape.exists_captured_listing_of_fixedPoint,
      statementIdentity := "sha256:6229f4053788af2b620d04f5df8b8ead8963f1ffb30952697ec73dca847c6886",
      registrationModuleName := `Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena, theoremName := `D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts,
      statementIdentity := "sha256:9fe223b46afd61e89e3883878aabd3f4184a39542015b7c4e40ec8c599a7c46c",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability }]
  companionPrefix := some `Reg.Catalogs.ExistentialWitnessRegistrations }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
#seal_information_theory


section
open LeanInformationAudit
open Lean in
run_meta do
  let env ← getEnv
  let entries := (InformationRegistry.entries env).filter fun entry =>
    #[`Reg.D5.S0.Diagonal.Lawvere.QualitativeEscape, `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability].contains entry.registrationModuleName
  unless entries.size == 2 do throwError "relocated production occurrence count"
  for entry in entries do
    if true then
      let info ← getConstInfo (RegistrationGates.diagnosticName entry.unitName entry.registrationModuleName)
      let some (.lit (.strVal diagnostic)) := info.value?
        | throwError "registration diagnostic is not a literal"
      if diagnostic.isEmpty then
        logInfo m!"REGISTRATION_WITNESSES_CHECKED {entry.theoremName} support=[readout[0]]"
      else
        logWarning diagnostic
end
