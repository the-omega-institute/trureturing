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
end
