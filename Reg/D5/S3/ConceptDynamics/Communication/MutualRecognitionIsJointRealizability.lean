import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
import Reg.Support.ExistentialWitnessRegistrationTemplates

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena, theoremName := `D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts,
      statementIdentity := "sha256:9fe223b46afd61e89e3883878aabd3f4184a39542015b7c4e40ec8c599a7c46c",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena, theoremName := `D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts,
      statementIdentity := "sha256:9fe223b46afd61e89e3883878aabd3f4184a39542015b7c4e40ec8c599a7c46c",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability }

namespace Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
open ExistentialWitnessRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability
open _root_.D5.S3.ConceptDynamics.ConceptJoinUniversal

register_information_theorem _root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts in recognitionArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Bool → Bool) × Bool × Bool) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w) true))
  primitives recognitionRealization.toPrimitiveBundle realization recognition_bridge
  variation recognition_lawSensitive sensitivity recognition_slotSensitive
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
open ExistentialWitnessRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability
open _root_.D5.S3.ConceptDynamics.ConceptJoinUniversal
example : _root_.Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts.__information_unit.Statement =
    (∃ (C₁ C₂ : Bool → Bool) (b₁ b₂ : Bool),
      C₁ ≠ C₂ ∧ MutuallyRecognized Set.univ C₁ C₂ (b₁, b₂)) := rfl
end

end Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability
