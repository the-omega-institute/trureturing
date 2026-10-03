import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations
import Reg.Support.ExistentialWitnessRegistrationTemplates



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

noncomputable def _root_.Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena (@Exists.{1} (Bool → Bool) fun (C₁ : Bool → Bool) => @Exists.{1} (Bool → Bool) fun (C₂ : Bool → Bool) => @Exists.{1} Bool fun (b₁ : Bool) => @Exists.{1} Bool fun (b₂ : Bool) => And (@Ne.{1} (Bool → Bool) C₁ C₂) (@D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.MutuallyRecognized.{0, 0, 0} Bool Bool Bool (@Set.univ.{0} Bool) C₁ C₂ (@Prod.mk.{0, 0} Bool Bool b₁ b₂))) D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionRealization D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognition_bridge D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts) (type_of% (recognitionArena)) (type_of% (recognitionArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Bool → Bool) × Bool × Bool) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w) true))) (type_of% (recognition_lawSensitive)) (type_of% (recognition_slotSensitive)) (Unit) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognition_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(recognitionArena)⟩,
  objectArena := ⟨(recognitionArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (recognitionArena) (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionRealization) (recognitionRealization.toPrimitiveBundle) ⟨(recognition_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Bool → Bool) × Bool × Bool) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w) true)),
  variation := some ⟨(recognition_lawSensitive)⟩,
  sensitivity := some ⟨(recognition_slotSensitive)⟩,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

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
