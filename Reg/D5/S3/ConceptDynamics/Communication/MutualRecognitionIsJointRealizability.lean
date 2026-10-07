import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
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



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Bool → Bool) × Bool × Bool) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w) true))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognition_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(recognitionArena)⟩,
  objectArena := .law ⟨(recognitionArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (recognitionArena) (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionRealization) (recognitionRealization.toPrimitiveBundle) ⟨(recognition_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (recognition_bridge) (@_root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((recognitionRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates.existentialWitnessRealization ((Bool → Bool) × (Bool → Bool) × Bool × Bool) (fun w => D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w = true) (fun w => instDecidableEqBool (D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionReadout w) true)),
  variation := .evidence ⟨(recognition_lawSensitive)⟩ (by first | exact (recognition_lawSensitive) | exact ⟨_, _, (recognition_lawSensitive)⟩),
  sensitivity := .evidence ⟨(recognition_slotSensitive)⟩ (by exact (recognition_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability, declaration := `D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability, declaration := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability, declaration := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability, declaration := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability, declaration := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1.canonicalArenaFact, `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }

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
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognition_bridge.toTheoremUnit _root_.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.mutual_recognition_does_not_require_equal_concepts).Statement =
    (∃ (C₁ C₂ : Bool → Bool) (b₁ b₂ : Bool),
      C₁ ≠ C₂ ∧ MutuallyRecognized Set.univ C₁ C₂ (b₁, b₂)) := rfl
end

end Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability


noncomputable def Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena
noncomputable def Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Communication\",\"MutualRecognitionIsJointRealizability\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Communication\",\"MutualRecognitionIsJointRealizability\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability, declaration := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability, declaration := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrations.recognitionArena
noncomputable def Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Communication\",\"MutualRecognitionIsJointRealizability\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"ConceptDynamics\",\"Communication\",\"MutualRecognitionIsJointRealizability\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability, declaration := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability, declaration := `Reg.D5.S3.ConceptDynamics.Communication.MutualRecognitionIsJointRealizability.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
