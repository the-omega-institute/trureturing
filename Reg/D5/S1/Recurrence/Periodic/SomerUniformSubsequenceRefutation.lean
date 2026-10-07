import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration
import Reg.Support.CertificateWordRegistrationTemplates



namespace Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration
attribute [local instance] _root_.D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration.instDecidableEqCertificateWord
attribute [local instance] _root_.D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration.instDecidableEqStateCertificateArena in

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.result) (type_of% (@certificateWordRealization CertificateWord (fun word index => word index))) (type_of% (actualWord)) (Unit) := {
  unitName := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.result.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration.certificateBridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(certificateArena)⟩,
  objectArena := .law ⟨(certificateArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (certificateArena) (D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration.certificateRealization) (certificateRealization.toPrimitiveBundle) ⟨(certificateBridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (certificateBridge) (@_root_.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.result))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((certificateRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@certificateWordRealization CertificateWord (fun word index => word index)),
  variation := .evidence ⟨(certificateVariation)⟩ (by first | exact (certificateVariation) | exact ⟨_, _, (certificateVariation)⟩),
  sensitivity := .evidence ⟨(certificateSensitivity)⟩ (by exact (certificateSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (actualWord),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency.types, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation, declaration := `D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation, declaration := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation, declaration := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation, declaration := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation, declaration := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1.canonicalArenaFact, `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }

end

end Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation


noncomputable def Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration.certificateArena
noncomputable def Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Periodic\",\"SomerUniformSubsequenceRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Periodic\",\"SomerUniformSubsequenceRefutation\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation, declaration := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation, declaration := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration.certificateArena
noncomputable def Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Periodic\",\"SomerUniformSubsequenceRefutation\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Recurrence\",\"Periodic\",\"SomerUniformSubsequenceRefutation\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation, declaration := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation, declaration := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
