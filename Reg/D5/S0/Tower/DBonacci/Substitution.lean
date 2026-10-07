import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
import Reg.Support.PointwiseEqualityRegistrations



namespace Reg.D5.S0.Tower.DBonacci.Substitution

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Tower.DBonacci.Substitution
open _root_.D5.S0.Tower.Tribonacci.Substitution (TribonacciGapLetter gapLetterSubstitution)



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 3) (instDecidableEqFin 3)
    (fun label => label) (fun label => label))) (type_of% (Fin 3)) (type_of% (substitution_empty)) := {
  unitName := `Reg.D5.S0.Tower.DBonacci.Substitution.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitution_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(substitutionArena)⟩,
  objectArena := .law ⟨(substitutionArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (substitutionArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionRealization) (substitutionRealization.toPrimitiveBundle) ⟨(substitution_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (substitution_bridge) (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((substitutionRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 3) (instDecidableEqFin 3)
    (fun label => label) (fun label => label)),
  variation := .evidence ⟨(substitution_lawSensitive)⟩ (by first | exact (substitution_lawSensitive) | exact ⟨_, _, (substitution_lawSensitive)⟩),
  sensitivity := .evidence ⟨(substitution_slotSensitive)⟩ (by exact (substitution_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := some (Fin 3),
  sourceSelection := none,
  continuation := .evidence ⟨(substitution_empty)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Tower.DBonacci.Substitution, declaration := `D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Tower.DBonacci.Substitution, declaration := `Reg.D5.S0.Tower.DBonacci.Substitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Tower.DBonacci.Substitution, declaration := `Reg.D5.S0.Tower.DBonacci.Substitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Tower.DBonacci.Substitution, declaration := `Reg.D5.S0.Tower.DBonacci.Substitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Tower.DBonacci.Substitution, declaration := `Reg.D5.S0.Tower.DBonacci.Substitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Tower.DBonacci.Substitution.registration_1.canonicalArenaFact, `Reg.D5.S0.Tower.DBonacci.Substitution.registration_1.canonicalObjectArenaFact] },
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
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S0.Tower.DBonacci.Substitution
open _root_.D5.S0.Tower.Tribonacci.Substitution (TribonacciGapLetter gapLetterSubstitution)
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitution_bridge.toTheoremUnit _root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible).Statement =
    (∀ label : Fin 3, (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel =
      gapLetterSubstitution (tribonacciGapLetterOfLabel label.1)) := rfl
end

end Reg.D5.S0.Tower.DBonacci.Substitution


noncomputable def Reg.D5.S0.Tower.DBonacci.Substitution.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena
noncomputable def Reg.D5.S0.Tower.DBonacci.Substitution.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"DBonacci\",\"Substitution\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"DBonacci\",\"Substitution\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Tower.DBonacci.Substitution, declaration := `Reg.D5.S0.Tower.DBonacci.Substitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Tower.DBonacci.Substitution, declaration := `Reg.D5.S0.Tower.DBonacci.Substitution.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Tower.DBonacci.Substitution.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena
noncomputable def Reg.D5.S0.Tower.DBonacci.Substitution.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"DBonacci\",\"Substitution\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"DBonacci\",\"Substitution\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Tower.DBonacci.Substitution, declaration := `Reg.D5.S0.Tower.DBonacci.Substitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Tower.DBonacci.Substitution, declaration := `Reg.D5.S0.Tower.DBonacci.Substitution.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
