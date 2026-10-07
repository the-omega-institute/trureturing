import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
import Reg.Support.PointwiseOrderRegistrations



namespace Reg.D5.S1.Words.Powers.GoldenDesubstitution

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S1.Words.Powers _root_.D5.S0.Tower.GoldenGapWord

theorem _root_.D5.S1.Words.Powers.substLength_pos.«Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds».__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.strictArena (∀ (b : Bool), @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.length.{0} Bool (D5.S0.Tower.GoldenGapWord.subst b))) D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positiveRealization := D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positive_bridge



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Words.Powers.substLength_pos) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun _ => lengthZero) (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b))) (type_of% (Bool)) (type_of% (positive_empty)) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Powers") "substLength_pos") "Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Powers") "substLength_pos") "Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds") "__primitive_realization"),
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positive_bridge,
  generated := false,
  arena := .law ⟨(strictArena)⟩,
  objectArena := .finite ⟨(objectArena)⟩,
  catalog := `substitutionBounds,
  localNames := false,
  realization := .legacy (strictArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positiveRealization) (positiveRealization.toPrimitiveBundle) ⟨(positive_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (positive_bridge) (@_root_.D5.S1.Words.Powers.substLength_pos))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((positiveRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun _ => lengthZero) (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b)),
  variation := .evidence ⟨(positive_lawSensitive)⟩ (by first | exact (positive_lawSensitive) | exact ⟨_, _, (positive_lawSensitive)⟩),
  sensitivity := .evidence ⟨(strict_slotSensitive)⟩ (by exact (strict_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .evidence ⟨(positive_empty)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Powers.GoldenDesubstitution, declaration := `D5.S1.Words.Powers.substLength_pos, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1.canonicalObjectArenaFact] },
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
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S1.Words.Powers _root_.D5.S0.Tower.GoldenGapWord

theorem _root_.D5.S1.Words.Powers.substLength_le_two.«Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds».__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.weakArena (∀ (b : Bool), @LE.le.{0} Nat instLENat (@List.length.{0} Bool (D5.S0.Tower.GoldenGapWord.subst b)) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upperRealization := D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upper_bridge



noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Words.Powers.substLength_le_two) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b) (fun _ => lengthTwo))) (type_of% (Bool)) (type_of% (upper_empty)) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Powers") "substLength_le_two") "Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Powers") "substLength_le_two") "Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds") "__primitive_realization"),
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upper_bridge,
  generated := false,
  arena := .law ⟨(weakArena)⟩,
  objectArena := .finite ⟨(objectArena)⟩,
  catalog := `substitutionBounds,
  localNames := false,
  realization := .legacy (weakArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upperRealization) (upperRealization.toPrimitiveBundle) ⟨(upper_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (upper_bridge) (@_root_.D5.S1.Words.Powers.substLength_le_two))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((upperRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b) (fun _ => lengthTwo)),
  variation := .evidence ⟨(upper_lawSensitive)⟩ (by first | exact (upper_lawSensitive) | exact ⟨_, _, (upper_lawSensitive)⟩),
  sensitivity := .evidence ⟨(weak_slotSensitive)⟩ (by exact (weak_slotSensitive)),
  partialSensitivity := none,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .evidence ⟨(upper_empty)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Powers.GoldenDesubstitution, declaration := `D5.S1.Words.Powers.substLength_le_two, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2.canonicalArenaFact, `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2.canonicalObjectArenaFact] },
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
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S1.Words.Powers _root_.D5.S0.Tower.GoldenGapWord
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positive_bridge.toTheoremUnit _root_.D5.S1.Words.Powers.substLength_pos).Statement =
    (∀ b : Bool, 0 < (subst b).length) := rfl
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations
open PointwiseRegistrationTemplates LeanInformationAudit
open EscapeRecord _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S1.Words.Powers _root_.D5.S0.Tower.GoldenGapWord
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upper_bridge.toTheoremUnit _root_.D5.S1.Words.Powers.substLength_le_two).Statement =
    (∀ b : Bool, (subst b).length ≤ 2) := rfl
end

end Reg.D5.S1.Words.Powers.GoldenDesubstitution


noncomputable def Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.strictArena
noncomputable def Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Powers\",\"GoldenDesubstitution\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Powers\",\"GoldenDesubstitution\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.Arena.{0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena
noncomputable def Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Powers\",\"GoldenDesubstitution\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Powers\",\"GoldenDesubstitution\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.weakArena
noncomputable def Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Powers\",\"GoldenDesubstitution\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Powers\",\"GoldenDesubstitution\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.Arena.{0} :=
  D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena
noncomputable def Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Powers\",\"GoldenDesubstitution\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Powers\",\"GoldenDesubstitution\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Powers.GoldenDesubstitution, declaration := `Reg.D5.S1.Words.Powers.GoldenDesubstitution.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
