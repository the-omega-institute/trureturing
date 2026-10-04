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



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S1.Words.Powers.substLength_pos) (type_of% (strictArena)) (type_of% (objectArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun _ => lengthZero) (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b))) (type_of% (positive_lawSensitive)) (type_of% (strict_slotSensitive)) (type_of% (Bool)) (type_of% (positive_empty)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Powers") "substLength_pos") "Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Powers") "substLength_pos") "Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds") "__primitive_realization"),
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positive_bridge,
  generated := false,
  arena := ⟨(strictArena)⟩,
  objectArena := ⟨(objectArena)⟩,
  catalog := `substitutionBounds,
  localNames := false,
  realization := .legacy (strictArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.positiveRealization) (positiveRealization.toPrimitiveBundle) ⟨(positive_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun _ => lengthZero) (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b)),
  variation := some ⟨(positive_lawSensitive)⟩,
  sensitivity := some ⟨(strict_slotSensitive)⟩,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .evidence ⟨(positive_empty)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

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



noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S1.Words.Powers.substLength_le_two) (type_of% (weakArena)) (type_of% (objectArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b) (fun _ => lengthTwo))) (type_of% (upper_lawSensitive)) (type_of% (weak_slotSensitive)) (type_of% (Bool)) (type_of% (upper_empty)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Powers") "substLength_le_two") "Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Powers") "substLength_le_two") "Reg.D5.S1.Words.Powers.GoldenDesubstitution/D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.objectArena/substitutionBounds") "__primitive_realization"),
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upper_bridge,
  generated := false,
  arena := ⟨(weakArena)⟩,
  objectArena := ⟨(objectArena)⟩,
  catalog := `substitutionBounds,
  localNames := false,
  realization := .legacy (weakArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.upperRealization) (upperRealization.toPrimitiveBundle) ⟨(upper_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseOrderRealization
    Bool (Fin 3) (instDecidableEqFin 3)
    (fun b => D5.S3.ConceptDynamics.InformationEscape.PointwiseOrderRegistrations.lengthReadout b) (fun _ => lengthTwo)),
  variation := some ⟨(upper_lawSensitive)⟩,
  sensitivity := some ⟨(weak_slotSensitive)⟩,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .evidence ⟨(upper_empty)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

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
