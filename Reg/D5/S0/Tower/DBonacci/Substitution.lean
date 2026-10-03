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

noncomputable def _root_.Reg.D5.S0.Tower.DBonacci.Substitution.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionArena (∀ (label : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))), @Eq.{1} (List.{0} D5.S0.Tower.Tribonacci.Substitution.TribonacciGapLetter) (@List.map.{0, 0} Nat D5.S0.Tower.Tribonacci.Substitution.TribonacciGapLetter D5.S0.Tower.DBonacci.Substitution.tribonacciGapLetterOfLabel (D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) label))) (D5.S0.Tower.Tribonacci.Substitution.gapLetterSubstitution (D5.S0.Tower.DBonacci.Substitution.tribonacciGapLetterOfLabel (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) label)))) D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionRealization D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitution_bridge D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible) (type_of% (substitutionArena)) (type_of% (substitutionArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 3) (instDecidableEqFin 3)
    (fun label => label) (fun label => label))) (type_of% (substitution_lawSensitive)) (type_of% (substitution_slotSensitive)) (type_of% (Fin 3)) (type_of% (substitution_empty)) (Unit) := {
  unitName := `Reg.D5.S0.Tower.DBonacci.Substitution.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitution_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(substitutionArena)⟩,
  objectArena := ⟨(substitutionArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (substitutionArena) (D5.S3.ConceptDynamics.InformationEscape.PointwiseEqualityRegistrations.substitutionRealization) (substitutionRealization.toPrimitiveBundle) ⟨(substitution_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates.homogeneousPointwiseEqRealization
    (Fin 3) (Fin 3) (instDecidableEqFin 3)
    (fun label => label) (fun label => label)),
  variation := some ⟨(substitution_lawSensitive)⟩,
  sensitivity := some ⟨(substitution_slotSensitive)⟩,
  escapeFrom := some (Fin 3),
  sourceSelection := none,
  continuation := .evidence ⟨(substitution_empty)⟩,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

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
example : _root_.Reg.D5.S0.Tower.DBonacci.Substitution.D5.S0.Tower.DBonacci.Substitution.gapLabelSubstitution_three_compatible.__information_unit.Statement =
    (∀ label : Fin 3, (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel =
      gapLetterSubstitution (tribonacciGapLetterOfLabel label.1)) := rfl
end

end Reg.D5.S0.Tower.DBonacci.Substitution
