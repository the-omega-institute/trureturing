import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Syntax
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
import Reg.Support.GuardedEqualityRegistrations



namespace Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
open GuardedEqualityRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

noncomputable def _root_.Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena (∀ (g : D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.PhysicalSourceGroup), @Eq.{1} Bool (D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.PhysicalSourceGroup.isOuter g) Bool.true → @Eq.{1} Nat (D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.PhysicalSourceGroup.dimension g) (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))) D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionRealization D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimension_bridge D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer) (type_of% (outerDimensionCodeArena)) (type_of% (outerDimensionCodeArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates.guardedEqRealization
    (Fin 6) (Fin 2) (instDecidableEqFin 2)
    (fun i => outerGuardReadout i) (fun i => outerDimensionReadout i) (fun _ => dimension40Code))) (type_of% (outerDimension_lawSensitive)) (type_of% (outerDimension_slotSensitive)) (Unit) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimension_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(outerDimensionCodeArena)⟩,
  objectArena := ⟨(outerDimensionCodeArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (outerDimensionCodeArena) (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionRealization) (outerDimensionRealization.toPrimitiveBundle) ⟨(outerDimension_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates.guardedEqRealization
    (Fin 6) (Fin 2) (instDecidableEqFin 2)
    (fun i => outerGuardReadout i) (fun i => outerDimensionReadout i) (fun _ => dimension40Code)),
  variation := some ⟨(outerDimension_lawSensitive)⟩,
  sensitivity := some ⟨(outerDimension_slotSensitive)⟩,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
open GuardedEqualityRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups
example : _root_.Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer.__information_unit.Statement =
    (∀ (g : PhysicalSourceGroup) (_h : g.isOuter = true), g.dimension = 40) := rfl
end

end Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups
