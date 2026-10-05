import LeanInformationAuditInterface.Contract.Registration
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



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates.guardedEqRealization
    (Fin 6) (Fin 2) (instDecidableEqFin 2)
    (fun i => outerGuardReadout i) (fun i => outerDimensionReadout i) (fun _ => dimension40Code))) (Unit) (Unit) := {
  unitName := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimension_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(outerDimensionCodeArena)⟩,
  objectArena := .law ⟨(outerDimensionCodeArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (outerDimensionCodeArena) (D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionRealization) (outerDimensionRealization.toPrimitiveBundle) ⟨(outerDimension_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (outerDimension_bridge) (@_root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((outerDimensionRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates.guardedEqRealization
    (Fin 6) (Fin 2) (instDecidableEqFin 2)
    (fun i => outerGuardReadout i) (fun i => outerDimensionReadout i) (fun _ => dimension40Code)),
  variation := .evidence ⟨(outerDimension_lawSensitive)⟩ (by first | exact (outerDimension_lawSensitive) | exact ⟨_, _, (outerDimension_lawSensitive)⟩),
  sensitivity := .evidence ⟨(outerDimension_slotSensitive)⟩ (by exact (outerDimension_slotSensitive)),
  partialSensitivity := none,
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
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimension_bridge.toTheoremUnit _root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer).Statement =
    (∀ (g : PhysicalSourceGroup) (_h : g.isOuter = true), g.dimension = 40) := rfl
end

end Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups
