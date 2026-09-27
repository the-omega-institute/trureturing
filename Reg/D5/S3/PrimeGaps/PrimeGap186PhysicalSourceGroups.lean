import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
import Reg.Support.GuardedEqualityRegistrations

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena, theoremName := `D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer,
      statementIdentity := "sha256:a2696beef1ce0e3cb782708559f90acd25415caf6cf673804746e92d6fbcc2a1",
      registrationModuleName := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations.outerDimensionCodeArena, theoremName := `D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer,
      statementIdentity := "sha256:a2696beef1ce0e3cb782708559f90acd25415caf6cf673804746e92d6fbcc2a1",
      registrationModuleName := `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups }]
  companionPrefix := some `Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups }

namespace Reg.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrations
open GuardedEqualityRegistrationTemplates LeanInformationAudit
open _root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups

register_information_theorem _root_.D5.S3.PrimeGaps.PrimeGap186PhysicalSourceGroups.dimension_eq_40_of_outer in outerDimensionCodeArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.GuardedEqualityRegistrationTemplates.guardedEqRealization
    (Fin 6) (Fin 2) (instDecidableEqFin 2)
    (fun i => outerGuardReadout i) (fun i => outerDimensionReadout i) (fun _ => dimension40Code))
  primitives outerDimensionRealization.toPrimitiveBundle realization outerDimension_bridge
  variation outerDimension_lawSensitive sensitivity outerDimension_slotSensitive
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
