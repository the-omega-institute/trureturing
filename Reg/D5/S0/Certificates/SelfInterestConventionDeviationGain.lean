import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import Reg.Support.IffRegistrations



namespace Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit
open _root_.D5.S0.Certificates.SelfInterestConventionDeviationGain

noncomputable def _root_.Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff.__information_unit : D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.{0, 0} (D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena) := @D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit.{0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena (∀ (convention : D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention), Iff (@Eq.{1} D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention (D5.S0.Certificates.SelfInterestConventionDeviationGain.dual convention) convention) (Or (@Eq.{1} D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention convention D5.S0.Certificates.SelfInterestConventionDeviationGain.FvF) (@Eq.{1} D5.S0.Certificates.SelfInterestConventionDeviationGain.Convention convention D5.S0.Certificates.SelfInterestConventionDeviationGain.AvA))) D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualRealization D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dual_bridge D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff) (type_of% (dualArena)) (type_of% (dualArena)) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    Convention (fun convention => dualFixedReadout convention)
    (fun convention => dualAlternativesReadout convention))) (type_of% (dual_lawSensitive)) (type_of% (dual_slotSensitive)) (Unit) (Unit) (Unit) := {
  unitName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dual_bridge,
  realizationSource := none,
  generated := false,
  arena := ⟨(dualArena)⟩,
  objectArena := ⟨(dualArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (dualArena) (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualRealization) (dualRealization.toPrimitiveBundle) ⟨(dual_bridge)⟩,
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    Convention (fun convention => dualFixedReadout convention)
    (fun convention => dualAlternativesReadout convention)),
  variation := some ⟨(dual_lawSensitive)⟩,
  sensitivity := some ⟨(dual_slotSensitive)⟩,
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
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit
open _root_.D5.S0.Certificates.SelfInterestConventionDeviationGain
example : _root_.Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff.__information_unit.Statement =
    (∀ convention : Convention, dual convention = convention ↔
      convention = FvF ∨ convention = AvA) := rfl
end

end Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
