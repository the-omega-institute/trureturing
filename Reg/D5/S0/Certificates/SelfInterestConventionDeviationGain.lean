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



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff) (type_of% (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    Convention (fun convention => dualFixedReadout convention)
    (fun convention => dualAlternativesReadout convention))) (Unit) (Unit) := {
  unitName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff.__information_unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dual_bridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨(dualArena)⟩,
  objectArena := .law ⟨(dualArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (dualArena) (D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualRealization) (dualRealization.toPrimitiveBundle) ⟨(dual_bridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (dual_bridge) (@_root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((dualRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    Convention (fun convention => dualFixedReadout convention)
    (fun convention => dualAlternativesReadout convention)),
  variation := .evidence ⟨(dual_lawSensitive)⟩ (by first | exact (dual_lawSensitive) | exact ⟨_, _, (dual_lawSensitive)⟩),
  sensitivity := .evidence ⟨(dual_slotSensitive)⟩ (by exact (dual_slotSensitive)),
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
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit
open _root_.D5.S0.Certificates.SelfInterestConventionDeviationGain
example : (_root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dual_bridge.toTheoremUnit _root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff).Statement =
    (∀ convention : Convention, dual convention = convention ↔
      convention = FvF ∨ convention = AvA) := rfl
end

end Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
