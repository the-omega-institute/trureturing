import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import Reg.Support.IffRegistrations

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff,
      statementIdentity := "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f",
      registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.dualArena, theoremName := `D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff,
      statementIdentity := "sha256:76175c4656a4be731bad802d770e51ed7e427531bf5c0a2577c86dd338299e1f",
      registrationModuleName := `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }]
  companionPrefix := some `Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain }

namespace Reg.D5.S0.Certificates.SelfInterestConventionDeviationGain

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
open _root_.D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
open IffRegistrationTemplates PointwiseRegistrationTemplates RegistrationTemplates LeanInformationAudit
open _root_.D5.S0.Certificates.SelfInterestConventionDeviationGain

register_information_theorem _root_.D5.S0.Certificates.SelfInterestConventionDeviationGain.dual_fixed_iff in dualArena
  readout via (@D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates.iffRealization
    Convention (fun convention => dualFixedReadout convention)
    (fun convention => dualAlternativesReadout convention))
  primitives dualRealization.toPrimitiveBundle realization dual_bridge
  variation dual_lawSensitive sensitivity dual_slotSensitive
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
