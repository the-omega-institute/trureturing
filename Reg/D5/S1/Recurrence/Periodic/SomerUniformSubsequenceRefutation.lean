import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration
import Reg.Support.CertificateWordRegistrationTemplates

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration.certificateArena, theoremName := `D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.result,
      statementIdentity := "sha256:9607a2d52421641d8fb269a93c91598c90346842c7c21a7b75b88596e8b83b79",
      registrationModuleName := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration.certificateArena, theoremName := `D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.result,
      statementIdentity := "sha256:9607a2d52421641d8fb269a93c91598c90346842c7c21a7b75b88596e8b83b79",
      registrationModuleName := `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation }]
  companionPrefix := some `Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation }

namespace Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration
attribute [local instance] _root_.D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration.instDecidableEqCertificateWord
attribute [local instance] _root_.D5.S3.ConceptDynamics.InformationEscape.SomerUniformSubsequenceCertificateRegistration.instDecidableEqStateCertificateArena in

register_information_theorem _root_.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.result in certificateArena
  readout via (@certificateWordRealization CertificateWord (fun word index => word index))
  primitives certificateRealization.toPrimitiveBundle realization certificateBridge
  variation certificateVariation sensitivity certificateSensitivity
  escape from (actualWord) escape continues (open)
end

end Reg.D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation
