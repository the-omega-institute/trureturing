import Reg.Support.LegacyResidue
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow
  expected := #[
    { objectArenaName := `Reg.Support.LegacyResidue.arena, theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification,
      statementIdentity := "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow }]
  source := #[
    { objectArenaName := `Reg.Support.LegacyResidue.arena, theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification,
      statementIdentity := "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow }


namespace Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.Reg.Support.LegacyFiniteTransport
open _root_.Reg.Support.LegacyResidue

register_information_theorem _root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification in arena
  readout via (RegistrationTemplates.binaryFamilyRealization (fun i s => readouts i s))
  primitives actual.toPrimitiveBundle
  realization bridge
  variation variation
  sensitivity sensitivity
  escape from (_root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.ResidueState) escape continues (open)

end Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow
