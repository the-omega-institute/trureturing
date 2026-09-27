import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena, theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification,
      statementIdentity := "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas.residueArena, theoremName := `D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification,
      statementIdentity := "sha256:6f8434c94b05962f830bd9c47522da114d168db8b17fa7825970bf48a600b9e6",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow }

namespace Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open FirstThreeArenas

register_information_theorem _root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification in residueArena
  primitives residueRealization.toPrimitiveBundle realization residue_bridge
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open _root_.D5.S3.ConceptDynamics.InformationEscape.TemplateShadow
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open FirstThreeArenas
example : _root_.Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.two_step_adaptive_residue_identification.__information_unit.Statement =
    (FirstThreeRealizations.two_step_adaptive_residue_identification_realization.toTheoremUnit
      two_step_adaptive_residue_identification).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification.TemplateShadow
