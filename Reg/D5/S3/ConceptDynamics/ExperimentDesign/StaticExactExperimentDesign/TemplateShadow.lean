import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena, theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design,
      statementIdentity := "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign.staticExactExperimentArena, theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design,
      statementIdentity := "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow }

namespace Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow

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
open _root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
open InformationEscapeArenas.StaticExactExperimentDesign

register_information_theorem _root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design in staticExactExperimentArena
  primitives staticRealization.toPrimitiveBundle realization static_bridge
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
open _root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
open InformationEscapeArenas.StaticExactExperimentDesign
example : _root_.Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design.__information_unit.Statement =
    (InformationEscapeRealizations.StaticExactExperimentDesign.static_exact_design_realization.toTheoremUnit
      static_exact_design).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow
