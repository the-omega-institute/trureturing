import Reg.Support.LegacyStaticDesign
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow
  expected := #[
    { objectArenaName := `Reg.Support.LegacyStaticDesign.arena, theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design,
      statementIdentity := "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow }]
  source := #[
    { objectArenaName := `Reg.Support.LegacyStaticDesign.arena, theoremName := `D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design,
      statementIdentity := "sha256:408742a2c71557575944155350def43ed8f9f37ec3a19fe75f721e084dfe939a",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow }


namespace Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.Reg.Support.LegacyFiniteTransport
open _root_.Reg.Support.LegacyStaticDesign

register_information_theorem _root_.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.static_exact_design in arena
  readout via (RegistrationTemplates.binaryFamilyRealization (fun i s => readouts i s))
  primitives actual.toPrimitiveBundle
  realization bridge
  variation variation
  sensitivity sensitivity
  escape from (Fin 3) escape continues (open)

end Reg.D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign.TemplateShadow
