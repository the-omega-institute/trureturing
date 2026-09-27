import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention.observationInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow }

namespace Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow

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
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open InformationEscapeArenas.ObservationIntervention

register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention in observationInterventionArena
  primitives observationRealization.toPrimitiveBundle realization observation_bridge
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
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open InformationEscapeArenas.ObservationIntervention
example : _root_.Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention.__information_unit.Statement =
    (D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention.observation_strictly_weaker_than_intervention_realization.toTheoremUnit
      observation_strictly_weaker_than_intervention).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow
