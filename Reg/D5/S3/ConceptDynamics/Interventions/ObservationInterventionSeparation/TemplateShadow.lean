import Reg.Support.LegacyCausalMapping
import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.TemplateShadow

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
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

register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention in _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionLawArena
  object_arena _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena catalog D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena
  readout via (@_root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates.observationFiniteRealization _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM
    (fun M => _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.oiObsCode M) (fun M => _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.oiIntCode M))
  primitives _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationRealization.toPrimitiveBundle realization _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_bridge
  variation _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_law_sensitive
  sensitivity _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservation_slot_sensitive
  escape from (_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM) escape continues (open)
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
example : _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention.«Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena».__information_unit.Statement =
    (D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention.observation_strictly_weaker_than_intervention_realization.toTheoremUnit
      observation_strictly_weaker_than_intervention).Statement := rfl
end

end Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.TemplateShadow
