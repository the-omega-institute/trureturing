import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena, theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment.unifiedArena, theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration }

namespace Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
local instance : DecidableEq IC.Model :=
  _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.modelDecidableEq

register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention
  in observationInterventionLawArena
  object_arena unifiedArena
  catalog «causal-unified-transitions»
  primitives observationInterventionUnifiedRealization.toPrimitiveBundle
  realization observation_intervention_unified_realization
end

end Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration
