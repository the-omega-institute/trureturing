import Reg.Support.LegacyCausalFinite
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration
  expected := #[
    { objectArenaName := `Reg.Support.LegacyCausalCoordinates.objectArena, theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration }]
  source := #[
    { objectArenaName := `Reg.Support.LegacyCausalCoordinates.objectArena, theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration }

namespace Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration
open _root_.Reg.Support.LegacyCausalFinite
open _root_.Reg.Support.LegacyCausalSlots (slotRealization)

register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention
  in _root_.Reg.Support.LegacyCausalSlots.oiDomainArena
  object_arena Reg.Support.LegacyCausalCoordinates.objectArena catalog «causal-unified-transitions»
  readout via (slotRealization (fun i x => oiRead i x))
  primitives oiActual.toPrimitiveBundle realization oi_bridge
  variation oi_variation sensitivity _root_.Reg.Support.LegacyCausalSlots.oi_sensitivity
  escape from (_root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM)
  escape continues (open)

end Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.UnifiedCausalRegistration
