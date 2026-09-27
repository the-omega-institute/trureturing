import Reg.Support.LegacyCausalFinite
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration
  expected := #[
    { objectArenaName := `Reg.Support.LegacyCausalCoordinates.objectArena, theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
      statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration }]
  source := #[
    { objectArenaName := `Reg.Support.LegacyCausalCoordinates.objectArena, theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
      statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration }]
  companionPrefix := some `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration }

namespace Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration
open _root_.Reg.Support.LegacyCausalFinite
open _root_.Reg.Support.LegacyCausalSlots (slotRealization)

register_information_theorem _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
  in _root_.Reg.Support.LegacyCausalSlots.icDomainArena
  object_arena Reg.Support.LegacyCausalCoordinates.objectArena catalog «causal-unified-transitions»
  readout via (slotRealization (fun i x => icRead i x))
  primitives icActual.toPrimitiveBundle realization ic_bridge
  variation ic_variation sensitivity _root_.Reg.Support.LegacyCausalSlots.ic_sensitivity
  escape from (_root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM)
  escape continues (open)

end Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.UnifiedCausalRegistration
