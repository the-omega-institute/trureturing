import Reg.Support.SharedArenaPeers

namespace Reg.Support.LegacyCausalMapping
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

section Intervention
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
attribute [local instance] FourthFifthArenas.modelFintype FourthFifthArenas.modelDecidableEq

/-- The replacement preserves the original catalog's state space and every
observational equivalence class, not just the existential theorem. -/
theorem intervention_kernel (x y : DeterministicBoolSCM) :
    finiteInterventionRealization.toPrimitiveBundle.agrees x y ↔
      FourthFifthRealizations.interventionRealization.toPrimitiveBundle.agrees x y := by
  revert x y
  decide +kernel

theorem intervention_dependence : ∀ i : Bool, ∃ x y : DeterministicBoolSCM,
    finiteInterventionRealization.readout i x ≠ finiteInterventionRealization.readout i y := by
  intro i
  cases i
  · change ∃ x y : DeterministicBoolSCM, icIntCode x ≠ icIntCode y
    decide +kernel
  · change ∃ x y : DeterministicBoolSCM, icCFCode x ≠ icCFCode y
    decide +kernel

theorem intervention_statement :
    (FourthFifthRealizations.intervention_strictly_weaker_than_counterfactual_realization.toTheoremUnit
      intervention_strictly_weaker_than_counterfactual).Statement =
    (finiteIntervention_bridge.toTheoremUnit intervention_strictly_weaker_than_counterfactual).Statement := rfl
end Intervention

section Observation
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation

theorem observation_kernel (x y : DeterministicBoolSCM) :
    finiteObservationRealization.toPrimitiveBundle.agrees x y ↔
      ObservationIntervention.observationInterventionRealization.toPrimitiveBundle.agrees x y := by
  revert x y
  decide +kernel

theorem observation_dependence : ∀ i : Bool, ∃ x y : DeterministicBoolSCM,
    finiteObservationRealization.readout i x ≠ finiteObservationRealization.readout i y := by
  intro i
  cases i
  · change ∃ x y : DeterministicBoolSCM, oiObsCode x ≠ oiObsCode y
    decide +kernel
  · change ∃ x y : DeterministicBoolSCM, oiIntCode x ≠ oiIntCode y
    decide +kernel

theorem observation_statement :
    (ObservationIntervention.observation_strictly_weaker_than_intervention_realization.toTheoremUnit
      observation_strictly_weaker_than_intervention).Statement =
    (finiteObservation_bridge.toTheoremUnit observation_strictly_weaker_than_intervention).Statement := rfl
end Observation

#print axioms intervention_kernel
#print axioms intervention_dependence
#print axioms observation_kernel
#print axioms observation_dependence
end Reg.Support.LegacyCausalMapping
