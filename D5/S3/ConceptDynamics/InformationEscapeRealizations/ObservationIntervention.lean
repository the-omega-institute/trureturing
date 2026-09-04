/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frozen observation-intervention theorem realizes a two-CUT law with 24 classes. -/

import D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention

/- Library-search audit trail (2026-09-04): the source `Obs` and `Int` readouts,
   named witness models, and typed bundle agreement theorem are exact hits and reused.
   No deposited legacy realization or partition-count theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention

/-- The concrete observation and intervention response functions. -/
def observationInterventionRealization :
    PrimitiveRealization observationInterventionSignature where
  readout
    | .observation => Obs
    | .intervention => Int
  anchor := fun i => Fin.elim0 i

/-- The legacy separation theorem is equivalent to its object-bound law. -/
theorem observation_strictly_weaker_than_intervention_realization :
    LegacyPrimitiveRealization observationInterventionArena
      ObservationInterventionStatement observationInterventionRealization := by
  exact ⟨Iff.rfl⟩

/-- The combined observation/intervention signature has 24 kernel classes. -/
theorem observation_strictly_weaker_than_intervention_partition_count :
    (Finset.univ.image (fun model : DeterministicBoolSCM =>
      (Obs model, Int model))).card = 24 := by
  decide

/-- The named opposite-direction models form the private census pair. -/
theorem observation_strictly_weaker_than_intervention_private_pair :
    ¬ observationInterventionRealization.toPrimitiveBundle.agrees
      xCausesYModel yCausesXModel := by
  intro h
  have hreadouts :=
    (PrimitiveRealization.toPrimitiveBundle_agrees_iff
      observationInterventionRealization xCausesYModel yCausesXModel).1 h |>.1
  have hintervention := hreadouts ObservationReadout.intervention
  have hwitness := congrFun (congrFun hintervention false) true
  have hfalse : false = true := by
    simpa [observationInterventionRealization,
      D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Int,
      xCausesYModel, yCausesXModel] using congrArg Prod.snd hwitness
  exact Bool.false_ne_true hfalse

example : observationInterventionArena.toArena.Nondegenerate := by decide

end D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
