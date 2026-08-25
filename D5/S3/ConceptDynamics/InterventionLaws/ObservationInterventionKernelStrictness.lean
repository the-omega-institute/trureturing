/- GID: D5/S3/ConceptDynamics/InterventionLaws/ObservationInterventionKernelStrictness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionLaws/ObservationInterventionKernelStrictness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The full intervention profile has a strictly finer kernel than observation. -/

import D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-26):
   * The frozen `ObservationInterventionSeparation` family supplies the exact
     finite Boolean structural-model carrier, observation and intervention
     channels, source models, and strict witness; all are imported directly.
   * Repository body-shape searches found no profile combining `Obs` as the
     null action with `Int` at each imposed Boolean value. It is constructed in
     the public statement, with no new `def` or `abbrev`.
   * Pinned Mathlib's `Set.ssubset_iff_exists` supplies the exact strict-subset
     characterization. No library theorem states the source-specific result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness

open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation

/-- Adding the null action to the two perfect interventions makes the complete
intervention profile refine observation. The two opposite-direction Boolean
models show that the refinement is already strict on this finite carrier. -/
theorem intervention_kernel_strictly_finer_than_observation :
    let fullInterventionProfile :
        DeterministicBoolSCM -> Option Bool -> Bool -> Bool × Bool :=
      fun model action =>
        match action with
        | none => Obs model
        | some imposedX => Int model imposedX
    { pair : DeterministicBoolSCM × DeterministicBoolSCM |
        Setoid.ker fullInterventionProfile pair.1 pair.2 } ⊂
      { pair : DeterministicBoolSCM × DeterministicBoolSCM |
        Setoid.ker Obs pair.1 pair.2 } := by
  dsimp only
  apply Set.ssubset_iff_exists.mpr
  constructor
  · intro pair profilesEqual
    exact congrFun profilesEqual none
  · rcases observation_strictly_weaker_than_intervention with
      ⟨firstModel, secondModel, observationsEqual, interventionsDiffer⟩
    refine ⟨(firstModel, secondModel), observationsEqual, ?_⟩
    intro profilesEqual
    apply interventionsDiffer
    funext imposedX
    exact congrFun profilesEqual (some imposedX)

#print axioms intervention_kernel_strictly_finer_than_observation

end D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
