/- GID: D5/S3/ConceptDynamics/ExperimentDesign/PositiveFirstExperimentIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentDesign/PositiveFirstExperimentIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive first experiment identifies the forward causal model. -/

import D5.S3.ConceptDynamics.ExperimentDesign.AdaptiveEarlyStopping

/- Library-search audit trail (2026-08-28):
   * Current-tree name and body-shape searches found the canonical `E_X` and
     `M_XY` objects in `AdaptiveEarlyStopping`, but no public theorem exposing
     the positive-output identification clause.
   * Pinned Mathlib has the Boolean decision simplification used below, but no
     theorem about this source-specific three-model experiment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification

open AdaptiveEarlyStopping

/-- A positive result from the first experiment uniquely identifies the model
in which changing `X` changes the law of `Y`. -/
theorem positive_first_experiment_identifies_model
    (model : Fin 3) (hpositive : E_X model = true) :
    model = M_XY := by
  simpa [E_X] using hpositive

#print axioms positive_first_experiment_identifies_model

end D5.S3.ConceptDynamics.ExperimentDesign.PositiveFirstExperimentIdentification
