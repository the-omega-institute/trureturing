/- GID: D5/S3/ConceptDynamics/Information/SharedSourcePerfectCorrelation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Information/SharedSourcePerfectCorrelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two identity readouts of one fair Boolean source are perfectly correlated. -/

import D5.S3.ConceptDynamics.Information.SharedSourceObservationDependence

/- Library-search audit trail (2026-08-26):
   * Current-tree searches for perfect observational correlation, Boolean conditional
     probabilities, identity channels, and the mass pair `(1, 0)` found no exact D5 theorem.
   * Exact family hit `RefinementEntropyMonotonicity.conceptLaw` is the canonical finite
     pushforward law and is applied directly to both marginal and joint readouts.
   * `SharedSourceObservationDependence.shared_source_observations_are_not_independent`
     constructs the same fair shared source but states dependence, not either conditional ratio.
   * Body-shape searches for the fair Boolean identity pushforward found `conceptLaw` uses but
     no separate conditional-probability primitive. Pinned Mathlib has general measure
     conditioning, but no exact theorem computing this finite shared-source model.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Information.SharedSourcePerfectCorrelation

open D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
open D5.S3.Entropy.Forgetting.CapacityMonotone

/-- For a fair Boolean source `U` with observational readouts `X = U` and
`Y = U`, the conditional mass of `Y = true` is one given `X = true` and zero
given `X = false`. -/
theorem fair_shared_source_perfect_observational_correlation :
    conceptLaw (fun _ : Bool => (1 / 2 : Real))
          (fun source : Bool => (source, source)) (true, true) /
        conceptLaw (fun _ : Bool => (1 / 2 : Real)) id true = 1 ∧
      conceptLaw (fun _ : Bool => (1 / 2 : Real))
          (fun source : Bool => (source, source)) (false, true) /
        conceptLaw (fun _ : Bool => (1 / 2 : Real)) id false = 0 := by
  constructor <;> norm_num [conceptLaw, pushforward]

#print axioms fair_shared_source_perfect_observational_correlation

end D5.S3.ConceptDynamics.Information.SharedSourcePerfectCorrelation
