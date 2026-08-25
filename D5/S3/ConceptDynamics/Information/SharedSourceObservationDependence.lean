/- GID: D5/S3/ConceptDynamics/Information/SharedSourceObservationDependence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Information/SharedSourceObservationDependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Copies of one fair Boolean source agree surely but are not independent. -/

import D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity

/- Library-search audit trail (2026-08-25):
   * The current-tree `conceptLaw` is the canonical pushforward law of a finite
     readout and is applied directly to the shared fair Boolean source below.
   * `SingleSampleLawNonimplication` contains a different PMF coupling whose
     marginals are unequal; it does not state this shared-source countermodel.
   * Repository searches for shared Boolean sources, observation independence,
     and the probability tuple `(1, 1/4, 1/2)` found no exact declaration.
   * Pinned Mathlib searches found finite PMF and independence infrastructure,
     but no theorem packaging the four clauses of this explicit countermodel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Information.SharedSourceObservationDependence

open D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
open D5.S3.Entropy.Forgetting.CapacityMonotone

/-- Copying one fair Boolean source into two observations makes their equality
certain, while the product of the two one-marginals is one quarter and differs
from the one-half joint probability. -/
theorem shared_source_observations_are_not_independent :
    conceptLaw (fun _ : Bool => (1 / 2 : Real))
        (fun source : Bool => decide (source = source)) true = 1 ∧
      conceptLaw (fun _ : Bool => (1 / 2 : Real)) id true *
          conceptLaw (fun _ : Bool => (1 / 2 : Real)) id true = 1 / 4 ∧
      conceptLaw (fun _ : Bool => (1 / 2 : Real)) id true *
          conceptLaw (fun _ : Bool => (1 / 2 : Real)) id true ≠
        conceptLaw (fun _ : Bool => (1 / 2 : Real))
          (fun source : Bool => (source, source)) (true, true) ∧
      conceptLaw (fun _ : Bool => (1 / 2 : Real))
          (fun source : Bool => (source, source)) (true, true) = 1 / 2 := by
  norm_num [conceptLaw, pushforward]

#print axioms shared_source_observations_are_not_independent

end D5.S3.ConceptDynamics.Information.SharedSourceObservationDependence
