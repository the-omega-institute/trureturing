/- GID: D5/S3/ConceptDynamics/Agency/CommitmentDepthTelescoping
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/CommitmentDepthTelescoping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Commitment depths telescope along every finite sequence of plan spaces. -/

import Mathlib.Analysis.SpecialFunctions.Log.Base

/- Library-search audit trail (2026-08-27):
   * D5 name and body-shape searches for commitment depth, finite plan trees,
     log-cardinality differences, and telescoping found no exact declaration.
   * The related `TrajectoryEntropyTelescoping` family concerns Shannon laws,
     not cardinalities of compatible future-plan spaces.
   * Exact pinned-Mathlib hit `Finset.sum_range_sub'` is applied directly to
     the base-two log-cardinality sequence. No new definition or abbreviation
     is introduced. -/

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.CommitmentDepthTelescoping

/-- Along a finite history, each commitment depth is the decrease in the
base-two log-cardinality of the compatible future-plan space. These decreases
telescope to the difference between the initial and terminal plan spaces. -/
theorem finite_plan_commitment_depth_telescopes
    {Plan : Type*} (planSpace : Nat -> Finset Plan) (n : Nat) :
    (∑ t ∈ Finset.range n,
        (Real.logb 2 (planSpace t).card -
          Real.logb 2 (planSpace (t + 1)).card)) =
      Real.logb 2 (planSpace 0).card - Real.logb 2 (planSpace n).card := by
  simpa using
    (Finset.sum_range_sub' (fun t => Real.logb 2 (planSpace t).card) n)

#print axioms finite_plan_commitment_depth_telescopes

end D5.S3.ConceptDynamics.Agency.CommitmentDepthTelescoping
