/- GID: D5/S3/ConceptDynamics/Discussion/ForgottenDistinctionPrecludesRefinement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Discussion/ForgottenDistinctionPrecludesRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A future readout that forgets a past distinction cannot refine the past readout. -/

import D5.S3.ConceptDynamics.RefinementFactorization.RefinementShrinksIndistinguishability

/- Library-search audit trail (2026-08-31):
   * Repository body-shape searches found and reuse the canonical `Concept` and
     `Refines` primitives from the ConceptDynamics family.
   * Repository search found `refinement_shrinks_indistinguishability`, which
     proves that refinement preserves fine-readout equality; its contrapositive
     supplies the forgetting obstruction, but it does not publicly state it.
   * Pinned Mathlib and reachable Lean ecosystem searches found no declaration
     that directly states the arbitrary-concept forgetting obstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Discussion.ForgottenDistinctionPrecludesRefinement

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.RefinementFactorization.RefinementShrinksIndistinguishability

/-- If a future concept identifies two states that a past concept distinguished,
then the future concept cannot refine the past concept. -/
theorem forgotten_distinction_precludes_refinement
    {X C D : Type*} (past : Concept X C) (future : Concept X D)
    {x y : X} (oldDistinction : past x ≠ past y)
    (forgotten : future x = future y) :
    ¬ Refines past future := by
  intro refinement
  exact oldDistinction
    (refinement_shrinks_indistinguishability past future refinement forgotten)

#print axioms forgotten_distinction_precludes_refinement

end D5.S3.ConceptDynamics.Discussion.ForgottenDistinctionPrecludesRefinement
