/- GID: D5/S3/ConceptDynamics/RefinementFactorization/RefinementShrinksIndistinguishability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/RefinementShrinksIndistinguishability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor-map refinement transports fine-readout equality to the coarse readout. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-26):
   * Exact D5 hits `Concept` and `Refines` are the canonical source-family
     primitives and are imported rather than redeclared.
   * `effective_refines_iff_reverse_kernel` is adjacent but assumes surjective
     effective presentations; its forward half is therefore narrower than the
     source theorem over arbitrary concepts and is not an exact bind target.
   * Body-shape and theorem-name searches found no arbitrary-readout theorem
     transporting equality through `Refines`.
   * Pinned Mathlib supplies core `congrArg` and `congrFun`, which directly
     implement the source proof; no more specific upstream theorem was found.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementFactorization.RefinementShrinksIndistinguishability

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- If the coarse concept factors through the fine concept, states with equal
fine readouts also have equal coarse readouts. -/
theorem refinement_shrinks_indistinguishability
    {X C D : Type*} (q_C : Concept X C) (q_D : Concept X D)
    (refinement : Refines q_C q_D) {x y : X}
    (sameFineReadout : q_D x = q_D y) :
    q_C x = q_C y := by
  rcases refinement with ⟨factor, factorization⟩
  calc
    q_C x = factor (q_D x) := congrFun factorization x
    _ = factor (q_D y) := congrArg factor sameFineReadout
    _ = q_C y := (congrFun factorization y).symm

#print axioms refinement_shrinks_indistinguishability

end D5.S3.ConceptDynamics.RefinementFactorization.RefinementShrinksIndistinguishability
