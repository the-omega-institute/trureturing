/- GID: D5/S3/Observer/VisibleDescent/VisibleDynamicsDescentCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/VisibleDescent/VisibleDynamicsDescentCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Visible dynamics descends exactly when hidden-to-visible flow vanishes. -/

import D5.S3.Observer.VisibleDescent.LinearDescentCriterion

/- Library-search audit trail (2026-08-25):
   * Repository searches for visible descent and hidden-to-visible cross blocks
     found the frozen `LinearDescentCriterion` on the source's Hilbert carrier.
     Its public theorem contains a stronger three-way equivalence and uniqueness
     result, but no public declaration has the exact two-way statement below.
   * The canonical orthogonal projections and descended operator are imported
     from that family; no parallel carrier or projection definition is added.
   * Pinned Mathlib's `List.TFAE.out` is the exact extraction primitive for two
     entries of the existing equivalence and is applied directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.VisibleDescent.VisibleDynamicsDescentCriterion

open D5.S3.Observer.VisibleDescent.LinearDescentCriterion

/-- A bounded Hilbert-space flow admits a closed visible evolution exactly when
its hidden-to-visible cross block vanishes. -/
theorem visible_dynamics_descends_iff_cross_block_zero
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) :
    (Exists fun descended : V →L[𝕜] V =>
      V.orthogonalProjectionOnto.comp T =
        descended.comp V.orthogonalProjectionOnto) ↔
      (V.orthogonalProjectionOnto.comp T).comp Vᗮ.starProjection = 0 := by
  exact (linear_descent_criterion V T).1.out 0 1

#print axioms visible_dynamics_descends_iff_cross_block_zero

end D5.S3.Observer.VisibleDescent.VisibleDynamicsDescentCriterion
