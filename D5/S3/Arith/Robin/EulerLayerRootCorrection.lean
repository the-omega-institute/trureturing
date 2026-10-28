/- GID: D5/S3/Arith/Robin/EulerLayerRootCorrection
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/EulerLayerRootCorrection
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Exact target statement for the strict Euler inventory root-scale correction; proof open. -/

import D5.S3.Arith.Robin.EulerLayerInventoryGrowth

namespace D5.S3.Arith.Robin.EulerLayerRootCorrection

open scoped Chebyshev

/-!
The paper/theory target is retained verbatim as a proposition. No theorem is
claimed here: the missing proof must establish the uniform second-layer cutoff
at `sqrt 2 * sqrt t`, the vanishing of all actual layers at least three, and
the root-scale Costa--Pereira limit for `psi - theta`.
-/
def strict_inventory_root_correction_statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t → ∀ U : ℕ, 0 < U →
    (∀ q : ℕ, q.Prime →
      U.factorization q =
        D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount.optimalLayerCount
          (1 / (t * Real.log t)) q) →
    |(Real.log U - Chebyshev.psi t) / Real.sqrt t - (Real.sqrt 2 - 1)| < ε

end D5.S3.Arith.Robin.EulerLayerRootCorrection
