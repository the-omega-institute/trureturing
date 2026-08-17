/- GID: D5/S3/Arith/Congruence/MarkovNeighborNormObstruction
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/MarkovNeighborNormObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Neighboring Markov factors cannot form an x^2 + 3y^2 norm. -/

import D5.S3.Arith.Congruence.ModThreeNormObstruction

namespace D5.S3.Arith.Congruence.MarkovNeighborNormObstruction

/-- The product of the neighboring factors `3 * mu - 1` and `3 * mu + 1` is not
representable by the quadratic norm `x ^ 2 + 3 * y ^ 2` over the integers. -/
theorem markov_neighbor_product_not_quadratic_norm (mu x y : ℤ) :
    x ^ 2 + 3 * y ^ 2 ≠ (3 * mu - 1) * (3 * mu + 1) := by
  have hfactor : (3 * mu - 1) * (3 * mu + 1) = 3 * (3 * mu ^ 2) - 1 := by
    ring
  rw [hfactor]
  exact
    ModThreeNormObstruction.three_mul_sub_one_not_quadratic_norm
      (3 * mu ^ 2) x y

#print axioms markov_neighbor_product_not_quadratic_norm

end D5.S3.Arith.Congruence.MarkovNeighborNormObstruction
