/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementRegionConvexity
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves that the golden displacement convergence region is convex. -/

import D5.S3.Analytic.Displacement.GoldenDisplacementTwoConstraintRegion

open GoldenDisplacementEulerProduct
open GoldenDisplacementTwoConstraintRegion

namespace GoldenDisplacementRegionConvexity

noncomputable section

/-- The parameters where the golden displacement series converges form a convex region. -/
theorem golden_displacement_convergence_region_convex :
    Convex ℝ {p : ℝ × ℝ | Summable (dTerm p.1 p.2)} := by
  rintro ⟨s1, w1⟩ hp ⟨s2, w2⟩ hq a b ha hb hab
  change Summable (dTerm s1 w1) at hp
  change Summable (dTerm s2 w2) at hq
  change Summable (dTerm (a * s1 + b * s2) (a * w1 + b * w2))
  rw [dTerm_summable_iff_two_constraints] at hp hq ⊢
  have weighted_average_lt {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
      1 < a * x + b * y := by
    by_cases haZero : a = 0
    · subst a
      have hbOne : b = 1 := by linarith
      subst b
      simpa using hy
    · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm haZero)
      calc
        1 = a * 1 + b * 1 := by linarith
        _ < a * x + b * y :=
          add_lt_add_of_lt_of_le
            (mul_lt_mul_of_pos_left hx haPos)
            (mul_le_mul_of_nonneg_left hy.le hb)
  constructor
  · nlinarith [weighted_average_lt hp.1 hq.1]
  · nlinarith [weighted_average_lt hp.2 hq.2]

end

end GoldenDisplacementRegionConvexity
