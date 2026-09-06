/- GID: D5/S3/TotalVariation/BhattacharyyaVariationMargin
   generality: G
   mirror-B: D5/B/S3/TotalVariation/BhattacharyyaVariationMargin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A certified total-variation lower margin gives an explicit Bhattacharyya affinity upper bound. -/

import D5.S3.TotalVariation.Bhattacharyya

/-!
# From a variation margin to an affinity ceiling

The frozen Bhattacharyya owner proves
`TV(p,q)^2 <= 1 - BC(p,q)^2`. This adapter exposes the direction needed by
robust testing: any nonnegative certified margin `delta <= TV(p,q)` implies
`BC(p,q) <= sqrt(1-delta^2)`. No new statistical inequality is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.BhattacharyyaVariationMargin

open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.Metric
open D5.S3.TotalVariation.Pinsker

/-- A nonnegative lower bound on total variation yields a complementary-square
upper bound on Bhattacharyya affinity. -/
theorem bhattacharyya_le_sqrt_one_sub_margin_sq
    {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1)
    (margin : ℝ) (hmargin : 0 ≤ margin)
    (hmarginTV : margin ≤ totalVariation p q) :
    bhattacharyya p q ≤ Real.sqrt (1 - margin ^ 2) := by
  have htvNonnegative : 0 ≤ totalVariation p q := total_variation_nonneg p q
  have hbcNonnegative : 0 ≤ bhattacharyya p q := by
    rw [bhattacharyya]
    exact Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have htvSquare := total_variation_sq_le_one_sub_bhattacharyya_sq p q hp hq
  have hmarginSquare : margin ^ 2 ≤ totalVariation p q ^ 2 :=
    (sq_le_sq₀ hmargin htvNonnegative).2 hmarginTV
  have hbcSquare : bhattacharyya p q ^ 2 ≤ 1 - margin ^ 2 := by
    nlinarith
  have hradicand : 0 ≤ 1 - margin ^ 2 := by
    nlinarith [sq_nonneg (bhattacharyya p q)]
  exact (Real.le_sqrt hbcNonnegative hradicand).2 hbcSquare

#print axioms bhattacharyya_le_sqrt_one_sub_margin_sq

end D5.S3.TotalVariation.BhattacharyyaVariationMargin
