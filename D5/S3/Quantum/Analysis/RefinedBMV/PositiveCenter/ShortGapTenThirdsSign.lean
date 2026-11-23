/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapTenThirdsSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The weighted geometric correction and scalar comparison at lower coordinate ten thirds. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapSign

namespace RefinedBMV.PositiveCenter

/-- The derivative and the weighted geometric correction have a positive sum on the widened strip. -/
theorem shortGapQuotient_weighted_pos_from_ten_thirds {h u α : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 3 / 11) (hu : 10 / 3 ≤ u)
    (hα : 0 ≤ α) (hαmax : α ≤ 3 / 20) :
    0 < deriv (shortGapQuotient h) u + (α + (3 / 2 + h)) * shortGapQuotient h u := by
  let g : ℝ := 3 + h
  let m : ℝ := 3 / 2 + h
  let L := upperTailSlope h u
  let E := Real.exp (-(g * u))
  have hu₀ : 0 < u := by linarith
  have hg : 0 < g := by dsimp only [g]; positivity
  have hm : (3 / 2 : ℝ) ≤ m := by dsimp only [m]; linarith
  have hm' : m ≤ 39 / 22 := by dsimp only [m]; linarith
  have hL₀ : 0 ≤ L := (upperTailSlope_bounds hh hu₀).1.le
  have hL : L ≤ 3 / 10 := by
    have h := (upperTailSlope_bounds hh hu₀).2.1.trans
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10 / 3) hu)
    norm_num at h ⊢
    exact h
  have hE₀ : 0 ≤ E := (Real.exp_pos _).le
  have hE : E ≤ 1 / 1000 := by
    have hgu : 10 ≤ g * u := by
      dsimp only [g]
      nlinarith only [hu, mul_nonneg hh.le hu₀.le]
    have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at ht
    have he : (1000 : ℝ) ≤ Real.exp (g * u) := by
      exact (show (1000 : ℝ) ≤ Real.exp 10 by linarith only [ht]).trans
        (Real.exp_le_exp.mpr hgu)
    change Real.exp (-(g * u)) ≤ 1 / 1000
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr he
  have hgeom : upperTailSlope g u * (1 - E) = g * E := by
    rw [← upperTailGap_logDeriv hg hu₀, (hasDerivAt_upperTailGap (t := u) hg).deriv]
    have hgap : 1 - E = g * upperTailGap g u := by
      dsimp only [E, upperTailGap]
      field_simp [hg.ne']
    rw [hgap]
    have hgpos : 0 < upperTailGap g u := by
      rw [expGapMean_eq hg]
      exact mul_pos hu₀ (expGapMean_pos _ _)
    field_simp [hgpos.ne'] <;> ring
  have hrec : shortGapQuotient h u = 1 / 4 - L * (1 - E) :=
    shortGapQuotient_recenter hh hu₀
  have hder := shortGapQuotient_recentered_slope hh hu₀
    (α := α) (β := α - L) (show α - (α - L) = upperTailSlope h u by dsimp only [L]; ring)
  change -deriv (shortGapQuotient h) u + (α + m) * (L * (1 - E)) =
    (3 / 2 + (α - L) + upperTailSlope g u) * (L * (1 - E)) at hder
  rw [show (3 / 2 + (α - L) + upperTailSlope g u) * (L * (1 - E)) =
      (3 / 2 + (α - L)) * (L * (1 - E)) + L * (upperTailSlope g u * (1 - E)) by ring,
    hgeom] at hder
  have heval : deriv (shortGapQuotient h) u + (α + m) * shortGapQuotient h u =
      α * (1 / 4 - L) + (m / 4 - 3 / 2 * L + L ^ 2) - L * E * (m - α + L) := by
    rw [hrec]
    dsimp only [g, m] at hder ⊢
    linear_combination -hder
  have hfirst : -(3 / 400 : ℝ) ≤ α * (1 / 4 - L) := by
    calc
      _ ≤ α * (-(1 / 20 : ℝ)) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hL]) hα
  have hsecond : (3 / 200 : ℝ) ≤ m / 4 - 3 / 2 * L + L ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ 6 / 5 - L by linarith only [hL])
    nlinarith only [h, hm]
  have hthird : L * E * (m - α + L) ≤ 171 / 275000 := by
    have hnonneg : 0 ≤ m - α + L := by linarith only [hm, hαmax, hL₀]
    have hupper : m - α + L ≤ (39 / 22 + 3 / 10 : ℝ) := by
      linarith only [hm', hα, hL]
    have hLE : L * E ≤ (3 / 10 : ℝ) * (1 / 1000) :=
      mul_le_mul hL hE hE₀ (by norm_num)
    calc
      _ ≤ ((3 / 10 : ℝ) * (1 / 1000)) * (39 / 22 + 3 / 10) :=
        mul_le_mul hLE hupper hnonneg (by norm_num)
      _ = _ := by norm_num
  change 0 < deriv (shortGapQuotient h) u + (α + m) * shortGapQuotient h u
  rw [heval]
  linarith only [hfirst, hsecond, hthird]

end RefinedBMV.PositiveCenter
