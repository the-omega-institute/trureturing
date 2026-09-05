/- GID: D5/S3/Weil/ZetaGamma/ArchimedeanObserverProductPositive
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaGamma/ArchimedeanObserverProductPositive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove strict positivity of the Archimedean observer product at every nonzero mode. -/

import D5.S3.Weil.ZetaGamma.MasslessTangentConeLimit

/-!
# Archimedean observer-product positivity

Every term in the logarithmic Archimedean tower is nonnegative. For a nonzero regulator mode,
the zeroth term is strictly positive, so summability upgrades this pointwise witness to strict
positivity of the whole tower.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaGamma.ArchimedeanObserverProductPositive

open D5.S3.Weil.ZetaGamma.MasslessTangentConeLimit

private theorem summable_observer_log_tower {sigma tau : ℝ} (hsigma : 0 < sigma) :
    Summable (fun m : ℕ => Real.log (1 + tau ^ 2 / (sigma + 2 * m) ^ 2)) := by
  have hmajorant : Summable (fun m : ℕ => tau ^ 2 / (sigma + 2 * m) ^ 2) := by
    rw [← summable_nat_add_iff 1]
    have hp : Summable (fun n : ℕ => tau ^ 2 * (1 / ((n : ℝ) + 1) ^ 2)) := by
      have hp0 : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
        Real.summable_nat_pow_inv.mpr (by norm_num)
      have hp1 : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) :=
        (summable_nat_add_iff 1).mpr hp0
      refine (hp1.mul_left (tau ^ 2)).congr ?_
      intro n
      push_cast
      simp only [one_div]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hp
    have hden : (n : ℝ) + 1 ≤ sigma + 2 * ((n + 1 : ℕ) : ℝ) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg tau)
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hden 2)
  refine Summable.of_nonneg_of_le (fun m => Real.log_nonneg ?_) (fun m => ?_) hmajorant
  · have hterm : 0 ≤ tau ^ 2 / (sigma + 2 * m) ^ 2 := by positivity
    linarith
  · have hpositive : 0 < 1 + tau ^ 2 / (sigma + 2 * m) ^ 2 := by positivity
    simpa using Real.log_le_sub_one_of_pos hpositive

/-- For every positive Archimedean offset and nonzero regulator mode, the logarithmic observer
product is strictly positive. The hypotheses exclude Lean's totalized division and the zero-mode
case, where the tower is identically zero. -/
theorem archimedean_observer_product_positive (sigma tau : ℝ) (hsigma : 0 < sigma)
    (htau : tau ≠ 0) :
    0 < archimedean_dispersion sigma (tau ^ 2) := by
  rw [archimedean_dispersion]
  refine (summable_observer_log_tower (tau := tau) hsigma).tsum_pos (fun m => ?_) 0 ?_
  · apply Real.log_nonneg
    have hterm : 0 ≤ tau ^ 2 / (sigma + 2 * m) ^ 2 := by positivity
    linarith
  · have hfrac : 0 < tau ^ 2 / sigma ^ 2 := by positivity
    simpa using Real.log_pos (show 1 < 1 + tau ^ 2 / sigma ^ 2 by linarith)

#print axioms archimedean_observer_product_positive

end D5.S3.Weil.ZetaGamma.ArchimedeanObserverProductPositive
