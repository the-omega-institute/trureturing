/- GID: D5/S3/Quantum/Semigroups/WuEndpointFiniteArithmetic
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuEndpointFiniteArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative centered Bernoulli moment gap. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A polynomial moment inequality for the finite proof of the Wu endpoint. -/

namespace WuEndpointFiniteArithmetic

private theorem bernoulli_moment_polynomial_gap {s v : ℝ} (hv : 0 ≤ v) (hvs : v ≤ s) :
    (14 / 3) * s ^ 4 * v ^ 2 ≤
      s ^ 2 * (s + 3 * v) ^ 4 - (s ^ 2 + 4 * s * v + (4 / 9) * v ^ 2) ^ 3 := by
  have hs : 0 ≤ s := hv.trans hvs
  have hdiff : 0 ≤ s - v := sub_nonneg.mpr hvs
  have hsq : 0 ≤ s ^ 2 - v ^ 2 := by
    calc
      0 ≤ (s - v) * (s + v) := mul_nonneg hdiff (add_nonneg hs hv)
      _ = s ^ 2 - v ^ 2 := by ring
  calc
    _ ≤
        (14 / 3) * s ^ 4 * v ^ 2 + (100 / 3) * s ^ 3 * v ^ 3 +
        (41273 / 729) * s ^ 2 * v ^ 4 + (64 / 27) * s * v ^ 4 * (s - v) +
        (64 / 729) * v ^ 4 * (s ^ 2 - v ^ 2) := by
      have h₂ : 0 ≤ (100 / 3 : ℝ) * s ^ 3 * v ^ 3 :=
        mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs _)) (pow_nonneg hv _)
      have h₃ : 0 ≤ (41273 / 729 : ℝ) * s ^ 2 * v ^ 4 :=
        mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs _)) (pow_nonneg hv _)
      have h₄ : 0 ≤ (64 / 27 : ℝ) * s * v ^ 4 * (s - v) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (pow_nonneg hv _)) hdiff
      have h₅ : 0 ≤ (64 / 729 : ℝ) * v ^ 4 * (s ^ 2 - v ^ 2) :=
        mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hv _)) hsq
      exact le_trans (le_add_of_nonneg_right h₂)
        (le_trans (le_add_of_nonneg_right h₃)
          (le_trans (le_add_of_nonneg_right h₄) (le_add_of_nonneg_right h₅)))
    _ = _ := by ring

/-- Quantitative gap between the powered input and output moments in centered coordinates. -/
theorem centered_bernoulli_moment_gap {a b : ℝ} (hleft : -a ≤ b) (hright : b ≤ a) :
    (14 / 3) * (a ^ 2) ^ 4 * (b ^ 2) ^ 2 ≤
      (a ^ 3 + 3 * a * b ^ 2) ^ 4 -
        (a ^ 4 + 4 * a ^ 2 * b ^ 2 + (4 / 9) * b ^ 4) ^ 3 := by
  have hb : b ^ 2 ≤ a ^ 2 := by
    apply sub_nonneg.mp
    calc
      0 ≤ (a - b) * (a + b) :=
        mul_nonneg (sub_nonneg.mpr hright) (by linarith only [hleft])
      _ = a ^ 2 - b ^ 2 := by ring
  calc
    _ ≤ (a ^ 2) ^ 2 * (a ^ 2 + 3 * b ^ 2) ^ 4 -
        ((a ^ 2) ^ 2 + 4 * a ^ 2 * b ^ 2 + (4 / 9) * (b ^ 2) ^ 2) ^ 3 :=
      bernoulli_moment_polynomial_gap (sq_nonneg b) hb
    _ = _ := by ring

#print axioms centered_bernoulli_moment_gap

end WuEndpointFiniteArithmetic
