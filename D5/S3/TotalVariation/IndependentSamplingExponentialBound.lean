/- GID: D5/S3/TotalVariation/IndependentSamplingExponentialBound
   generality: G
   mirror-B: D5/B/S3/TotalVariation/IndependentSamplingExponentialBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound a repeated failure factor by its exponential envelope. -/

import Mathlib.Analysis.Complex.Exponential

namespace D5.S3.TotalVariation.IndependentSamplingExponentialBound

/-- A repeated failure factor with probability threshold `epsilon` is bounded by the
corresponding exponential envelope. -/
theorem independent_sampling_exponential_bound
    (epsilon : ℝ) (m : ℕ) (_hε0 : 0 ≤ epsilon) (hε1 : epsilon ≤ 1) :
    (1 - epsilon) ^ m ≤ Real.exp (-(epsilon * (m : ℝ))) := by
  calc
    (1 - epsilon) ^ m ≤ Real.exp (-epsilon) ^ m :=
      pow_le_pow_left₀ (sub_nonneg.mpr hε1) (Real.one_sub_le_exp_neg epsilon) m
    _ = Real.exp (-(epsilon * (m : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The parameter domains are inhabited. -/
example : Nonempty (ℝ × ℕ) := inferInstance

/-- A half-probability threshold over two checks satisfies the hypotheses and the bound. -/
example :
    (1 - (1 / 2 : ℝ)) ^ 2 ≤ Real.exp (-((1 / 2 : ℝ) * (2 : ℝ))) := by
  exact independent_sampling_exponential_bound (1 / 2) 2 (by norm_num) (by norm_num)

end D5.S3.TotalVariation.IndependentSamplingExponentialBound
