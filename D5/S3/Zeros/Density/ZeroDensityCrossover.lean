/- GID: D5/S3/Zeros/Density/ZeroDensityCrossover
   generality: G
   mirror-B: D5/B/S3/Zeros/Density/ZeroDensityCrossover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Guth-Maynard density exponent wins exactly between its two crossover points. -/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

namespace D5.S3.Zeros.Density.ZeroDensityCrossover

/-- On the zero-density range `0 <= epsilon < 1/2`, the Guth-Maynard exponent
`30(1/2-epsilon)/13` is no larger than both the Ingham and Huxley exponents exactly between
the crossover points `epsilon = 1/5` and `epsilon = 4/15`. -/
theorem guth_maynard_dominates_iff {epsilon : ℝ} (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_half : epsilon < 1 / 2) :
    (30 * (1 / 2 - epsilon) / 13 ≤ 3 * (1 / 2 - epsilon) / (3 / 2 - epsilon) ∧
        30 * (1 / 2 - epsilon) / 13 ≤ 3 * (1 / 2 - epsilon) / (1 / 2 + 3 * epsilon)) ↔
      1 / 5 ≤ epsilon ∧ epsilon ≤ 4 / 15 := by
  have hnumerator : 0 < 1 / 2 - epsilon := by linarith
  have hingham_denominator : 0 < 3 / 2 - epsilon := by linarith
  have hhuxley_denominator : 0 < 1 / 2 + 3 * epsilon := by linarith
  have hingham :
      30 * (1 / 2 - epsilon) / 13 ≤ 3 * (1 / 2 - epsilon) / (3 / 2 - epsilon) ↔
        1 / 5 ≤ epsilon := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 13) hingham_denominator]
    constructor <;> intro h <;> nlinarith
  have hhuxley :
      30 * (1 / 2 - epsilon) / 13 ≤ 3 * (1 / 2 - epsilon) / (1 / 2 + 3 * epsilon) ↔
        epsilon ≤ 4 / 15 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 13) hhuxley_denominator]
    constructor <;> intro h <;> nlinarith
  exact and_congr hingham hhuxley

end D5.S3.Zeros.Density.ZeroDensityCrossover
