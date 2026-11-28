/- GID: D5/S3/Quantum/AURICOmega/ThreeReadingContrast
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/ThreeReadingContrast
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: []
   utility: none
   digest: Classify all contrasts against a third point for a normalized rational Gram form. -/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace D5.S3.Quantum.AURICOmega.ThreeReadingContrast

/-- At fixed mutual reading `r`, the signed differences of nonnegative readings
against a third point fill exactly the rational slice of the closed unit disk.
Positivity is tested on all rational weights for the three sampled points. -/
theorem exists_nonnegative_readings_iff (r d : ℚ) :
    (∃ a b : ℚ, 0 ≤ a ∧ 0 ≤ b ∧ a - b = d ∧
      ∀ x y z : ℚ, 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + 2 * (r * x * y + a * x * z + b * y * z)) ↔
    r ^ 2 + d ^ 2 ≤ 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl, gram⟩
    have hr : r ≤ 1 := by nlinarith only [gram 1 (-1) 0]
    rcases le_total b a with hab | hba
    · have residual := gram 1 (-r) (-(a - b))
      have correction := mul_nonneg (mul_nonneg (sub_nonneg.mpr hr) hb) (sub_nonneg.mpr hab)
      nlinarith only [residual, correction]
    · have residual := gram (-r) 1 (a - b)
      have correction := mul_nonneg (mul_nonneg (sub_nonneg.mpr hr) ha) (sub_nonneg.mpr hba)
      nlinarith only [residual, correction]
  · intro hd
    have slack : 0 ≤ 1 - r ^ 2 - d ^ 2 := by linarith
    rcases le_total 0 d with h | h
    · refine ⟨d, 0, h, le_rfl, sub_zero _, ?_⟩
      intro x y z
      nlinarith only [sq_nonneg (y + r * x), sq_nonneg (z + d * x), mul_nonneg slack (sq_nonneg x)]
    · refine ⟨0, -d, le_rfl, neg_nonneg.mpr h, by ring, ?_⟩
      intro x y z
      nlinarith only [sq_nonneg (x + r * y), sq_nonneg (z - d * y), mul_nonneg slack (sq_nonneg y)]

end D5.S3.Quantum.AURICOmega.ThreeReadingContrast
