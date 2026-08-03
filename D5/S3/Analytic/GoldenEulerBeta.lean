/- GID: D5/S3/Analytic/GoldenEulerBeta
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden Euler germ exponent beta(v): closed form, initial power law, growth. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S3.Analytic.GoldenEulerBeta

noncomputable section

/-- The exponent account for the golden Euler germ. -/
def o5Beta (v : ℕ) : ℝ :=
  ((⌊((v + 1 : ℕ) : ℝ) * Real.goldenRatio⌋ : ℤ) : ℝ) - 1 -
    (v : ℝ) * (1 - Real.goldenRatio)

private theorem goldenRatio_gt_eight_fifths :
    (8 : ℝ) / 5 < Real.goldenRatio := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem goldenRatio_lt_five_thirds :
    Real.goldenRatio < (5 : ℝ) / 3 := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem floor_two_mul_goldenRatio :
    ⌊(2 : ℝ) * Real.goldenRatio⌋ = (3 : ℤ) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths, goldenRatio_lt_five_thirds]

private theorem floor_three_mul_goldenRatio :
    ⌊(3 : ℝ) * Real.goldenRatio⌋ = (4 : ℤ) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths, goldenRatio_lt_five_thirds]

private theorem floor_four_mul_goldenRatio :
    ⌊(4 : ℝ) * Real.goldenRatio⌋ = (6 : ℤ) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths, goldenRatio_lt_five_thirds]

private theorem floor_five_mul_goldenRatio :
    ⌊(5 : ℝ) * Real.goldenRatio⌋ = (8 : ℤ) := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num at * <;>
    nlinarith [goldenRatio_gt_eight_fifths, goldenRatio_lt_five_thirds]

/-- Closed form of the golden Euler exponent account. -/
theorem o5_beta_closed_form (v : ℕ) :
    o5Beta v = Real.sqrt 5 * (v : ℝ) + 1 / Real.goldenRatio -
      Int.fract (((v + 1 : ℕ) : ℝ) * Real.goldenRatio) := by
  have hfloor :
      ((⌊((v : ℝ) + 1) * Real.goldenRatio⌋ : ℤ) : ℝ) +
          Int.fract (((v : ℝ) + 1) * Real.goldenRatio) =
        ((v : ℝ) + 1) * Real.goldenRatio :=
    Int.floor_add_fract (((v : ℝ) + 1) * Real.goldenRatio)
  rw [o5Beta, one_div, Real.inv_goldenRatio,
    ← Real.goldenRatio_sub_goldenConj]
  rw [← Real.one_sub_goldenConj]
  simp only [Nat.cast_add, Nat.cast_one] at ⊢
  linarith

/-- The first three exponent values are consecutive powers of the golden ratio. -/
theorem o5_beta_power_law :
    o5Beta 1 = Real.goldenRatio ^ 2 ∧
      o5Beta 2 = Real.goldenRatio ^ 3 ∧
      o5Beta 3 = Real.goldenRatio ^ 4 := by
  have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 = Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  have hfourth : Real.goldenRatio ^ 4 = 3 * Real.goldenRatio + 2 := by
    calc
      Real.goldenRatio ^ 4 = (Real.goldenRatio ^ 2) ^ 2 := by ring
      _ = (Real.goldenRatio + 1) ^ 2 := by rw [Real.goldenRatio_sq]
      _ = 3 * Real.goldenRatio + 2 := by
        nlinarith [Real.goldenRatio_sq]
  constructor
  · rw [o5Beta]
    norm_num
    rw [floor_two_mul_goldenRatio]
    norm_num
    ring
  constructor
  · rw [o5Beta]
    norm_num
    rw [floor_three_mul_goldenRatio, hcube]
    norm_num
    ring
  · rw [o5Beta]
    norm_num
    rw [floor_four_mul_goldenRatio, hfourth]
    norm_num
    ring

/-- The initial power law stops at the fourth exponent value. -/
theorem o5_beta_power_law_terminates :
    o5Beta 4 ≠ Real.goldenRatio ^ 5 := by
  have hcube : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
    calc
      Real.goldenRatio ^ 3 = Real.goldenRatio * Real.goldenRatio ^ 2 := by ring
      _ = Real.goldenRatio * (Real.goldenRatio + 1) := by
        rw [Real.goldenRatio_sq]
      _ = 2 * Real.goldenRatio + 1 := by
        nlinarith [Real.goldenRatio_sq]
  have hfifth : Real.goldenRatio ^ 5 = 3 + 5 * Real.goldenRatio := by
    calc
      Real.goldenRatio ^ 5 = Real.goldenRatio ^ 3 * Real.goldenRatio ^ 2 := by ring
      _ = (2 * Real.goldenRatio + 1) * (Real.goldenRatio + 1) := by
        rw [hcube, Real.goldenRatio_sq]
      _ = 3 + 5 * Real.goldenRatio := by
        nlinarith [Real.goldenRatio_sq]
  change
    ((⌊(5 : ℝ) * Real.goldenRatio⌋ : ℤ) : ℝ) - 1 -
      (4 : ℝ) * (1 - Real.goldenRatio) ≠ Real.goldenRatio ^ 5
  rw [floor_five_mul_goldenRatio, hfifth]
  norm_num
  nlinarith [Real.goldenRatio_pos]

/-- The exponent account has the linear lower bound obtained from `fract < 1`. -/
theorem o5_beta_growth (v : ℕ) :
    Real.sqrt 5 * (v : ℝ) + 1 / Real.goldenRatio - 1 ≤ o5Beta v := by
  rw [o5_beta_closed_form]
  linarith [Int.fract_lt_one (((v + 1 : ℕ) : ℝ) * Real.goldenRatio)]

end

end D5.S3.Analytic.GoldenEulerBeta
