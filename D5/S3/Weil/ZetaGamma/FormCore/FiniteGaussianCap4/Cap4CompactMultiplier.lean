/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4CompactMultiplier
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform signed compact multiplier control and global half-line domination. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Uniform signed compact multiplier control and global half-line domination. -/

set_option autoImplicit false

noncomputable section
namespace FiniteGaussianCap4

/-- The original tail multiplier, zero below the physical endpoint. -/
def capWeight (x : ℝ) : ℝ :=
  if Real.pi < x then
    (x / Real.pi) ^ (5 / 2 : ℝ) - 4 * (x / Real.pi) ^ (-7 / 2 : ℝ)
  else 0

/-- The signed correction, supported in the fixed interval (0,6). -/
def compactDebit (x : ℝ) : ℝ :=
  if 0 < x ∧ x < 6 then x ^ 2 / 10 - capWeight x else 0

private theorem pow_five_halves (r : ℝ) (hr : 0 < r) :
    r ^ (5 / 2 : ℝ) = r ^ 2 * Real.sqrt r := by
  calc
    _ = r ^ ((2 : ℕ) : ℝ) * r ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hr]
      norm_num
    _ = _ := by rw [Real.rpow_natCast, Real.sqrt_eq_rpow]

private theorem pi_square_bounds : (9 : ℝ) ≤ Real.pi ^ 2 ∧ Real.pi ^ 2 ≤ 10 := by
  constructor
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_lt_d2, Real.pi_pos]

private theorem debit_on_annulus (p r : ℝ)
    (hp : 9 ≤ p ^ 2) (hp' : p ^ 2 ≤ 10) (hr : 1 ≤ r) (hr' : r ≤ 2) :
    |(p ^ 2 / 10) * r ^ 2 - r ^ (5 / 2 : ℝ) +
      4 * r ^ (-7 / 2 : ℝ)| ≤ 4 := by
  have hr0 : 0 < r := by linarith
  have hs0 : 1 ≤ Real.sqrt r :=
    (Real.le_sqrt (by norm_num) hr0.le).2 (by simpa using hr)
  have hs1 : Real.sqrt r ≤ 3 / 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hi0 : 0 ≤ r ^ (-7 / 2 : ℝ) := Real.rpow_nonneg hr0.le _
  have hi1 : r ^ (-7 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num)
  have hsq : r ^ 2 ≤ 4 := by nlinarith
  have hlow := mul_le_mul_of_nonneg_right
    (show (9 / 10 : ℝ) ≤ p ^ 2 / 10 by linarith) (sq_nonneg r)
  have hupp := mul_le_mul_of_nonneg_right
    (show p ^ 2 / 10 ≤ (1 : ℝ) by linarith) (sq_nonneg r)
  have hslo := mul_le_mul_of_nonneg_left hs0 (sq_nonneg r)
  have hshi := mul_le_mul_of_nonneg_left hs1 (sq_nonneg r)
  rw [pow_five_halves r hr0, abs_le]
  constructor <;> nlinarith

private theorem debit_nonpositive_after_cutoff (p r : ℝ)
    (hp : p ^ 2 ≤ 10) (hr : (9 / 5 : ℝ) ≤ r) :
    (p ^ 2 / 10) * r ^ 2 ≤
      r ^ (5 / 2 : ℝ) - 4 * r ^ (-7 / 2 : ℝ) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hs : (4 / 3 : ℝ) ≤ Real.sqrt r :=
    (Real.le_sqrt (by norm_num) hr0.le).2 (by nlinarith)
  have hsq : (81 / 25 : ℝ) ≤ r ^ 2 := by nlinarith
  have hcub : (729 / 125 : ℝ) ≤ r ^ 3 :=
    by convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 5) hr 3 using 1 <;> norm_num
  have hpow : (4 : ℝ) ≤ r ^ (7 / 2 : ℝ) := by
    have he := Real.rpow_le_rpow_of_exponent_le hr1
      (by norm_num : (3 : ℝ) ≤ 7 / 2)
    rw [Real.rpow_ofNat] at he
    linarith
  have hinv : r ^ (-7 / 2 : ℝ) ≤ 1 / 4 := by
    rw [show (-7 / 2 : ℝ) = -(7 / 2 : ℝ) by ring, Real.rpow_neg hr0.le]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hpow
  have hcoef := mul_le_mul_of_nonneg_right
    (show p ^ 2 / 10 ≤ (1 : ℝ) by linarith) (sq_nonneg r)
  have hsprod := mul_le_mul_of_nonneg_left hs (sq_nonneg r)
  rw [pow_five_halves r hr0]
  nlinarith

/-- Full signed multiplier bound; the right endpoint is treated separately. -/
theorem compactDebit_abs_le_four (x : ℝ) : |compactDebit x| ≤ 4 := by
  by_cases hx : 0 < x ∧ x < 6
  · rw [compactDebit, if_pos hx]
    by_cases hpi : Real.pi < x
    · rw [capWeight, if_pos hpi]
      have hr : 1 ≤ x / Real.pi := (le_div_iff₀ Real.pi_pos).2 (by linarith)
      have hr' : x / Real.pi ≤ 2 := (div_le_iff₀ Real.pi_pos).2
        (by linarith [Real.pi_gt_three])
      have hident : x ^ 2 / 10 =
          (Real.pi ^ 2 / 10) * (x / Real.pi) ^ 2 := by
        field_simp [Real.pi_ne_zero]
        <;> ring
      rw [hident]
      convert debit_on_annulus Real.pi (x / Real.pi)
        pi_square_bounds.1 pi_square_bounds.2 hr hr' using 1 <;> congr 1 <;> ring
    · rw [capWeight, if_neg hpi, sub_zero]
      have hxpi : x ≤ Real.pi := le_of_not_gt hpi
      have hsq : x ^ 2 ≤ Real.pi ^ 2 :=
        pow_le_pow_left₀ hx.1.le hxpi 2
      rw [abs_of_nonneg (by positivity)]
      nlinarith [pi_square_bounds.2]
  · simp [compactDebit, hx]

/-- Pointwise domination on the entire positive physical half-line. -/
theorem capWeight_ge_quadratic_minus_compact (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 / 10 - compactDebit x ≤ capWeight x := by
  by_cases hmid : 0 < x ∧ x < 6
  · simp only [compactDebit, if_pos hmid]
    linarith
  · rw [compactDebit, if_neg hmid, sub_zero]
    by_cases hz : x = 0
    · simp [hz, capWeight, not_lt_of_ge Real.pi_pos.le]
    · have hx6 : 6 ≤ x := by
        have hx0 : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
        exact le_of_not_gt (fun h => hmid ⟨hx0, h⟩)
      have hpi : Real.pi < x := by linarith [Real.pi_lt_d2]
      rw [capWeight, if_pos hpi]
      have hr : (9 / 5 : ℝ) ≤ x / Real.pi :=
        (le_div_iff₀ Real.pi_pos).2 (by nlinarith [Real.pi_lt_d2])
      have hident : x ^ 2 / 10 =
          (Real.pi ^ 2 / 10) * (x / Real.pi) ^ 2 := by
        field_simp [Real.pi_ne_zero]
        <;> ring
      rw [hident]
      exact debit_nonpositive_after_cutoff Real.pi (x / Real.pi)
        pi_square_bounds.2 hr

end FiniteGaussianCap4
