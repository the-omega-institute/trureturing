/- GID: D5/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/AffinePolynomialPairAlternatingPolar
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan]
   utility: none
   digest: The alternating affine pair is (1+2i)(1-i)^m with a continuous polar angle. -/

import D5.S1.Recurrence.Invariants.AffinePolynomialPairRowSums
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

/-! The alternating affine pair, its complex form and its continuous polar angle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.AffinePolynomialPairAlternatingPolar

open D5.S1.Recurrence.Invariants.AffinePolynomialPairBinomialCoefficients
open D5.S1.Recurrence.Invariants.AffinePolynomialPairRowSums

/-- The pair `(a_m, b_m)` with `a_0 = 1`, `b_0 = 2`, `a_(m+1) = a_m + b_m` and
`b_(m+1) = b_m - a_m`. -/
def ab : ℕ → ℤ × ℤ
  | 0 => (1, 2)
  | m + 1 => ((ab m).1 + (ab m).2, (ab m).2 - (ab m).1)

/-- `a_m`, the first component; it equals `v_(m+1)(-1)`. -/
def a (m : ℕ) : ℤ := (ab m).1
/-- `b_m`, the second component. -/
def b (m : ℕ) : ℤ := (ab m).2

private theorem complex_form (m : ℕ) :
    (a m : ℂ) + b m * Complex.I = (1 + 2 * Complex.I) * (1 - Complex.I) ^ m := by
  induction m with
  | zero => simp [a, b, ab]
  | succ m ih =>
    simp only [a, b, ab] at ih ⊢
    push_cast
    rw [pow_succ, ← mul_assoc, ← ih]
    ring_nf
    rw [Complex.I_sq]
    ring

private theorem four_step (m : ℕ) : a (m + 4) = -4 * a m ∧ b (m + 4) = -4 * b m := by
  simp only [a, b, ab]
  constructor <;> ring

private theorem b_values : b 0 = 2 ∧ b 1 = 1 ∧ b 2 = -2 ∧ b 3 = -6 ∧ b 18 = -512 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide⟩

private theorem a_is_v (m : ℕ) : a m = w (m + 1) := by
  have hrec := (result).2.2.2.1
  have hw1 := (result).2.2.2.2.1
  have hw2 := (result).2.2.2.2.2
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp [a, ab, hw1]
    · simp [a, ab, hw2]
    · rw [hrec (m + 1) (by omega), ← ih (m + 1) (by omega), ← ih m (by omega)]
      simp only [a, ab]
      ring

private theorem u_identity (n : ℕ) (hn : 1 ≤ n) :
    ((pair (n - 1)).1).eval (-1) = a n - a (n - 1) - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [a_is_v, a_is_v, show k + 1 - 1 = k by omega]
  simp only [w, show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega, pair,
    Polynomial.eval_add, Polynomial.eval_one]
  ring

open Real in
private theorem polar (m : ℕ) :
    let α := arctan 2
    let θ := α - m * π / 4
    let A := √5 * (16 : ℝ) ^ (α / (2 * π))
    let B := (16 : ℝ) ^ (-1 / (2 * π))
    (a m : ℝ) = A * B ^ θ * cos θ ∧ (b m : ℝ) = A * B ^ θ * sin θ := by
  intro α θ A B
  have hπ : π ≠ 0 := pi_ne_zero
  have hR : ∀ k : ℕ, A * B ^ (α - k * π / 4) = √5 * (16 : ℝ) ^ ((k : ℝ) / 8) := by
    intro k
    simp only [A, B]
    rw [← rpow_mul (by norm_num), mul_assoc, ← rpow_add (by norm_num)]
    congr 2
    field_simp
    ring
  have h16 : (16 : ℝ) ^ ((1 : ℝ) / 8) = √2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← rpow_mul (by norm_num), sqrt_eq_rpow]
    norm_num
  have hs2 : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  simp only [θ, hR]
  induction m with
  | zero =>
    simp only [a, b, ab, Nat.cast_zero, zero_mul, zero_div, sub_zero, rpow_zero, mul_one]
    have h5 : √5 ≠ 0 := by positivity
    rw [cos_arctan, sin_arctan, show (1 : ℝ) + 2 ^ 2 = 5 by norm_num]
    constructor <;> field_simp <;> norm_num
  | succ m ih =>
    obtain ⟨ha, hb⟩ := ih
    have hstep : (16 : ℝ) ^ (((m : ℝ) + 1) / 8) = (16 : ℝ) ^ ((m : ℝ) / 8) * √2 := by
      rw [← h16, ← rpow_add (by norm_num)]; ring_nf
    have hc : cos (α - ((m : ℝ) + 1) * π / 4) =
        (cos (α - m * π / 4) + sin (α - m * π / 4)) * (√2 / 2) := by
      rw [show α - ((m : ℝ) + 1) * π / 4 = (α - m * π / 4) - π / 4 by ring,
        cos_sub, cos_pi_div_four, sin_pi_div_four]; ring
    have hsn : sin (α - ((m : ℝ) + 1) * π / 4) =
        (sin (α - m * π / 4) - cos (α - m * π / 4)) * (√2 / 2) := by
      rw [show α - ((m : ℝ) + 1) * π / 4 = (α - m * π / 4) - π / 4 by ring,
        sin_sub, cos_pi_div_four, sin_pi_div_four]; ring
    simp only [a, b, ab] at ha hb ⊢
    push_cast
    rw [ha, hb, hstep, hc, hsn]
    constructor
    · linear_combination (√5 * (16 : ℝ) ^ ((m : ℝ) / 8)) *
        (cos (α - m * π / 4) + sin (α - m * π / 4)) / 2 * hs2 * (-1)
    · linear_combination (√5 * (16 : ℝ) ^ ((m : ℝ) / 8)) *
        (sin (α - m * π / 4) - cos (α - m * π / 4)) / 2 * hs2 * (-1)

/-- Corollary 9 of the Ma–Zhang note on A208509, with the source's zero-based index `m`:
`a_m = v_(m+1)(-1)` for the pair `a_0 = 1`, `b_0 = 2`, `a_(m+1) = a_m + b_m`,
`b_(m+1) = b_m - a_m`; `a_m + i b_m = (1 + 2i)(1 - i)^m`; `a_(m+4) = -4 a_m`, `b_(m+4) = -4 b_m`;
`b_0, …, b_3 = 2, 1, -2, -6` and `b_18 = -512`; the polar form with the continuous angle
`θ_m = arctan 2 - mπ/4`, `A = √5 · 16^(arctan 2/(2π))`, `B = 16^(-1/(2π))`; and
`u_n(-1) = a_n - a_(n-1) - 1` for `n ≥ 1`. -/
theorem result :
    (∀ m : ℕ, a m = w (m + 1)) ∧
    (∀ m : ℕ, (a m : ℂ) + b m * Complex.I = (1 + 2 * Complex.I) * (1 - Complex.I) ^ m) ∧
    (∀ m : ℕ, a (m + 4) = -4 * a m ∧ b (m + 4) = -4 * b m) ∧
    (b 0 = 2 ∧ b 1 = 1 ∧ b 2 = -2 ∧ b 3 = -6 ∧ b 18 = -512) ∧
    (∀ m : ℕ,
      (a m : ℝ) = √5 * (16 : ℝ) ^ (Real.arctan 2 / (2 * Real.pi)) *
          ((16 : ℝ) ^ (-1 / (2 * Real.pi))) ^ (Real.arctan 2 - m * Real.pi / 4) *
          Real.cos (Real.arctan 2 - m * Real.pi / 4) ∧
      (b m : ℝ) = √5 * (16 : ℝ) ^ (Real.arctan 2 / (2 * Real.pi)) *
          ((16 : ℝ) ^ (-1 / (2 * Real.pi))) ^ (Real.arctan 2 - m * Real.pi / 4) *
          Real.sin (Real.arctan 2 - m * Real.pi / 4)) ∧
    (∀ n : ℕ, 1 ≤ n → ((pair (n - 1)).1).eval (-1) = a n - a (n - 1) - 1) :=
  ⟨a_is_v, complex_form, four_step, b_values, polar, u_identity⟩

end D5.S1.Recurrence.Invariants.AffinePolynomialPairAlternatingPolar
