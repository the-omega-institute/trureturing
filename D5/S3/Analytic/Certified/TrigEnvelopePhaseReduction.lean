/- GID: D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction
   generality: I
   mirror-B: D5/B/S3/Analytic/Certified/TrigEnvelopePhaseReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certified trigonometric envelopes, golden floors, phase reduction, and sums. -/

import D5.S3.Analytic.GoldenEulerBeta
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- Library-search audit trail (2026-09-05):
   * Pinned Mathlib supplies `alternating_series_error_bound`,
     `Real.hasSum_cos`, `Real.cos_eq_tsum`, `Real.hasSum_sin`,
     `Real.sin_eq_tsum`, `Real.hasSum_cosh`, `Real.hasSum_sinh`,
     `Real.cos_abs`, `Real.sin_neg`, `Real.cos_sub_int_mul_two_pi`,
     `Real.sin_sub_int_mul_two_pi`, `Real.cos_add_int_mul_pi`,
     `Real.sin_add_int_mul_pi`, `Real.pi_gt_d20`, `Real.pi_lt_d20`,
     `Complex.norm_le_abs_re_add_abs_im`, and `Int.floor_add_fract`.
   * The frozen `o5_beta_closed_form` supplies the independent beta identity.
   * Repository and pinned-Mathlib shape searches found no existing arbitrary-order
     cosine or sine envelope, explicit 61-entry golden floor table, rational-to-index
     phase decision theorem, or matching mixed-sign coordinate accumulation theorem. -/

namespace D5.S3.Analytic.Certified.TrigEnvelopePhaseReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.Analytic.GoldenEulerBeta

noncomputable section

/-! ## Arbitrary-order Taylor enclosures -/

private theorem evenCoeff_antitone (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Antitone (fun k : ℕ => y ^ (2 * k) / ((2 * k).factorial : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro k
  apply div_le_div₀
  · positivity
  · exact pow_le_pow_of_le_one hy0 hy1 (by omega)
  · exact_mod_cast Nat.factorial_pos (2 * k)
  · exact_mod_cast Nat.factorial_le (by omega : 2 * k ≤ 2 * (k + 1))

private theorem abs_cos_sub_partial_le_nonneg (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1) (n : ℕ) :
    |Real.cos x - ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)| ≤
      x ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  have h := alternating_series_error_bound
    (fun k : ℕ => x ^ (2 * k) / ((2 * k).factorial : ℝ))
    (evenCoeff_antitone x hx0 hx)
    (Real.hasSum_cosh x).summable n
  have hcos :
      (∑' k : ℕ, (-1 : ℝ) ^ k *
        (x ^ (2 * k) / ((2 * k).factorial : ℝ))) = Real.cos x := by
    simpa [mul_div_assoc] using (Real.hasSum_cos x).tsum_eq
  rw [hcos] at h
  simpa [mul_div_assoc] using h

/-- The cosine Taylor polynomial of every order has its sharp next-term
alternating-series error bound throughout `|x| ≤ 1`. -/
theorem abs_cos_sub_partial_le (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    |Real.cos x - ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)| ≤
      |x| ^ (2 * n) / ((2 * n).factorial : ℝ) := by
  have h := abs_cos_sub_partial_le_nonneg |x| (abs_nonneg x) hx n
  simpa only [Real.cos_abs, (even_two_mul _).pow_abs] using h

private theorem oddCoeff_antitone (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Antitone (fun k : ℕ => y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro k
  apply div_le_div₀
  · positivity
  · exact pow_le_pow_of_le_one hy0 hy1 (by omega)
  · exact_mod_cast Nat.factorial_pos (2 * k + 1)
  · exact_mod_cast Nat.factorial_le (by omega : 2 * k + 1 ≤ 2 * (k + 1) + 1)

private theorem abs_sin_sub_partial_le_nonneg (x : ℝ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1) (n : ℕ) :
    |Real.sin x - ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)| ≤
      x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
  have h := alternating_series_error_bound
    (fun k : ℕ => x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
    (oddCoeff_antitone x hx0 hx)
    (Real.hasSum_sinh x).summable n
  have hsin :
      (∑' k : ℕ, (-1 : ℝ) ^ k *
        (x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))) = Real.sin x := by
    simpa [mul_div_assoc] using (Real.hasSum_sin x).tsum_eq
  rw [hsin] at h
  simpa [mul_div_assoc] using h

/-- The sine Taylor polynomial of every order has its sharp next-term
alternating-series error bound throughout `|x| ≤ 1`. -/
theorem abs_sin_sub_partial_le (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    |Real.sin x - ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)| ≤
      |x| ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
  by_cases hx0 : 0 ≤ x
  · have hx1 : x ≤ 1 := by simpa [abs_of_nonneg hx0] using hx
    simpa [abs_of_nonneg hx0] using abs_sin_sub_partial_le_nonneg x hx0 hx1 n
  · have hxneg : x < 0 := lt_of_not_ge hx0
    have h := abs_sin_sub_partial_le_nonneg (-x) (by linarith)
      (by simpa [abs_of_neg hxneg] using hx) n
    have hsum :
        (∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (-x) ^ (2 * k + 1) /
          ((2 * k + 1).factorial : ℝ)) =
          -(∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) /
            ((2 * k + 1).factorial : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [(odd_two_mul_add_one k).neg_pow]
      ring
    rw [Real.sin_neg, hsum] at h
    simpa only [abs_of_neg hxneg, neg_sub_neg, abs_sub_comm] using h

/-! ## Certified phase range reduction -/

/-- An interval enclosure that fits inside a unit residual window produces an
exact periodic representative for both cosine and sine. -/
theorem exists_reduced_phase (theta a b : ℝ) (k : ℤ)
    (ha : a ≤ theta) (hb : theta ≤ b)
    (hk : |a - k * (2 * Real.pi)| + (b - a) ≤ 1) :
    ∃ r, theta = r + k * (2 * Real.pi) ∧ |r| ≤ 1 ∧
      Real.cos theta = Real.cos r ∧ Real.sin theta = Real.sin r := by
  refine ⟨theta - k * (2 * Real.pi), by ring, ?_, ?_, ?_⟩
  · calc
      |theta - k * (2 * Real.pi)| =
          |(a - k * (2 * Real.pi)) + (theta - a)| := by ring_nf
      _ ≤ |a - k * (2 * Real.pi)| + |theta - a| := abs_add_le _ _
      _ = |a - k * (2 * Real.pi)| + (theta - a) := by
        rw [abs_of_nonneg (sub_nonneg.mpr ha)]
      _ ≤ |a - k * (2 * Real.pi)| + (b - a) := by linarith
      _ ≤ 1 := hk
  · exact (Real.cos_sub_int_mul_two_pi theta k).symm
  · exact (Real.sin_sub_int_mul_two_pi theta k).symm

/-- A rational approximation to pi whose certified error is small enough for
rational phase-index decisions. -/
def piApprox : ℚ := 314159265358979323846 / 10 ^ 20

/-- Mathlib's pinned twenty-decimal bounds certify the rational pi carrier. -/
theorem abs_pi_sub_piApprox_lt :
    |Real.pi - (piApprox : ℝ)| < (1 / 10 ^ 19 : ℝ) := by
  rw [abs_lt]
  constructor
  · have h := Real.pi_gt_d20
    norm_num [piApprox] at h ⊢
    linarith
  · have h := Real.pi_lt_d20
    norm_num [piApprox] at h ⊢
    linarith

/-- The nearest integer to `a / (2 * piApprox)`, computed in rational
arithmetic. Its certified meaning is supplied by `exists_reduced_phase_of_rat`. -/
def phaseIndex (a : ℚ) : ℤ := ⌊a / (2 * piApprox) + 1 / 2⌋

/-- The nearest integer to `a / piApprox`, used when a sign-changing pi shift
is required. Its certified meaning is supplied by
`exists_reduced_phase_pi_of_rat`. -/
def phaseIndexPi (a : ℚ) : ℤ := ⌊a / piApprox + 1 / 2⌋

private theorem abs_floor_div_add_half_le (a d : ℚ)
    (hd : 1 ≤ d) (ha : |a| ≤ 10 ^ 7) :
    |⌊a / d + 1 / 2⌋| ≤ (10000001 : ℤ) := by
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd
  have habs_div : |a / d| ≤ |a| := by
    rw [abs_div, abs_of_nonneg hd0]
    exact div_le_self (abs_nonneg a) hd
  have hbound : |a / d| ≤ 10 ^ 7 := habs_div.trans ha
  rw [abs_le] at hbound ⊢
  constructor
  · rw [Int.le_floor]
    norm_num at hbound ⊢
    linarith
  · rw [Int.floor_le_iff]
    norm_num at hbound ⊢
    linarith

private theorem abs_phaseIndex_le (a : ℚ) (ha : |a| ≤ 10 ^ 7) :
    |phaseIndex a| ≤ (10000001 : ℤ) := by
  apply abs_floor_div_add_half_le
  · norm_num [piApprox]
  · exact ha

private theorem abs_phaseIndexPi_le (a : ℚ) (ha : |a| ≤ 10 ^ 7) :
    |phaseIndexPi a| ≤ (10000001 : ℤ) := by
  apply abs_floor_div_add_half_le
  · norm_num [piApprox]
  · exact ha

private theorem phase_error_two_pi_lt (a : ℚ) (ha : |a| ≤ 10 ^ 7) :
    |((phaseIndex a : ℤ) : ℝ) * (2 * Real.pi) -
        ((phaseIndex a : ℤ) : ℝ) * (2 * (piApprox : ℝ))| <
      (1 / 100 : ℝ) := by
  have hk_int := abs_phaseIndex_le a ha
  have hk_real : |((phaseIndex a : ℤ) : ℝ)| ≤ (10000001 : ℝ) := by
    exact_mod_cast hk_int
  calc
    |((phaseIndex a : ℤ) : ℝ) * (2 * Real.pi) -
        ((phaseIndex a : ℤ) : ℝ) * (2 * (piApprox : ℝ))| =
        |((phaseIndex a : ℤ) : ℝ)| *
          (2 * |Real.pi - (piApprox : ℝ)|) := by
            rw [show ((phaseIndex a : ℤ) : ℝ) * (2 * Real.pi) -
                ((phaseIndex a : ℤ) : ℝ) * (2 * (piApprox : ℝ)) =
              ((phaseIndex a : ℤ) : ℝ) *
                (2 * (Real.pi - (piApprox : ℝ))) by ring,
              abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (10000001 : ℝ) * (2 * |Real.pi - (piApprox : ℝ)|) := by
      exact mul_le_mul_of_nonneg_right hk_real (by positivity)
    _ < (10000001 : ℝ) * (2 * (1 / 10 ^ 19 : ℝ)) := by
      exact mul_lt_mul_of_pos_left
        (mul_lt_mul_of_pos_left abs_pi_sub_piApprox_lt (by norm_num)) (by norm_num)
    _ < (1 / 100 : ℝ) := by norm_num

private theorem phase_error_pi_lt (a : ℚ) (ha : |a| ≤ 10 ^ 7) :
    |((phaseIndexPi a : ℤ) : ℝ) * Real.pi -
        ((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ)| <
      (1 / 100 : ℝ) := by
  have hk_int := abs_phaseIndexPi_le a ha
  have hk_real : |((phaseIndexPi a : ℤ) : ℝ)| ≤ (10000001 : ℝ) := by
    exact_mod_cast hk_int
  calc
    |((phaseIndexPi a : ℤ) : ℝ) * Real.pi -
        ((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ)| =
        |((phaseIndexPi a : ℤ) : ℝ)| *
          |Real.pi - (piApprox : ℝ)| := by
            rw [show ((phaseIndexPi a : ℤ) : ℝ) * Real.pi -
                ((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ) =
              ((phaseIndexPi a : ℤ) : ℝ) *
                (Real.pi - (piApprox : ℝ)) by ring, abs_mul]
    _ ≤ (10000001 : ℝ) * |Real.pi - (piApprox : ℝ)| := by
      exact mul_le_mul_of_nonneg_right hk_real (abs_nonneg _)
    _ < (10000001 : ℝ) * (1 / 10 ^ 19 : ℝ) := by
      exact mul_lt_mul_of_pos_left abs_pi_sub_piApprox_lt (by norm_num)
    _ < (1 / 100 : ℝ) := by norm_num

/-- Rational interval data computes the two-pi phase index and absorbs the
certified pi-approximation error before applying exact periodicity. -/
theorem exists_reduced_phase_of_rat (a b : ℚ) (theta : ℝ)
    (ha : (a : ℝ) ≤ theta) (hb : theta ≤ (b : ℝ))
    (hsize : |a| ≤ 10 ^ 7)
    (hres : |a - (phaseIndex a : ℚ) * (2 * piApprox)| + (b - a) ≤ 99 / 100) :
    ∃ r : ℝ, theta = r + phaseIndex a * (2 * Real.pi) ∧ |r| ≤ 1 ∧
      Real.cos theta = Real.cos r ∧ Real.sin theta = Real.sin r := by
  have hres_real :
      |(a : ℝ) - ((phaseIndex a : ℤ) : ℝ) * (2 * (piApprox : ℝ))| +
          ((b : ℝ) - (a : ℝ)) ≤ (99 / 100 : ℝ) := by
    have hcast :
        ((|a - (phaseIndex a : ℚ) * (2 * piApprox)| + (b - a) : ℚ) : ℝ) ≤
          (((99 / 100 : ℚ) : ℝ)) := by
      exact_mod_cast hres
    simpa using hcast
  have herr := phase_error_two_pi_lt a hsize
  have herr_rev :
      |((phaseIndex a : ℤ) : ℝ) * (2 * (piApprox : ℝ)) -
        ((phaseIndex a : ℤ) : ℝ) * (2 * Real.pi)| < (1 / 100 : ℝ) := by
    simpa only [abs_sub_comm] using herr
  have hexact_lt :
      |(a : ℝ) - ((phaseIndex a : ℤ) : ℝ) * (2 * Real.pi)| +
          ((b : ℝ) - (a : ℝ)) < 1 := by
    calc
      |(a : ℝ) - ((phaseIndex a : ℤ) : ℝ) * (2 * Real.pi)| +
          ((b : ℝ) - (a : ℝ)) =
          |((a : ℝ) - ((phaseIndex a : ℤ) : ℝ) *
              (2 * (piApprox : ℝ))) +
            (((phaseIndex a : ℤ) : ℝ) * (2 * (piApprox : ℝ)) -
              ((phaseIndex a : ℤ) : ℝ) * (2 * Real.pi))| +
            ((b : ℝ) - (a : ℝ)) := by ring_nf
      _ ≤ (|(a : ℝ) - ((phaseIndex a : ℤ) : ℝ) *
              (2 * (piApprox : ℝ))| +
            |((phaseIndex a : ℤ) : ℝ) * (2 * (piApprox : ℝ)) -
              ((phaseIndex a : ℤ) : ℝ) * (2 * Real.pi)|) +
            ((b : ℝ) - (a : ℝ)) := by gcongr; exact abs_add_le _ _
      _ = (|(a : ℝ) - ((phaseIndex a : ℤ) : ℝ) *
              (2 * (piApprox : ℝ))| + ((b : ℝ) - (a : ℝ))) +
            |((phaseIndex a : ℤ) : ℝ) * (2 * (piApprox : ℝ)) -
              ((phaseIndex a : ℤ) : ℝ) * (2 * Real.pi)| := by
            ring
      _ < (99 / 100 : ℝ) + 1 / 100 := add_lt_add_of_le_of_lt hres_real herr_rev
      _ = 1 := by norm_num
  exact exists_reduced_phase theta (a : ℝ) (b : ℝ) (phaseIndex a)
    ha hb hexact_lt.le

/-- Rational interval data computes a pi phase index. The resulting exact
identities record the sign change for odd indices. -/
theorem exists_reduced_phase_pi_of_rat (a b : ℚ) (theta : ℝ)
    (ha : (a : ℝ) ≤ theta) (hb : theta ≤ (b : ℝ))
    (hsize : |a| ≤ 10 ^ 7)
    (hres : |a - (phaseIndexPi a : ℚ) * piApprox| + (b - a) ≤ 99 / 100) :
    ∃ r : ℝ, theta = r + phaseIndexPi a * Real.pi ∧ |r| ≤ 1 ∧
      Real.cos theta = (-1 : ℝ) ^ phaseIndexPi a * Real.cos r ∧
      Real.sin theta = (-1 : ℝ) ^ phaseIndexPi a * Real.sin r := by
  have hres_real :
      |(a : ℝ) - ((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ)| +
          ((b : ℝ) - (a : ℝ)) ≤ (99 / 100 : ℝ) := by
    have hcast :
        ((|a - (phaseIndexPi a : ℚ) * piApprox| + (b - a) : ℚ) : ℝ) ≤
          (((99 / 100 : ℚ) : ℝ)) := by
      exact_mod_cast hres
    simpa using hcast
  have herr := phase_error_pi_lt a hsize
  have herr_rev :
      |((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ) -
        ((phaseIndexPi a : ℤ) : ℝ) * Real.pi| < (1 / 100 : ℝ) := by
    simpa only [abs_sub_comm] using herr
  have hexact_lt :
      |(a : ℝ) - ((phaseIndexPi a : ℤ) : ℝ) * Real.pi| +
          ((b : ℝ) - (a : ℝ)) < 1 := by
    calc
      |(a : ℝ) - ((phaseIndexPi a : ℤ) : ℝ) * Real.pi| +
          ((b : ℝ) - (a : ℝ)) =
          |((a : ℝ) - ((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ)) +
            (((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ) -
              ((phaseIndexPi a : ℤ) : ℝ) * Real.pi)| +
            ((b : ℝ) - (a : ℝ)) := by ring_nf
      _ ≤ (|(a : ℝ) - ((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ)| +
            |((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ) -
              ((phaseIndexPi a : ℤ) : ℝ) * Real.pi|) +
            ((b : ℝ) - (a : ℝ)) := by gcongr; exact abs_add_le _ _
      _ = (|(a : ℝ) - ((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ)| +
            ((b : ℝ) - (a : ℝ))) +
          |((phaseIndexPi a : ℤ) : ℝ) * (piApprox : ℝ) -
            ((phaseIndexPi a : ℤ) : ℝ) * Real.pi| := by
            ring
      _ < (99 / 100 : ℝ) + 1 / 100 := add_lt_add_of_le_of_lt hres_real herr_rev
      _ = 1 := by norm_num
  refine ⟨theta - phaseIndexPi a * Real.pi, by ring, ?_, ?_, ?_⟩
  · calc
      |theta - phaseIndexPi a * Real.pi| =
          |((a : ℝ) - phaseIndexPi a * Real.pi) + (theta - (a : ℝ))| := by
            ring_nf
      _ ≤ |(a : ℝ) - phaseIndexPi a * Real.pi| + |theta - (a : ℝ)| :=
        abs_add_le _ _
      _ = |(a : ℝ) - phaseIndexPi a * Real.pi| + (theta - (a : ℝ)) := by
        rw [abs_of_nonneg (sub_nonneg.mpr ha)]
      _ ≤ |(a : ℝ) - phaseIndexPi a * Real.pi| + ((b : ℝ) - (a : ℝ)) := by
        linarith
      _ ≤ 1 := hexact_lt.le
  · simpa only [sub_add_cancel] using Real.cos_add_int_mul_pi
      (theta - phaseIndexPi a * Real.pi) (phaseIndexPi a)
  · simpa only [sub_add_cancel] using Real.sin_add_int_mul_pi
      (theta - phaseIndexPi a * Real.pi) (phaseIndexPi a)

/-! ## Mixed-sign complex accumulation -/

/-- Pointwise lower and upper real-part bounds accumulate over a finite sum. -/
theorem sum_re_le_of_bounds {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (lo hi : ι → ℝ)
    (h : ∀ i ∈ s, lo i ≤ (z i).re ∧ (z i).re ≤ hi i) :
    (∑ i ∈ s, lo i) ≤ (∑ i ∈ s, z i).re ∧
      (∑ i ∈ s, z i).re ≤ ∑ i ∈ s, hi i := by
  constructor
  · simpa using Finset.sum_le_sum fun i hi_mem => (h i hi_mem).1
  · simpa using Finset.sum_le_sum fun i hi_mem => (h i hi_mem).2

/-- Pointwise lower and upper imaginary-part bounds accumulate over a finite sum. -/
theorem sum_im_le_of_bounds {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (lo hi : ι → ℝ)
    (h : ∀ i ∈ s, lo i ≤ (z i).im ∧ (z i).im ≤ hi i) :
    (∑ i ∈ s, lo i) ≤ (∑ i ∈ s, z i).im ∧
      (∑ i ∈ s, z i).im ≤ ∑ i ∈ s, hi i := by
  constructor
  · simpa using Finset.sum_le_sum fun i hi_mem => (h i hi_mem).1
  · simpa using Finset.sum_le_sum fun i hi_mem => (h i hi_mem).2

/-- Separate absolute bounds on the two coordinates give an additive complex
norm bound. This companion is consumed by the L2c center-norm certificate. -/
theorem norm_le_of_re_im_bounds {z : ℂ} {a b : ℝ}
    (hre : |z.re| ≤ a) (him : |z.im| ≤ b) : ‖z‖ ≤ a + b :=
  (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hre him)

/-! ## Exact floor table for the golden exponent -/

/-- The exact values of `floor ((v + 1) * phi)` for `0 ≤ v ≤ 60`. Its
correctness and its affine beta consequence are proved below. -/
def o5FloorTable : Fin 61 → ℤ :=
  ![1, 3, 4, 6, 8, 9, 11, 12, 14, 16, 17, 19, 21, 22, 24, 25,
    27, 29, 30, 32, 33, 35, 37, 38, 40, 42, 43, 45, 46, 48, 50,
    51, 53, 55, 56, 58, 59, 61, 63, 64, 66, 67, 69, 71, 72, 74,
    76, 77, 79, 80, 82, 84, 85, 87, 88, 90, 92, 93, 95, 97, 98]

private theorem goldenRatio_bounds :
    (1618033 / 1000000 : ℝ) < Real.goldenRatio ∧
      Real.goldenRatio < (809017 / 500000 : ℝ) := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  constructor <;> nlinarith

/-- Every entry of `o5FloorTable` is the exact golden-ratio floor. -/
theorem o5Beta_floor_table (v : ℕ) (hv : v ≤ 60) :
    ⌊((v + 1 : ℕ) : ℝ) * Real.goldenRatio⌋ =
      o5FloorTable ⟨v, by omega⟩ := by
  rcases goldenRatio_bounds with ⟨hphi_lo, hphi_hi⟩
  interval_cases v <;>
    rw [Int.floor_eq_iff] <;>
    constructor <;>
    norm_num [o5FloorTable] <;>
    nlinarith

/-- On the certified range, the frozen golden exponent is the affine
expression obtained from the exact floor table. -/
theorem o5Beta_eq_affine (v : ℕ) (hv : v ≤ 60) :
    o5Beta v =
      ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) - 1 - (v : ℝ) +
        (v : ℝ) * Real.goldenRatio := by
  let x : ℝ := ((v + 1 : ℕ) : ℝ) * Real.goldenRatio
  have hfloor := o5Beta_floor_table v hv
  have hfloor_real :
      ((⌊x⌋ : ℤ) : ℝ) = ((o5FloorTable ⟨v, by omega⟩ : ℤ) : ℝ) := by
    exact_mod_cast hfloor
  have hfract := Int.floor_add_fract x
  rw [hfloor_real] at hfract
  have hsqrt : Real.sqrt 5 = 2 * Real.goldenRatio - 1 := by
    rw [Real.goldenRatio]
    ring
  have hinv : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
    rw [one_div, Real.inv_goldenRatio, Real.goldenConj, Real.goldenRatio]
    ring
  rw [o5_beta_closed_form, hsqrt, hinv]
  dsimp [x] at hfract
  simp only [Nat.cast_add, Nat.cast_one] at hfract ⊢
  ring_nf at hfract ⊢
  linarith

/-! ## Fidelity witnesses -/

example : ∃ x : ℝ, |x| ≤ 1 := ⟨0, by norm_num⟩

example : Nonempty (Fin 61) := ⟨⟨0, by norm_num⟩⟩

example :
    ∃ theta a b : ℝ, ∃ k : ℤ,
      a ≤ theta ∧ theta ≤ b ∧
        |a - k * (2 * Real.pi)| + (b - a) ≤ 1 := by
  exact ⟨0, 0, 0, 0, by norm_num, by norm_num, by norm_num⟩

private theorem o5Beta_one_bounds :
    (1309 / 500 : ℝ) < o5Beta 1 ∧ o5Beta 1 < (65451 / 25000 : ℝ) := by
  rw [o5_beta_power_law.1, Real.goldenRatio_sq, Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  constructor <;> nlinarith

/-- The actual mode-one phase from the golden Euler germ is enclosed by a
rational interval whose computed pi index is three. -/
example :
    ∃ r : ℝ,
      (5256712292901926 / 10 ^ 15 : ℝ) * o5Beta 1 * Real.log 2 =
          r + phaseIndexPi (47 / 5) * Real.pi ∧
      |r| ≤ 1 ∧
      Real.cos ((5256712292901926 / 10 ^ 15 : ℝ) * o5Beta 1 * Real.log 2) =
        (-1 : ℝ) ^ phaseIndexPi (47 / 5) * Real.cos r ∧
      Real.sin ((5256712292901926 / 10 ^ 15 : ℝ) * o5Beta 1 * Real.log 2) =
        (-1 : ℝ) ^ phaseIndexPi (47 / 5) * Real.sin r := by
  let theta : ℝ :=
    (5256712292901926 / 10 ^ 15 : ℝ) * o5Beta 1 * Real.log 2
  have hc_lo : (21 / 4 : ℝ) < (5256712292901926 / 10 ^ 15 : ℝ) := by norm_num
  have hc_hi : (5256712292901926 / 10 ^ 15 : ℝ) <
      (52567123 / 10000000 : ℝ) := by norm_num
  have hlog_lo : (693 / 1000 : ℝ) < Real.log 2 :=
    (by norm_num : (693 / 1000 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hlog_hi : Real.log 2 < (693147181 / 1000000000 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hbeta_pos : 0 < o5Beta 1 :=
    (by norm_num : (0 : ℝ) < 1309 / 500).trans o5Beta_one_bounds.1
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htheta_lo :
      (21 / 4 : ℝ) * (1309 / 500) * (693 / 1000) < theta := by
    dsimp [theta]
    calc
      (21 / 4 : ℝ) * (1309 / 500) * (693 / 1000) <
          (5256712292901926 / 10 ^ 15 : ℝ) * (1309 / 500) *
            (693 / 1000) := by gcongr
      _ < (5256712292901926 / 10 ^ 15 : ℝ) * o5Beta 1 *
          (693 / 1000) := by gcongr; exact o5Beta_one_bounds.1
      _ < (5256712292901926 / 10 ^ 15 : ℝ) * o5Beta 1 * Real.log 2 := by
        gcongr
  have htheta_hi : theta <
      (52567123 / 10000000 : ℝ) * (65451 / 25000) *
        (693147181 / 1000000000) := by
    dsimp [theta]
    calc
      (5256712292901926 / 10 ^ 15 : ℝ) * o5Beta 1 * Real.log 2 <
          (52567123 / 10000000 : ℝ) * o5Beta 1 * Real.log 2 := by
        gcongr
      _ < (52567123 / 10000000 : ℝ) * (65451 / 25000) * Real.log 2 := by
        gcongr
        exact o5Beta_one_bounds.2
      _ < (52567123 / 10000000 : ℝ) * (65451 / 25000) *
          (693147181 / 1000000000) := by gcongr
  have ha : ((47 / 5 : ℚ) : ℝ) ≤ theta := by
    norm_num at htheta_lo ⊢
    linarith
  have hb : theta ≤ ((191 / 20 : ℚ) : ℝ) := by
    norm_num at htheta_hi ⊢
    linarith
  simpa only [theta] using exists_reduced_phase_pi_of_rat
    (47 / 5) (191 / 20) theta ha hb
    (by norm_num) (by norm_num [phaseIndexPi, piApprox])

#print axioms abs_cos_sub_partial_le
#print axioms abs_sin_sub_partial_le
#print axioms exists_reduced_phase
#print axioms abs_pi_sub_piApprox_lt
#print axioms exists_reduced_phase_of_rat
#print axioms exists_reduced_phase_pi_of_rat
#print axioms sum_re_le_of_bounds
#print axioms sum_im_le_of_bounds
#print axioms norm_le_of_re_im_bounds
#print axioms o5Beta_floor_table
#print axioms o5Beta_eq_affine

end

end D5.S3.Analytic.Certified.TrigEnvelopePhaseReduction
