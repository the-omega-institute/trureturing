/- GID: D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction
   generality: I
   mirror-B: D5/B/S3/Analytic/Certified/TrigEnvelopePhaseReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certified trigonometric envelopes, golden floors, phase reduction, and sums. -/

import Mathlib
import D5.S3.Analytic.GoldenEulerBeta

/- Library-search audit trail (2026-09-05):
   * Pinned Mathlib supplies `alternating_series_error_bound`,
     `Real.hasSum_cos`, `Real.cos_eq_tsum`, `Real.hasSum_sin`,
     `Real.sin_eq_tsum`, `Real.hasSum_cosh`, `Real.hasSum_sinh`,
     `Real.cos_abs`, `Real.sin_neg`, `Real.cos_sub_int_mul_two_pi`,
     `Real.sin_sub_int_mul_two_pi`, `Real.pi_gt_d20`, `Real.pi_lt_d20`,
     `Complex.norm_le_abs_re_add_abs_im`, and `Int.floor_add_fract`.
   * The frozen `o5_beta_closed_form` supplies the independent beta identity.
   * Repository and pinned-Mathlib shape searches found no existing arbitrary-order
     cosine or sine envelope, explicit 61-entry golden floor table, reduced-phase
     interval lemma, or matching mixed-sign coordinate accumulation theorem. -/

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

/-! ## Phase range reduction -/

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

#print axioms abs_cos_sub_partial_le
#print axioms abs_sin_sub_partial_le
#print axioms exists_reduced_phase
#print axioms sum_re_le_of_bounds
#print axioms sum_im_le_of_bounds
#print axioms norm_le_of_re_im_bounds
#print axioms o5Beta_floor_table
#print axioms o5Beta_eq_affine

end

end D5.S3.Analytic.Certified.TrigEnvelopePhaseReduction
