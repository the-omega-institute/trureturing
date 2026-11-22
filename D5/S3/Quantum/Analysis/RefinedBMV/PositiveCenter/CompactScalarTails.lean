/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactScalarTails
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Degree-24 scalar Taylor bounds for the compact positive-center comparison. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterUpperTail
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-! Scalar Taylor approximations used in the compact positive-center kernel bound. -/

open scoped BigOperators

namespace RefinedBMV.PositiveCenter

noncomputable section

private def expTaylor (m : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range m, x ^ n / (n.factorial : ℝ)

private theorem expTaylor_error {m : ℕ} {x : ℝ} (hx : |x| / (m.succ : ℝ) ≤ 1 / 2) :
    |Real.exp x - expTaylor m x| ≤ |x| ^ m / (m.factorial : ℝ) * 2 := by
  have hratio : ‖(x : ℂ)‖ / (m.succ : ℝ) ≤ 1 / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hx
  unfold expTaylor
  exact_mod_cast Complex.exp_bound' hratio

/-- The degree-24 exponential Taylor polynomial. -/
def compactExpTaylor (x : ℝ) : ℝ := expTaylor 25 x

/-- Uniform absolute error of the exponential polynomial on `[-3/2, 3/2]`. -/
theorem compactExp_sub_taylor_abs_le {x : ℝ} (hx : |x| ≤ 3 / 2) :
    |Real.exp x - compactExpTaylor x| ≤ 2 * (3 / 2 : ℝ) ^ 25 / ((25 : ℕ).factorial : ℝ) := by
  have hratio : |x| / ((25 : ℕ).succ : ℝ) ≤ 1 / 2 := by
    norm_num
    linarith
  unfold compactExpTaylor
  calc
    _ ≤ |x| ^ 25 / ((25 : ℕ).factorial : ℝ) * 2 := expTaylor_error hratio
    _ ≤ (3 / 2 : ℝ) ^ 25 / ((25 : ℕ).factorial : ℝ) * 2 := by gcongr
    _ = _ := by ring

/-- The degree-24 Taylor polynomial for the exponential quotient. -/
def compactPhiTaylor (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 25, x ^ n / ((n + 1).factorial : ℝ)

private theorem phiTaylor_error {x : ℝ} (hx : x ≠ 0) (hx₁ : |x| ≤ 1) :
    |(Real.exp x - 1) / x - compactPhiTaylor x| ≤ 2 * |x| ^ 25 / ((26 : ℕ).factorial : ℝ) := by
  have hratio : |x| / ((26 : ℕ).succ : ℝ) ≤ 1 / 2 := by
    norm_num
    linarith
  have hsplit : expTaylor 26 x = 1 + x * compactPhiTaylor x := by
    unfold expTaylor compactPhiTaylor
    rw [Finset.sum_range_succ', Finset.mul_sum, add_comm (1 : ℝ)]
    congr 1
    · exact Finset.sum_congr rfl fun n _ ↦ by rw [pow_succ', mul_div_assoc]
    · simp
  have hquot : (Real.exp x - 1) / x - compactPhiTaylor x =
      (Real.exp x - expTaylor 26 x) / x := by
    rw [hsplit]
    field_simp [hx]
    ring
  rw [hquot, abs_div]
  calc
    _ ≤ (|x| ^ 26 / ((26 : ℕ).factorial : ℝ) * 2) / |x| :=
      div_le_div_of_nonneg_right (expTaylor_error hratio) (abs_nonneg _)
    _ = _ := by
      rw [show |x| ^ 26 = |x| * |x| ^ 25 from pow_succ' _ _]
      field_simp [(abs_pos.mpr hx).ne']

/-- Uniform absolute error of the exponential quotient polynomial for `0 < |x| ≤ 3/11`. -/
theorem compactPhi_sub_taylor_abs_le {x : ℝ} (hx : 0 < |x|) (hx₁ : |x| ≤ 3 / 11) :
    |(Real.exp x - 1) / x - compactPhiTaylor x| ≤
      2 * (3 / 11 : ℝ) ^ 25 / ((26 : ℕ).factorial : ℝ) :=
  (phiTaylor_error (abs_pos.mp hx) (hx₁.trans (by norm_num))).trans (by gcongr)

/-- The cutoff is `u` times the exponential quotient evaluated at `-h*u`. -/
theorem compactUpperTailGap_sub_taylor_abs_le {p : ℕ} (hp : 11 ≤ p) {u : ℝ}
    (hu : 0 < u) (hu₁ : u ≤ 1) :
    let h : ℝ := 3 / (p : ℝ)
    |upperTailGap h u - u * compactPhiTaylor (-(h * u))| ≤
      u * (2 * (3 / 11 : ℝ) ^ 25 / ((26 : ℕ).factorial : ℝ)) := by
  intro h
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₀ : (0 : ℝ) < p := by linarith
  have hh : 0 < h := div_pos (by norm_num) hp₀
  have hh₁ : h ≤ 3 / 11 := (div_le_iff₀ hp₀).2 (by linarith)
  have harg : 0 < h * u := mul_pos hh hu
  have habs : |-(h * u)| = h * u := by rw [abs_neg, abs_of_pos harg]
  have hbound : |-(h * u)| ≤ 3 / 11 := by
    rw [habs]
    exact (mul_le_of_le_one_right hh.le hu₁).trans hh₁
  have hgap : upperTailGap h u = u * ((Real.exp (-(h * u)) - 1) / (-(h * u))) := by
    unfold upperTailGap
    field_simp [hh.ne', hu.ne']
    ring
  rw [hgap, ← mul_sub, abs_mul, abs_of_pos hu]
  exact mul_le_mul_of_nonneg_left (compactPhi_sub_taylor_abs_le (habs.symm ▸ harg) hbound) hu.le

/-- The degree-24 Taylor polynomial for `sinh x / x`. -/
def compactSinhcTaylor (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 25, if Even n then x ^ n / ((n + 1).factorial : ℝ) else 0

private theorem compactPhiTaylor_average (x : ℝ) :
    (compactPhiTaylor x + compactPhiTaylor (-x)) / 2 = compactSinhcTaylor x := by
  rw [compactPhiTaylor, compactPhiTaylor, compactSinhcTaylor, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  by_cases hn : Even n
  · rw [ite_eq_left hn, hn.neg_pow]
    ring
  · rw [ite_eq_right hn, (Nat.not_even_iff_odd.mp hn).neg_pow, neg_div, add_neg_cancel, zero_div]

/-- Uniform absolute error of the hyperbolic sine quotient polynomial for `0 < x ≤ 3/22`. -/
theorem compactSinhc_sub_taylor_abs_le {x : ℝ} (hx : 0 < x) (hx₁ : x ≤ 3 / 22) :
    |Real.sinh x / x - compactSinhcTaylor x| ≤
      2 * (3 / 22 : ℝ) ^ 25 / ((26 : ℕ).factorial : ℝ) := by
  have habs : |x| ≤ 3 / 22 := by rwa [abs_of_pos hx]
  have hx₁' := habs.trans (show (3 / 22 : ℝ) ≤ 1 by norm_num)
  have hpos := phiTaylor_error hx.ne' hx₁'
  have hneg := phiTaylor_error (neg_ne_zero.mpr hx.ne') (by rwa [abs_neg])
  rw [abs_neg] at hneg
  have haverage : Real.sinh x / x - compactSinhcTaylor x =
      (((Real.exp x - 1) / x - compactPhiTaylor x) +
        ((Real.exp (-x) - 1) / (-x) - compactPhiTaylor (-x))) / 2 := by
    rw [Real.sinh_eq, ← compactPhiTaylor_average, div_neg]
    ring
  rw [haverage]
  let error : ℝ := 2 * |x| ^ 25 / ((26 : ℕ).factorial : ℝ)
  calc
    _ ≤ (error + error) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add hpos hneg)) (by norm_num)
    _ = error := by ring
    _ ≤ _ := by
      dsimp [error]
      gcongr

#print axioms compactExp_sub_taylor_abs_le
#print axioms compactPhi_sub_taylor_abs_le
#print axioms compactUpperTailGap_sub_taylor_abs_le
#print axioms compactSinhc_sub_taylor_abs_le

end

end RefinedBMV.PositiveCenter
