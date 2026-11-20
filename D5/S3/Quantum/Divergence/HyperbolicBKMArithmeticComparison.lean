/- GID: D5/S3/Quantum/Divergence/HyperbolicBKMArithmeticComparison
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/HyperbolicBKMArithmeticComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar comparison of the BKM, geometric, and arithmetic coefficients. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The scalar BKM coefficient comparison used in the `12 Δ` Petz bound. -/

namespace HyperbolicBKMArithmeticComparison

private noncomputable def hyperbolicGap (x : ℝ) : ℝ :=
  2 * Real.sinh x + Real.tanh x - 3 * x

private theorem hasDerivAt_hyperbolicGap (x : ℝ) :
    HasDerivAt hyperbolicGap
      ((Real.cosh x - 1) ^ 2 * (2 * Real.cosh x + 1) / Real.cosh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have ht : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
    have hquot := (Real.hasDerivAt_sinh x).fun_div (Real.hasDerivAt_cosh x) hc
    simpa only [← Real.tanh_eq_sinh_div_cosh, ← pow_two, Real.cosh_sq_sub_sinh_sq]
      using hquot
  have hderiv := (((Real.hasDerivAt_sinh x).const_mul 2).add ht).sub
    (hasDerivAt_const_mul (x := x) (3 : ℝ))
  have hfactor : 2 * Real.cosh x + 1 / Real.cosh x ^ 2 - 3 =
      (Real.cosh x - 1) ^ 2 * (2 * Real.cosh x + 1) / Real.cosh x ^ 2 := by
    field_simp [hc] <;> ring
  rw [← hfactor]
  exact hderiv

/-- The unnormalized hyperbolic inequality on the nonnegative half-line. -/
theorem three_mul_le_two_sinh_add_tanh {x : ℝ} (hx : 0 ≤ x) :
    3 * x ≤ 2 * Real.sinh x + Real.tanh x := by
  have hmonotone : Monotone hyperbolicGap :=
    monotone_of_deriv_nonneg (fun y => (hasDerivAt_hyperbolicGap y).differentiableAt)
      (fun y => by
        rw [(hasDerivAt_hyperbolicGap y).deriv]
        have hfactor : 0 ≤ 2 * Real.cosh y + 1 :=
          add_nonneg (mul_nonneg (by norm_num) (Real.cosh_pos y).le) zero_le_one
        exact div_nonneg (mul_nonneg (sq_nonneg _) hfactor) (sq_nonneg _))
  have hzero : hyperbolicGap 0 = 0 := by simp [hyperbolicGap]
  have hle : hyperbolicGap 0 ≤ hyperbolicGap x := hmonotone hx
  rw [hzero] at hle
  exact sub_nonneg.mp hle

/-- The comparison after normalization by the geometric coefficient. -/
theorem div_sinh_le {x : ℝ} (hx : 0 < x) :
    x / Real.sinh x ≤ (2 + 1 / Real.cosh x) / 3 := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hs).2
  calc
    x * 3 = 3 * x := mul_comm _ _
    _ ≤ 2 * Real.sinh x + Real.tanh x := three_mul_le_two_sinh_add_tanh hx.le
    _ = (2 + 1 / Real.cosh x) * Real.sinh x := by
      simp only [Real.tanh_eq_sinh_div_cosh, div_eq_mul_inv, one_mul]
      ring

private theorem log_divided_difference_le_of_lt {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    (Real.log a - Real.log b) / (a - b) ≤
      (2 * (1 / Real.sqrt (a * b)) + 2 / (a + b)) / 3 := by
  have ha : 0 < a := hb.trans hba
  let x : ℝ := (Real.log a - Real.log b) / 2
  let g : ℝ := Real.sqrt (a * b)
  have hx : 0 < x := div_pos (sub_pos.mpr (Real.log_lt_log hb hba)) (by norm_num)
  have hg : 0 < g := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hg_exp : g = Real.exp ((Real.log a + Real.log b) / 2) := by
    rw [Real.exp_half, Real.exp_add, Real.exp_log ha, Real.exp_log hb]
  have hplus : g * Real.exp x = a := by
    have harg : (Real.log a + Real.log b) / 2 + x = Real.log a := by
      dsimp only [x]
      ring
    rw [hg_exp, ← Real.exp_add, harg, Real.exp_log ha]
  have hminus : g * Real.exp (-x) = b := by
    have harg : (Real.log a + Real.log b) / 2 + (-x) = Real.log b := by
      dsimp only [x]
      ring
    rw [hg_exp, ← Real.exp_add, harg, Real.exp_log hb]
  have hsinh : g * Real.sinh x = (a - b) / 2 := by
    rw [Real.sinh_eq, ← mul_div_assoc, mul_sub, hplus, hminus]
  have hcosh : g * Real.cosh x = (a + b) / 2 := by
    rw [Real.cosh_eq, ← mul_div_assoc, mul_add, hplus, hminus]
  have hbkm : (Real.log a - Real.log b) / (a - b) = (x / Real.sinh x) / g := by
    have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
    rw [div_div]
    apply (div_eq_div_iff (sub_ne_zero.mpr hba.ne') (mul_ne_zero hs.ne' hg.ne')).2
    calc
      (Real.log a - Real.log b) * (Real.sinh x * g) =
          (2 * x) * (g * Real.sinh x) := by
        dsimp only [x]
        ring
      _ = x * (a - b) := by rw [hsinh] <;> ring
  have hsld : (1 / Real.cosh x) / g = 2 / (a + b) := by
    rw [div_div, mul_comm (Real.cosh x) g, hcosh, div_div_eq_mul_div, one_mul]
  rw [hbkm]
  calc
    (x / Real.sinh x) / g ≤ ((2 + 1 / Real.cosh x) / 3) / g :=
      div_le_div_of_nonneg_right (div_sinh_le hx) hg.le
    _ = (2 * (1 / g) + (1 / Real.cosh x) / g) / 3 := by ring
    _ = (2 * (1 / Real.sqrt (a * b)) + 2 / (a + b)) / 3 := by rw [hsld]

/-- The actual logarithmic divided-difference coefficient is bounded by two thirds of
the geometric coefficient and one third of the arithmetic (SLD) coefficient.
At coincident positive arguments all three coefficients equal `1 / a`. -/
theorem bkm_log_divided_difference_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (if a = b then 1 / a else (Real.log a - Real.log b) / (a - b)) ≤
      (2 * (1 / Real.sqrt (a * b)) + 2 / (a + b)) / 3 := by
  rcases lt_trichotomy b a with hba | hba | hab
  · rw [if_neg hba.ne']
    exact log_divided_difference_le_of_lt hb hba
  · subst b
    have hsld : (2 : ℝ) / (a + a) = 1 / a :=
      (div_eq_div_iff (add_pos ha ha).ne' ha.ne').2 (by ring)
    rw [if_pos rfl, Real.sqrt_mul_self ha.le, hsld]
    exact le_of_eq (by ring)
  · rw [if_neg hab.ne]
    calc
      (Real.log a - Real.log b) / (a - b) =
          -(Real.log b - Real.log a) / -(b - a) := by simp only [neg_sub]
      _ = (Real.log b - Real.log a) / (b - a) := neg_div_neg_eq _ _
      _ ≤ (2 * (1 / Real.sqrt (a * b)) + 2 / (a + b)) / 3 := by
        simpa only [mul_comm b a, add_comm b a] using log_divided_difference_le_of_lt ha hab

end HyperbolicBKMArithmeticComparison
