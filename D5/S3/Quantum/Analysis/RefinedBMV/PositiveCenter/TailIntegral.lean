/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/TailIntegral
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exponential integral and divided-difference estimates for the upper-tail remainder. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.UpperTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp

/-! # Uniform derivative bound for the upper-tail divided difference -/

open MeasureTheory Set

namespace RefinedBMV.PositiveCenter

/-- Cancel the square-root sum in the quadratic upper-tail remainder. -/
theorem upperTail_quadratic_rationalization {l₀ l₁ ell x : ℝ}
    (hl₀ : l₀ < 1) (hl₁ : l₁ < 1) (hell : 0 < ell) :
    let b₀ := Real.sqrt (1 - l₀)
    let b₁ := Real.sqrt (1 - l₁)
    ((l₁ - l₀) / ell)^2 / ((b₁ + b₀)^2 * x) = ((b₁ - b₀) / ell)^2 / x := by
  let b₀ := Real.sqrt (1 - l₀)
  let b₁ := Real.sqrt (1 - l₁)
  change ((l₁ - l₀) / ell)^2 / ((b₁ + b₀)^2 * x) = ((b₁ - b₀) / ell)^2 / x
  have hb₀ : 0 < b₀ := Real.sqrt_pos.2 (sub_pos.mpr hl₀)
  have hb₁ : 0 < b₁ := Real.sqrt_pos.2 (sub_pos.mpr hl₁)
  have hprod : -(b₁ - b₀) * (b₁ + b₀) = l₁ - l₀ := by
    have h₀ : b₀ ^ 2 = 1 - l₀ := Real.sq_sqrt (sub_nonneg.mpr hl₀.le)
    have h₁ : b₁ ^ 2 = 1 - l₁ := Real.sq_sqrt (sub_nonneg.mpr hl₁.le)
    nlinarith only [h₀, h₁]
  have hr : ((l₁ - l₀) / ell) / (b₁ + b₀) = (-(b₁ - b₀)) / ell := by
    rw [← hprod]
    field_simp [hell.ne', (add_pos hb₁ hb₀).ne']
  calc
    _ = (((l₁ - l₀) / ell) / (b₁ + b₀))^2 / x := by
      simp only [div_pow, div_div, mul_pow, mul_assoc]
    _ = _ := by rw [hr]; ring

private theorem hasDerivAt_negExp (x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Real.exp (-s)) (-Real.exp (-x)) x := by
  have h : HasDerivAt (fun s : ℝ ↦ -s) (-1) x := HasDerivAt.neg (hasDerivAt_id' x)
  simpa only [mul_neg_one] using h.exp

theorem upperTail_integral_negExp (u : ℝ) :
    (∫ s in (0 : ℝ)..u, Real.exp (-s)) = 1 - Real.exp (-u) := by
  have h (x : ℝ) : HasDerivAt (fun s : ℝ ↦ -Real.exp (-s)) (Real.exp (-x)) x := by
    have hd := HasDerivAt.neg (hasDerivAt_negExp x)
    change HasDerivAt (fun s : ℝ ↦ -Real.exp (-s)) _ x at hd
    simpa only [neg_neg] using hd
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ h x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [neg_zero, Real.exp_zero]
  ring

private theorem integral_negExp_mul_gap (u : ℝ) :
    (∫ s in (0 : ℝ)..u, Real.exp (-s) * (u - s)) = u - 1 + Real.exp (-u) := by
  let F : ℝ → ℝ := fun s ↦ (s + 1 - u) * Real.exp (-s)
  have h (x : ℝ) : HasDerivAt F (Real.exp (-x) * (u - x)) x := by
    have h₀ := (((hasDerivAt_id' x).add_const 1).sub_const u).mul (hasDerivAt_negExp x)
    change HasDerivAt F _ x at h₀
    convert h₀ using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ h x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [F, zero_add, neg_zero, Real.exp_zero]
  ring

private theorem weightedTail_coefficient {u : ℝ} (hu : 0 < u) :
    Real.exp (-u) / (1 - Real.exp (-u)) ^ 2 * (u - 1 + Real.exp (-u)) ≤ 1 / 2 := by
  have he₀ : 0 < 1 - Real.exp (-u) := by
    have he := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    rw [Real.exp_zero] at he
    linarith
  have he₁ : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hs := Real.self_le_sinh_iff.mpr hu.le
  rw [Real.sinh_eq] at hs
  have hh : 2 * u ≤ Real.exp u - Real.exp (-u) := by linarith only [hs]
  have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-u)).le
  rw [sub_mul, he₁] at hm
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos he₀)).mpr
  nlinarith only [hm]

/-- For the tail average of `Q`, a Lipschitz bound on `exp(s) * Q(s)`
gives a derivative bound independent of the lower spectral gap. -/
theorem upperTail_average_derivative {Q : ℝ → ℝ} {u M : ℝ}
    (hu : 0 < u) (hM : 0 ≤ M) (hQ : ContinuousOn Q (uIcc 0 u))
    (hprimitive : HasDerivAt (fun x ↦ ∫ s in (0 : ℝ)..x, Q s) (Q u) u)
    (hlip : ∀ s ∈ Icc 0 u,
      |Real.exp u * Q u - Real.exp s * Q s| ≤ M * (u - s)) :
    |deriv (fun x ↦ (∫ s in (0 : ℝ)..x, Q s) / (1 - Real.exp (-x))) u| ≤ M / 2 := by
  let H : ℝ → ℝ := fun s ↦ Real.exp (-s) * (Real.exp u * Q u - Real.exp s * Q s)
  let e := Real.exp (-u)
  let ell := 1 - e
  have he : 0 < e := Real.exp_pos _
  have hell : 0 < ell := by
    have h := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    rw [Real.exp_zero] at h
    dsimp [ell, e]
    linarith
  have hexp (s : ℝ) : Real.exp (-s) * Real.exp s = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hfun (s : ℝ) : H s = (Real.exp u * Q u) * Real.exp (-s) - Q s := by
    have hcancel : Real.exp (-s) * (Real.exp s * Q s) = Q s := by
      rw [← mul_assoc, hexp s, one_mul]
    dsimp [H]
    rw [mul_sub, hcancel]
    ring
  have hQint : IntervalIntegrable Q volume 0 u := hQ.intervalIntegrable
  have hconst : Continuous (fun s : ℝ ↦ (Real.exp u * Q u) * Real.exp (-s)) := by
    fun_prop
  have hfun' : H = fun s ↦ (Real.exp u * Q u) * Real.exp (-s) - Q s := funext hfun
  have hHcont : ContinuousOn H (uIcc 0 u) := by
    rw [hfun']
    exact hconst.continuousOn.sub hQ
  have hHint : (∫ s in (0 : ℝ)..u, H s) =
      (Real.exp u * Q u) * ell - ∫ s in (0 : ℝ)..u, Q s := by
    rw [hfun', intervalIntegral.integral_sub (hconst.intervalIntegrable _ _) hQint,
      intervalIntegral.integral_const_mul, upperTail_integral_negExp]
  have hnum :
      Q u * ell - (∫ s in (0 : ℝ)..u, Q s) * e =
      e * ∫ s in (0 : ℝ)..u, H s := by
    have hp : e * ((Real.exp u * Q u) * ell) = Q u * ell := calc
      _ = (e * Real.exp u) * (Q u * ell) := by ring
      _ = Q u * ell := by rw [show e * Real.exp u = 1 from hexp u, one_mul]
    rw [hHint, mul_sub e, hp]
    ring
  have hH : |∫ s in (0 : ℝ)..u, H s| ≤ M * (u - 1 + e) := calc
    _ ≤ ∫ s in (0 : ℝ)..u, |H s| :=
      intervalIntegral.abs_integral_le_integral_abs hu.le
    _ ≤ ∫ s in (0 : ℝ)..u, M * (Real.exp (-s) * (u - s)) := by
      apply intervalIntegral.integral_mono_on hu.le hHcont.abs.intervalIntegrable
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      intro s hs
      have hm := mul_le_mul_of_nonneg_left (hlip s hs) (Real.exp_pos (-s)).le
      dsimp [H]
      rw [abs_mul, abs_of_nonneg (Real.exp_pos (-s)).le]
      nlinarith only [hm]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_negExp_mul_gap]
  have hden' : HasDerivAt (fun x ↦ 1 - Real.exp (-x)) e u := by
    have hden := HasDerivAt.sub (hasDerivAt_const u (1 : ℝ)) (hasDerivAt_negExp u)
    change HasDerivAt (fun x ↦ 1 - Real.exp (-x)) _ u at hden
    simpa only [zero_sub, neg_neg, e] using hden
  have hdiv := hprimitive.div hden' (show 1 - Real.exp (-u) ≠ 0 from hell.ne')
  change HasDerivAt (fun x ↦ (∫ s in (0 : ℝ)..x, Q s) / (1 - Real.exp (-x))) _ u at hdiv
  rw [hdiv.deriv]
  change |(Q u * ell - (∫ s in (0 : ℝ)..u, Q s) * e) / ell ^ 2| ≤ M / 2
  rw [hnum, abs_div, abs_mul, abs_of_nonneg he.le, abs_of_nonneg (sq_nonneg ell)]
  have hC : e / ell^2 * (u - 1 + e) ≤ 1/2 := weightedTail_coefficient hu
  have hscale : 0 ≤ e / ell^2 := by positivity
  calc
    _ = (e / ell^2) * |∫ s in (0 : ℝ)..u, H s| := by ring
    _ ≤ (e / ell^2) * (M * (u - 1 + e)) := mul_le_mul_of_nonneg_left hH hscale
    _ = M * (e / ell^2 * (u - 1 + e)) := by ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hC hM
      linarith only [hm]

#print axioms upperTail_average_derivative
#print axioms upperTail_quadratic_rationalization

end RefinedBMV.PositiveCenter
