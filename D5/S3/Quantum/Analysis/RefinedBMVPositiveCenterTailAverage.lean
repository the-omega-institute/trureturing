/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterTailAverage
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform derivative bound for the exponentially weighted tail average. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterUpperTail
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

private theorem integral_negExp (u : ℝ) :
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
      intervalIntegral.integral_const_mul, integral_negExp]
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

/-- The total marginal correction under the quadratic remainder's root. -/
noncomputable def upperTailLambda (h t : ℝ) : ℝ :=
  (1 + (3 + h) * upperTailGap h t) * Real.exp (-((3 + h) * t)) +
    ((3 + h) * (3 + 2*h) / 2) * (upperTailGap h t)^2 * Real.exp (-(2*t))

private theorem hasDerivAt_exp_decay (r t : ℝ) :
    HasDerivAt (fun x ↦ Real.exp (-(r * x))) (-r * Real.exp (-(r * t))) t := by
  have hmul : HasDerivAt (fun x : ℝ ↦ r*x) r t := by
    simpa using (hasDerivAt_id' t).const_mul r
  have hneg : HasDerivAt (fun x : ℝ ↦ -(r*x)) (-r) t := HasDerivAt.neg hmul
  simpa only [mul_comm] using hneg.exp

/-- Factor the derivative of the total marginal correction before taking
the square root. This is the positive integrand for the quadratic tail. -/
theorem hasDerivAt_upperTailLambda {h t : ℝ} (hh : 0 < h) :
    let a := upperTailGap h t
    let j := 1 + h
    let g := 3 + h
    let k := 3 + 2*h
    HasDerivAt (upperTailLambda h)
      (-g*k * Real.exp (-(2*t)) * a * (j*a - 1 + Real.exp (-(j*t)))) t := by
  let a := upperTailGap h
  let j : ℝ := 1 + h
  let g : ℝ := 3 + h
  let k : ℝ := 3 + 2*h
  have ha := hasDerivAt_upperTailGap (h := h) (t := t) hh
  have hm : Real.exp (-(h*t)) = 1 - h*a t := by
    dsimp [a, upperTailGap]
    field_simp [hh.ne']
    ring
  have he : Real.exp (-(g*t)) = Real.exp (-(2*t)) * Real.exp (-(j*t)) := by
    rw [← Real.exp_add]
    dsimp [g, j]
    congr 1
    ring
  have hfirst := ((ha.const_mul g).const_add 1).mul (hasDerivAt_exp_decay g t)
  have hfirst' : HasDerivAt (fun x ↦ (1 + g*a x)*Real.exp (-(g*x)))
      (-g*k*a t*Real.exp (-(g*t))) t := by
    change HasDerivAt (fun x ↦ (1 + g*a x)*Real.exp (-(g*x))) _ t at hfirst
    apply hfirst.congr_deriv
    rw [hm]
    dsimp [k, g]
    ring
  have hsecond := (((ha.pow 2).const_mul (g*k/2)).mul (hasDerivAt_exp_decay 2 t))
  have hsum := HasDerivAt.add hfirst' hsecond
  change HasDerivAt (upperTailLambda h) _ t at hsum
  dsimp only
  apply hsum.congr_deriv
  simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
  rw [hm, he]
  dsimp [k, g, j]
  ring

/-- The factored derivative is nonnegative after changing the sign, and
its magnitude is bounded by `j g k a(t)^2 exp(-2t)`. -/
theorem upperTailLambda_deriv_bounds {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    0 ≤ -deriv (upperTailLambda h) t ∧
    -deriv (upperTailLambda h) t ≤
      (1+h)*(3+h)*(3+2*h) * (upperTailGap h t)^2 * Real.exp (-(2*t)) := by
  let a := upperTailGap h
  let j : ℝ := 1 + h
  let H : ℝ → ℝ := fun x ↦ j*a x - 1 + Real.exp (-(j*x))
  have hj : 0 < j := by dsimp [j]; positivity
  have hD (x : ℝ) : HasDerivAt H
      (j*(Real.exp (-(h*x)) - Real.exp (-(j*x)))) x := by
    have hsum := (((hasDerivAt_upperTailGap (h := h) (t := x) hh).const_mul j).sub_const 1).add
      (hasDerivAt_exp_decay j x)
    change HasDerivAt H _ x at hsum
    apply hsum.congr_deriv
    ring
  have hdiff : Differentiable ℝ H := fun x ↦ (hD x).differentiableAt
  have hmono : MonotoneOn H (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) hdiff.continuous.continuousOn
      hdiff.differentiableOn
    intro x hx
    have hx₀ : 0 ≤ x := mem_Ici.mp (interior_subset hx)
    rw [(hD x).deriv]
    exact mul_nonneg hj.le (sub_nonneg.mpr (Real.exp_le_exp.mpr (by dsimp [j]; nlinarith)))
  have hH₀ : H 0 = 0 := by simp [H, a, upperTailGap]
  have hH : 0 ≤ H t := by
    rw [← hH₀]
    exact hmono self_mem_Ici (mem_Ici.mpr ht) ht
  have hH₁ : H t ≤ j * a t := by
    have he := Real.exp_le_exp.mpr (show -(j*t) ≤ 0 from neg_nonpos.mpr (mul_nonneg hj.le ht))
    rw [Real.exp_zero] at he
    dsimp [H]
    linarith
  have ha₀ : 0 ≤ a t := by
    have he := Real.exp_le_exp.mpr (show -(h*t) ≤ 0 from neg_nonpos.mpr (mul_nonneg hh.le ht))
    rw [Real.exp_zero] at he
    exact div_nonneg (sub_nonneg.mpr he) hh.le
  have hd := (hasDerivAt_upperTailLambda (t := t) hh).deriv
  rw [hd]
  let C := (3+h)*(3+2*h)*Real.exp (-(2*t))*a t
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hl := mul_nonneg hC hH
  have hr := mul_le_mul_of_nonneg_left hH₁ hC
  dsimp [C, H, a, j] at hl hr
  exact ⟨by nlinarith only [hl], by nlinarith only [hr]⟩

/-- An exponential envelope from the exact addition law of the gap,
using only the logarithmic slope at the initial point. -/
theorem upperTail_decay_envelope {h t s : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 11 ≤ t) (hs : 0 ≤ s) :
    (upperTailGap h (t+s))^2 * Real.exp (-(2*(t+s))) ≤
      ((upperTailGap h t)^2 * Real.exp (-(2*t))) * Real.exp (-(20*s/11)) := by
  let a := upperTailGap h
  let L := upperTailSlope h t
  have ht₀ : 0 < t := by linarith
  have ha : 0 < a t :=
    (by norm_num : (0 : ℝ) < 3).trans_le (upperTailGap_ge_three hh hhmax ht)
  have ht' : 11 ≤ t+s := by linarith
  have ha' : 0 ≤ a (t+s) :=
    (by norm_num : (0 : ℝ) ≤ 3).trans (upperTailGap_ge_three hh hhmax ht')
  have hadd : a (t+s) = a t + Real.exp (-(h*t)) * a s := by
    dsimp [a, upperTailGap]
    rw [show -(h*(t+s)) = -(h*t) + -(h*s) by ring, Real.exp_add]
    field_simp [hh.ne']
    ring
  have hExp : Real.exp (-(h*t)) = L * a t := by
    apply (div_eq_iff ha.ne').mp
    rw [← (hasDerivAt_upperTailGap hh).deriv]
    exact upperTailGap_logDeriv hh ht₀
  have hL := (upperTailSlope_bounds hh ht₀).2.1.trans
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 11) ht)
  have htop : a (t+s) ≤ a t * Real.exp (s/11) := calc
    _ = a t + Real.exp (-(h*t)) * a s := hadd
    _ ≤ a t + Real.exp (-(h*t)) * s := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (upperTailGap_le hh) (Real.exp_pos _).le)
    _ = a t*(1+L*s) := by rw [hExp]; ring
    _ ≤ a t * Real.exp (s/11) := by
      apply mul_le_mul_of_nonneg_left _ ha.le
      have hm := mul_le_mul_of_nonneg_right hL hs
      have he := Real.add_one_le_exp (s/11)
      linarith
  have hm := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha' htop 2)
    (Real.exp_pos (-(2*(t+s)))).le
  have heq : (a t * Real.exp (s/11))^2 * Real.exp (-(2*(t+s))) =
      (a t^2 * Real.exp (-(2*t))) * Real.exp (-(20*s/11)) := by
    have he : Real.exp (s/11)^2 * Real.exp (-(2*(t+s))) =
        Real.exp (-(2*t)) * Real.exp (-(20*s/11)) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, mul_assoc, he, ← mul_assoc]
  exact hm.trans_eq heq

/-- The upper-tail radicand is separated from zero as soon as the upper
gap is at least eleven. -/
theorem upperTail_radical_lower {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 11 ≤ t) : 3 / 4 ≤ Real.sqrt (1 - upperTailLambda h t) := by
  let a := upperTailGap h t
  let g : ℝ := 3 + h
  let k : ℝ := 3 + 2 * h
  let c : ℝ := g * k / 2
  let U := a^2 * Real.exp (-(2 * t))
  have ha := upperTailGap_ge_three hh hhmax ht
  change 3 ≤ a at ha
  have ht₀ : 0 ≤ t := by linarith
  have ha₀ : 0 ≤ a := by linarith
  have hc₀ : 9 / 2 ≤ c := by dsimp [c, g, k]; nlinarith [sq_nonneg h]
  have hc₁ : c ≤ 6 := by
    have hmk := mul_le_mul_of_nonneg_left hhmax hh.le
    dsimp [c, g, k]
    nlinarith only [hmk, hhmax]
  have hU₀ : 0 ≤ U := by dsimp [U]; positivity
  have hU₁ : U < 1 / 2000000 := by
    have hbudget : 200*Real.exp (-t) + 10000*U < 1 / 200 := by
      simpa only [U, neg_mul] using upperTail_remainder_budget ht ha₀ (upperTailGap_le hh)
    linarith only [hbudget, Real.exp_pos (-t)]
  have hcoeff : 1 + g * a ≤ (c / 3) * a^2 := by
    have hg : g ≤ 10 / 3 := by dsimp [g]; linarith
    have h₀ := mul_le_mul_of_nonneg_right hg ha₀
    have hs : 3 * a ≤ a^2 := by nlinarith [mul_nonneg ha₀ (sub_nonneg.mpr ha)]
    have hs' : 9 ≤ a^2 := by nlinarith
    have hc : (3 / 2 : ℝ) * a^2 ≤ (c/3) * a^2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg a)
    nlinarith only [h₀, hs, hs', hc]
  have hA : (1 + g*a)*Real.exp (-(g*t)) ≤ (c/3)*U := calc
    _ ≤ (1 + g*a)*Real.exp (-(2*t)) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [g]; positivity)
      apply Real.exp_le_exp.mpr
      dsimp [g]
      nlinarith [mul_nonneg hh.le ht₀]
    _ ≤ ((c/3)*a^2)*Real.exp (-(2*t)) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
    _ = _ := by dsimp [U]; ring
  have hΛ : upperTailLambda h t ≤ (4/3)*c*U := by
    change (1 + g*a)*Real.exp (-(g*t)) + c*a^2*Real.exp (-(2*t)) ≤ _
    rw [show c*a^2*Real.exp (-(2*t)) = c*U from mul_assoc _ _ _]
    linarith only [hA]
  have hbound := mul_le_mul_of_nonneg_right hc₁ hU₀
  apply Real.le_sqrt_of_sq_le
  nlinarith only [hΛ, hbound, hU₁]

/-- Bounds on the rate of decrease of the total marginal correction,
including the two derivatives needed after taking its square root. -/
theorem upperTail_rate_derivatives {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 11 ≤ t) :
    let f : ℝ → ℝ := fun s ↦ -deriv (upperTailLambda h) s
    let x := ((3+h)*(3+2*h)/2)*(upperTailGap h t)^2*Real.exp (-(2*t))
    |deriv f t| ≤ 6*x ∧ |deriv (deriv f) t| ≤ 13*x := by
  let a := upperTailGap h
  let A : ℝ → ℝ := fun s ↦ Real.exp (-(h*s))
  let j : ℝ := 1+h
  let J : ℝ → ℝ := fun s ↦ Real.exp (-(j*s))
  let H : ℝ → ℝ := fun s ↦ j*a s - 1 + J s
  let H₁ : ℝ → ℝ := fun s ↦ j*(A s - J s)
  let H₂ : ℝ → ℝ := fun s ↦ j*(-h*A s + j*J s)
  let F : ℝ → ℝ := fun s ↦ a s*H s
  let F₁ : ℝ → ℝ := fun s ↦ A s*H s + a s*H₁ s
  let F₂ : ℝ → ℝ := fun s ↦ -h*A s*H s + 2*A s*H₁ s + a s*H₂ s
  let c : ℝ := (3+h)*(3+2*h)/2
  let E : ℝ → ℝ := fun s ↦ Real.exp (-(2*s))
  let f : ℝ → ℝ := fun s ↦ -deriv (upperTailLambda h) s
  let f₁ : ℝ → ℝ := fun s ↦ 2*c*E s*(F₁ s - 2*F s)
  let L := upperTailSlope h t
  change |deriv f t| ≤ 6*(c*(a t)^2*E t) ∧
    |deriv (deriv f) t| ≤ 13*(c*(a t)^2*E t)
  have hH₁ (s : ℝ) : HasDerivAt H (H₁ s) s := by
    apply ((((hasDerivAt_upperTailGap (t := s) hh).const_mul j).sub_const 1).add
      (hasDerivAt_exp_decay j s)).congr_deriv
    dsimp [H₁, A, J]
    ring
  have hH₂ (s : ℝ) : HasDerivAt H₁ (H₂ s) s := by
    apply (((hasDerivAt_exp_decay h s).sub (hasDerivAt_exp_decay j s)).const_mul j).congr_deriv
    dsimp [H₂, A, J]
    ring
  have hF₁ (s : ℝ) : HasDerivAt F (F₁ s) s :=
    (hasDerivAt_upperTailGap hh).mul (hH₁ s)
  have hF₂ (s : ℝ) : HasDerivAt F₁ (F₂ s) s := by
    apply (((hasDerivAt_exp_decay h s).mul (hH₁ s)).add
      ((hasDerivAt_upperTailGap hh).mul (hH₂ s))).congr_deriv
    dsimp [F₂, A]
    ring
  have hf (s : ℝ) : f s = 2*c*E s*F s := by
    dsimp only [f]
    rw [(hasDerivAt_upperTailLambda (t := s) hh).deriv]
    dsimp [c, E, F, H, J, j, a]
    ring
  have hD (s : ℝ) : deriv f s = f₁ s := by
    rw [show f = fun r ↦ 2*c*E r*F r from funext hf]
    have hd := ((hasDerivAt_exp_decay 2 s).const_mul (2*c)).mul (hF₁ s)
    change HasDerivAt (fun r ↦ 2*c*E r*F r) _ s at hd
    rw [hd.deriv]
    dsimp [f₁, E]
    ring
  have hD₂ : deriv (deriv f) t = 2*c*E t*(F₂ t - 4*F₁ t + 4*F t) := by
    rw [show deriv f = f₁ from funext hD]
    have hd := ((hasDerivAt_exp_decay 2 t).const_mul (2*c)).mul
      ((hF₂ t).sub ((hF₁ t).const_mul 2))
    change HasDerivAt f₁ _ t at hd
    rw [hd.deriv]
    dsimp [E]
    ring
  have ht₀ : 0 < t := by linarith
  have hapos : 0 < a t := by
    have h := upperTailGap_ge_three hh hhmax ht
    dsimp [a]
    linarith
  have ha := hapos.le
  have hA : 0 ≤ A t := (Real.exp_pos _).le
  have hJ : 0 ≤ J t := (Real.exp_pos _).le
  have hJA : J t ≤ A t := Real.exp_le_exp.mpr (by
    dsimp [j]
    linarith)
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hj' : j ≤ 14/11 := by dsimp [j]; linarith
  have hc : 0 ≤ 2*c*E t := by dsimp [c, E]; positivity
  have hL : 0 ≤ L := (upperTailSlope_bounds hh ht₀).1.le
  have hL' : L ≤ 1/11 := (upperTailSlope_bounds hh ht₀).2.1.trans
    (one_div_le_one_div_of_le (by norm_num) ht)
  have hAl : A t = L*a t := by
    rw [show A t = deriv a t from ((hasDerivAt_upperTailGap hh).deriv).symm]
    exact (div_eq_iff hapos.ne').mp (upperTailGap_logDeriv hh ht₀)
  have hH : 0 ≤ H t := by
    have hneg := (upperTailLambda_deriv_bounds hh ht₀.le).1
    change 0 ≤ f t at hneg
    rw [hf] at hneg
    dsimp only [F] at hneg
    rw [← mul_assoc] at hneg
    have hpos : 0 < 2*c*E t*a t := by dsimp [c, E]; positivity
    exact nonneg_of_mul_nonneg_right hneg hpos
  have hH' : H t ≤ j*a t := by
    have hexp : J t ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hj ht₀.le))
    dsimp only [H]
    linarith
  have h₁ : 0 ≤ H₁ t := mul_nonneg hj (sub_nonneg.mpr hJA)
  have h₁' : H₁ t ≤ j*A t := mul_le_mul_of_nonneg_left (sub_le_self _ hJ) hj
  have h₂ : |H₂ t| ≤ j*(h+j)*A t := by
    calc
      _ ≤ j*(h*A t + j*J t) := by
        dsimp only [H₂]
        rw [abs_mul, abs_of_nonneg hj]
        apply mul_le_mul_of_nonneg_left _ hj
        have hsum := abs_add_le (-h*A t) (j*J t)
        rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hh.le hA),
          abs_of_nonneg (mul_nonneg hj hJ)] at hsum
        simpa only [neg_mul] using hsum
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJA hj) hj
        linarith only [hm]
  have hF : 0 ≤ F t := mul_nonneg ha hH
  have hF' : F t ≤ j*(a t)^2 := by
    have hm := mul_le_mul_of_nonneg_left hH' ha
    dsimp only [F]
    linarith only [hm]
  have hp : 0 ≤ F₁ t := add_nonneg (mul_nonneg hA hH) (mul_nonneg ha h₁)
  have hp' : F₁ t ≤ (2/11)*(j*(a t)^2) := calc
    _ ≤ A t*(j*a t) + a t*(j*A t) := add_le_add
      (mul_le_mul_of_nonneg_left hH' hA) (mul_le_mul_of_nonneg_left h₁' ha)
    _ = (2*L)*(j*(a t)^2) := by rw [hAl]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hL']) (by positivity)
  have hq : |F₂ t| ≤ (2/11)*(j*(a t)^2) := calc
    _ ≤ |-h*A t*H t| + |2*A t*H₁ t| + |a t*H₂ t| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ h*A t*(j*a t) + 2*A t*(j*A t) + a t*(j*(h+j)*A t) := by
      rw [neg_mul, neg_mul, abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg hh.le hA) hH),
        abs_of_nonneg (mul_nonneg (by positivity : 0 ≤ 2*A t) h₁),
        abs_mul, abs_of_nonneg ha]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hH' (mul_nonneg hh.le hA))
        (mul_le_mul_of_nonneg_left h₁' (by positivity)))
        (mul_le_mul_of_nonneg_left h₂ ha)
    _ = ((2*h+j)*L + 2*L^2)*(j*(a t)^2) := by rw [hAl]; ring
    _ ≤ _ := by
      have hk : 2*h+j ≤ 20/11 := by linarith only [hhmax, hj']
      have hm := mul_le_mul hk hL' hL (by norm_num : (0 : ℝ) ≤ 20/11)
      have hs := pow_le_pow_left₀ hL hL' 2
      exact mul_le_mul_of_nonneg_right (by nlinarith only [hm, hs]) (by positivity)
  have hf₁ : |F₁ t - 2*F t| ≤ 2*(j*(a t)^2) :=
    abs_le.mpr ⟨by linarith only [hp, hF'], by nlinarith only [hF, hp', hj, sq_nonneg (a t)]⟩
  have hf₂ : |F₂ t - 4*F₁ t + 4*F t| ≤ (54/11)*(j*(a t)^2) := calc
    _ ≤ |F₂ t| + |-(4*F₁ t)| + |4*F t| := by
      simpa only [sub_eq_add_neg] using
        (abs_add_le (F₂ t + -(4*F₁ t)) (4*F t)).trans
          (add_le_add (abs_add_le (F₂ t) (-(4*F₁ t))) (le_refl |4*F t|))
    _ ≤ _ := by
      rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ 4*F₁ t),
        abs_of_nonneg (by positivity : 0 ≤ 4*F t)]
      linarith only [hq, hp', hF']
  rw [hD, hD₂]
  dsimp only [f₁]
  have habs (y : ℝ) : |(2*c*E t)*y| = (2*c*E t)*|y| := by
    rw [abs_mul, abs_of_nonneg hc]
  simp only [habs]
  have hx : 0 ≤ c*(a t)^2*E t := by dsimp [c, E]; positivity
  constructor
  · calc
      _ ≤ 2*c*E t*(2*(j*(a t)^2)) := mul_le_mul_of_nonneg_left hf₁ hc
      _ = (4*j)*(c*(a t)^2*E t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hj']) hx
  · calc
      _ ≤ 2*c*E t*((54/11)*(j*(a t)^2)) := mul_le_mul_of_nonneg_left hf₂ hc
      _ = ((108/11)*j)*(c*(a t)^2*E t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hj']) hx

/-- The first three derivatives of the square root in the upper-tail remainder. -/
theorem upperTail_radical_derivatives {h t : ℝ} (hh : 0 < h) (hhmax : h ≤ 3 / 11)
    (ht : 11 ≤ t) :
    let b : ℝ → ℝ := fun s ↦ Real.sqrt (1 - upperTailLambda h s)
    let x := ((3+h)*(3+2*h)/2)*(upperTailGap h t)^2*Real.exp (-(2*t))
    |deriv b t| ≤ 2*x ∧ |deriv (deriv b) t| ≤ 5*x ∧
      |deriv (deriv (deriv b)) t| ≤ 10*x := by
  let r : ℝ → ℝ := fun s ↦ 1 - upperTailLambda h s
  let b : ℝ → ℝ := fun s ↦ Real.sqrt (r s)
  let f : ℝ → ℝ := fun s ↦ -deriv (upperTailLambda h) s
  let c : ℝ := (3+h)*(3+2*h)/2
  let a := upperTailGap h t
  let U := a^2*Real.exp (-(2*t))
  let x := c*U
  let q : ℝ := 3/4
  have hbt : q ≤ b t := upperTail_radical_lower hh hhmax ht
  have hqt : 0 < q := by norm_num [q]
  have hbpos : 0 < b t := hqt.trans_le hbt
  have hrt : 0 < r t := Real.sqrt_pos.mp hbpos
  have hΛsmooth : ContDiff ℝ 3 (upperTailLambda h) := by
    unfold upperTailLambda upperTailGap
    fun_prop
  have hfSmooth : ContDiff ℝ 2 f := (hΛsmooth.deriv' (n := 2)).neg
  have hdf (s : ℝ) : HasDerivAt f (deriv f s) s :=
    (hfSmooth.differentiable (by norm_num) s).hasDerivAt
  have hdf' (s : ℝ) : HasDerivAt (deriv f) (deriv (deriv f) s) s :=
    (hfSmooth.differentiable_deriv_two s).hasDerivAt
  have hrcont : Continuous r := continuous_const.sub hΛsmooth.continuous
  have hnear {s : ℝ} (hs : 0 < r s) : ∀ᶠ y in nhds s, 0 < r y :=
    hrcont.continuousAt.eventually (Ioi_mem_nhds hs)
  have hb₁ {s : ℝ} (hs : 0 < r s) : HasDerivAt b (f s / (2*b s)) s := by
    have hd : HasDerivAt (upperTailLambda h) (deriv (upperTailLambda h) s) s :=
      (hasDerivAt_upperTailLambda hh).differentiableAt.hasDerivAt
    simpa only [zero_sub, r, b, f] using
      ((hasDerivAt_const s (1 : ℝ)).fun_sub hd).sqrt hs.ne'
  have hb₂ {s : ℝ} (hs : 0 < r s) :
      HasDerivAt (deriv b)
        (deriv f s / (2*b s) - (f s)^2 / (4*(b s)^3)) s := by
    have hbne := (Real.sqrt_pos.mpr hs).ne'
    have hlocal : deriv b =ᶠ[nhds s] fun y ↦ f y / (2*b y) :=
      (hnear hs).mono fun _ hy ↦ (hb₁ hy).deriv
    have hquot := (hdf s).fun_div ((hb₁ hs).const_mul 2) (mul_ne_zero two_ne_zero hbne)
    refine (hquot.congr_of_eventuallyEq hlocal).congr_deriv ?_
    field_simp [hbne]
    ring
  have hb₃ :
      deriv (deriv (deriv b)) t = deriv (deriv f) t / (2*b t)
        - 3*f t*deriv f t / (4*(b t)^3) + 3*(f t)^3 / (8*(b t)^5) := by
    have hlocal : deriv (deriv b) =ᶠ[nhds t]
        fun y ↦ deriv f y / (2*b y) - (f y)^2 / (4*(b y)^3) :=
      (hnear hrt).mono fun _ hy ↦ (hb₂ hy).deriv
    have hbne := hbpos.ne'
    have hfirst := (hdf' t).fun_div ((hb₁ hrt).const_mul 2) (mul_ne_zero two_ne_zero hbne)
    have hsecond := ((hdf t).pow 2).fun_div (((hb₁ hrt).pow 3).const_mul 4)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hbne))
    have hresult := ((hfirst.sub hsecond).congr_of_eventuallyEq hlocal).deriv
    simp only [Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat] at hresult
    rw [hresult]
    field_simp [hbne]
    ring
  have ha : 0 ≤ a := by
    have h := upperTailGap_ge_three hh hhmax ht
    dsimp [a]
    linarith
  have hc₀ : 0 ≤ c := by dsimp [c]; positivity
  have hc₁ : c ≤ 6 := by
    have hm := mul_le_mul_of_nonneg_left hhmax hh.le
    dsimp [c]
    nlinarith only [hm, hhmax]
  have hU₀ : 0 ≤ U := by dsimp [U]; positivity
  have hx₀ : 0 ≤ x := mul_nonneg hc₀ hU₀
  have hx₁ : x ≤ 3/200 := by
    have hbudget : 200*Real.exp (-t) + 10000*U < 1 / 200 := by
      simpa only [U, neg_mul] using upperTail_remainder_budget ht ha (upperTailGap_le hh)
    have h := mul_le_mul_of_nonneg_right hc₁ hU₀
    change c*U ≤ 3/200
    linarith only [h, hbudget, Real.exp_pos (-t)]
  have hfx : |f t| ≤ 3*x := by
    obtain ⟨hf₀, hf₁⟩ := upperTailLambda_deriv_bounds hh (by linarith : 0 ≤ t)
    change 0 ≤ f t at hf₀
    have hf₁' : f t ≤ (2*(1+h))*x := by
      dsimp [x, U, c, a]
      nlinarith only [hf₁]
    rw [abs_of_nonneg hf₀]
    exact hf₁'.trans (mul_le_mul_of_nonneg_right (by linarith only [hhmax]) hx₀)
  have hxform : ((3+h)*(3+2*h)/2)*(upperTailGap h t)^2*Real.exp (-(2*t)) = x := by
    dsimp [x, c, U, a]
    ring
  obtain ⟨hf₁, hf₂⟩ := upperTail_rate_derivatives hh hhmax ht
  change |deriv f t| ≤ _ at hf₁
  change |deriv (deriv f) t| ≤ _ at hf₂
  rw [hxform] at hf₁ hf₂
  have hdiv {k num B : ℝ} (hk : 0 < k) (n : ℕ) (hn : |num| ≤ B) :
      |num / (k*(b t)^n)| ≤ B / (k*q^n) := calc
    _ = |num| / (k*(b t)^n) := by
      rw [abs_div, abs_of_pos (mul_pos hk (pow_pos hbpos n))]
    _ ≤ |num| / (k*q^n) := by
      apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hqt.le hbt _) hk.le
    _ ≤ _ := div_le_div_of_nonneg_right hn (by positivity)
  have hp₂ : |(f t)^2| ≤ (3*x)^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hfx _
  have hp₃ : |3*(f t)^3| ≤ 3*(3*x)^3 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hfx _) (by norm_num)
  have hm : |3*f t*deriv f t| ≤ 3*(3*x)*(6*x) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hfx (by norm_num)) hf₁ (abs_nonneg _)
      (by positivity)
  dsimp only
  rw [hxform]
  change |deriv b t| ≤ 2*x ∧ |deriv (deriv b) t| ≤ 5*x ∧
    |deriv (deriv (deriv b)) t| ≤ 10*x
  refine ⟨?_, ?_, ?_⟩
  · rw [(hb₁ hrt).deriv]
    have h := hdiv (by norm_num : (0 : ℝ) < 2) 1 hfx
    simp only [pow_one, q] at h
    exact h.trans_eq (by ring)
  · rw [(hb₂ hrt).deriv]
    have h : |deriv f t / (2*b t) - (f t)^2 / (4*(b t)^3)| ≤
        |deriv f t / (2*b t)| + |(f t)^2 / (4*(b t)^3)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (deriv f t / (2*b t)) (-((f t)^2 / (4*(b t)^3)))
    have h₁ := hdiv (by norm_num : (0 : ℝ) < 2) 1 hf₁
    have h₂ := hdiv (by norm_num : (0 : ℝ) < 4) 3 hp₂
    have hsq := mul_le_mul_of_nonneg_left hx₁ hx₀
    dsimp [q] at h₁ h₂
    simp only [pow_one] at h₁
    have h₁' : |deriv f t / (2*b t)| ≤ 4*x := h₁.trans_eq (by ring)
    have h₂' : |(f t)^2 / (4*(b t)^3)| ≤ (16/3)*x^2 := h₂.trans_eq (by ring)
    nlinarith only [h, h₁', h₂', hsq, hx₀]
  · rw [hb₃]
    have h := abs_add_le
      (deriv (deriv f) t / (2*b t) - 3*f t*deriv f t / (4*(b t)^3))
      (3*(f t)^3 / (8*(b t)^5))
    have habs : |deriv (deriv f) t / (2*b t) - 3*f t*deriv f t / (4*(b t)^3)| ≤
        |deriv (deriv f) t / (2*b t)| + |3*f t*deriv f t / (4*(b t)^3)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
        (deriv (deriv f) t / (2*b t)) (-(3*f t*deriv f t / (4*(b t)^3)))
    have h₁ := hdiv (by norm_num : (0 : ℝ) < 2) 1 hf₂
    have h₂ := hdiv (by norm_num : (0 : ℝ) < 4) 3 hm
    have h₃ := hdiv (by norm_num : (0 : ℝ) < 8) 5 hp₃
    have hsq := mul_le_mul_of_nonneg_left hx₁ hx₀
    have hcu := mul_le_mul_of_nonneg_left hx₁ (sq_nonneg x)
    dsimp [q] at h₁ h₂ h₃
    simp only [pow_one] at h₁
    have h₁' : |deriv (deriv f) t / (2*b t)| ≤ (26/3)*x := h₁.trans_eq (by ring)
    have h₂' : |3*f t*deriv f t / (4*(b t)^3)| ≤ 32*x^2 := h₂.trans_eq (by ring)
    have h₃' : |3*(f t)^3 / (8*(b t)^5)| ≤ (128/3)*x^3 := h₃.trans_eq (by ring)
    nlinarith only [h, habs, h₁', h₂', h₃', hsq, hcu, hx₀]

private theorem upperTail_integral_bound {Q : ℝ → ℝ} {u A : ℝ} (hu : 0 ≤ u)
    (hQ : ContinuousOn Q (uIcc 0 u)) (hQ₀ : ∀ s ∈ Icc 0 u, |Q s| ≤ A * Real.exp (-s)) :
    |∫ s in (0 : ℝ)..u, Q s| ≤ A*(1 - Real.exp (-u)) := calc
  _ ≤ ∫ s in (0 : ℝ)..u, |Q s| :=
    intervalIntegral.abs_integral_le_integral_abs hu
  _ ≤ ∫ s in (0 : ℝ)..u, A*Real.exp (-s) := by
    apply intervalIntegral.integral_mono_on hu hQ.abs.intervalIntegrable
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    exact hQ₀
  _ = _ := by rw [intervalIntegral.integral_const_mul, integral_negExp]

/-- An exponentially decaying derivative controls a divided difference and
its derivative, uniformly as the increment tends to zero. -/
private theorem upperTail_dividedDifference_bound {F Q Q₁ : ℝ → ℝ} {u A B : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∀ s, 0 ≤ s → HasDerivAt F (Q s) s)
    (hQ : ∀ s, 0 ≤ s → HasDerivAt Q (Q₁ s) s)
    (hQ₀ : ∀ s, 0 ≤ s → |Q s| ≤ A * Real.exp (-s))
    (hQ₁ : ∀ s, 0 ≤ s → |Q₁ s| ≤ B * Real.exp (-s)) :
    |(F u - F 0)/(1 - Real.exp (-u))| ≤ A ∧
      |deriv (fun s ↦ (F s - F 0)/(1 - Real.exp (-s))) u| ≤ (A+B)/2 := by
  have hell : 0 < 1 - Real.exp (-u) := by
    apply sub_pos.mpr
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hQc {s : ℝ} (hs : 0 ≤ s) : ContinuousOn Q (uIcc 0 s) := by
    rw [uIcc_of_le hs]
    exact fun t ht ↦ (hQ t ht.1).continuousAt.continuousWithinAt
  have hFTC (s : ℝ) (hs : 0 ≤ s) : (∫ t in (0 : ℝ)..s, Q t) = F s - F 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_)
      (hQc hs).intervalIntegrable
    rw [uIcc_of_le hs] at ht
    exact hF t ht.1
  have hb := upperTail_integral_bound hu.le (hQc hu.le) (fun s hs ↦ hQ₀ s hs.1)
  have hZ (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt (fun y ↦ Real.exp y * Q y) (Real.exp s * (Q s + Q₁ s)) s := by
    apply ((Real.hasDerivAt_exp s).mul (hQ s hs)).congr_deriv
    ring
  have hZbound (s : ℝ) (hs : 0 ≤ s) :
      ‖deriv (fun y ↦ Real.exp y * Q y) s‖ ≤ A+B := by
    rw [(hZ s hs).deriv, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos s)]
    calc
      _ ≤ Real.exp s * (A*Real.exp (-s) + B*Real.exp (-s)) := by
        refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (Real.exp_pos s).le
        exact add_le_add (hQ₀ s hs) (hQ₁ s hs)
      _ = _ := by
        rw [← add_mul, ← mul_assoc, mul_comm (Real.exp s) (A+B), mul_assoc,
          ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hlip (s : ℝ) (hs : s ∈ Icc 0 u) :
      |Real.exp u * Q u - Real.exp s * Q s| ≤ (A+B)*(u-s) := by
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t (ht : t ∈ Icc 0 u) ↦ (hZ t ht.1).differentiableAt)
      (fun t ht ↦ hZbound t ht.1) (convex_Icc 0 u) hs ⟨hu.le, le_rfl⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs.2)] using hm
  have hlocal : (fun s ↦ ∫ t in (0 : ℝ)..s, Q t) =ᶠ[nhds u] fun s ↦ F s - F 0 :=
    (eventually_gt_nhds hu).mono fun s hs ↦ hFTC s hs.le
  have hprimitive := ((hF u hu.le).sub_const (F 0)).congr_of_eventuallyEq hlocal
  have hquot : (fun s ↦ (∫ t in (0 : ℝ)..s, Q t)/(1 - Real.exp (-s))) =ᶠ[nhds u]
      fun s ↦ (F s - F 0)/(1 - Real.exp (-s)) :=
    hlocal.mono fun s hs ↦ congrArg (fun y ↦ y/(1 - Real.exp (-s))) hs
  have ha := upperTail_average_derivative hu (add_nonneg hA hB) (hQc hu.le) hprimitive hlip
  rw [hquot.deriv_eq] at ha
  refine ⟨?_, ha⟩
  rw [← hFTC u hu.le, abs_div, abs_of_pos hell]
  exact (div_le_iff₀ hell).mpr hb

/-- The root divided difference used in the rationalized quadratic tail. -/
noncomputable def upperTailRootDifference (h u d : ℝ) : ℝ :=
  (Real.sqrt (1 - upperTailLambda h (d+u)) - Real.sqrt (1 - upperTailLambda h d)) /
    (1 - Real.exp (-u))

theorem upperTail_rootDifference_bounds {h u d : ℝ} (hh : 0 < h) (hhmax : h ≤ 3/11)
    (hu : 0 < u) (hd : 11 ≤ d) :
    let T := upperTailRootDifference h
    let x := ((3+h)*(3+2*h)/2)*(upperTailGap h d)^2*Real.exp (-(2*d))
    |T u d| ≤ 2*x ∧
    |deriv (fun s ↦ T s d) u| ≤ 4*x ∧
    |deriv (T u) d| ≤ 5*x ∧
    |deriv (fun s ↦ deriv (T s) d) u| ≤ 8*x ∧
    |deriv (deriv (T u)) d| ≤ 10*x ∧
    ContDiffAt ℝ 2 (T u) d ∧ DifferentiableAt ℝ (fun s ↦ T s d) u ∧
    DifferentiableAt ℝ (fun s ↦ deriv (T s) d) u := by
  let r : ℝ → ℝ := fun s ↦ 1 - upperTailLambda h s
  let b : ℝ → ℝ := fun s ↦ Real.sqrt (r s)
  let b₁ := deriv b
  let b₂ := deriv b₁
  let b₃ := deriv b₂
  let ell : ℝ → ℝ := fun s ↦ 1 - Real.exp (-s)
  let T₁ : ℝ → ℝ → ℝ := fun s t ↦ (b₁ (t+s) - b₁ t) / ell s
  let T₂ : ℝ → ℝ → ℝ := fun s t ↦ (b₂ (t+s) - b₂ t) / ell s
  let c : ℝ := (3+h)*(3+2*h)/2
  let X : ℝ → ℝ := fun t ↦ c*(upperTailGap h t)^2*Real.exp (-(2*t))
  let x := X d
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hx : 0 ≤ x := by dsimp [x, X]; positivity
  have hr (t : ℝ) (ht : 11 ≤ t) : 0 < r t :=
    Real.sqrt_pos.mp ((by norm_num : (0 : ℝ) < 3/4).trans_le
      (upperTail_radical_lower hh hhmax ht))
  have hR : ContDiff ℝ 3 r := by
    unfold r upperTailLambda upperTailGap
    fun_prop
  have hB {t : ℝ} (ht : 0 < r t) : ContDiffAt ℝ 3 b t :=
    hR.contDiffAt.sqrt ht.ne'
  have hB₁ {t : ℝ} (ht : 0 < r t) : ContDiffAt ℝ 2 b₁ t :=
    (hB ht).derivWithin (by norm_num)
  have hB₂ {t : ℝ} (ht : 0 < r t) : ContDiffAt ℝ 1 b₂ t :=
    (hB₁ ht).derivWithin (by norm_num)
  have hb {t : ℝ} (ht : 0 < r t) : HasDerivAt b (b₁ t) t :=
    ((hB ht).differentiableAt (by norm_num)).hasDerivAt
  have hb₁ {t : ℝ} (ht : 0 < r t) : HasDerivAt b₁ (b₂ t) t :=
    ((hB₁ ht).differentiableAt (by norm_num)).hasDerivAt
  have hb₂ {t : ℝ} (ht : 0 < r t) : HasDerivAt b₂ (b₃ t) t :=
    ((hB₂ ht).differentiableAt (by norm_num)).hasDerivAt
  have hshift {F : ℝ → ℝ} {y z D : ℝ} (hf : HasDerivAt F D (z+y)) :
      HasDerivAt (fun s ↦ F (z+s)) D y := by
    have hd := hf.comp y ((hasDerivAt_id' y).const_add z)
    change HasDerivAt (fun s ↦ F (z+s)) (D*1) y at hd
    simpa only [mul_one] using hd
  have hshift' {F : ℝ → ℝ} {y z D : ℝ} (hf : HasDerivAt F D (y+z)) :
      HasDerivAt (fun s ↦ F (s+z)) D y := by
    have hd := hf.comp y ((hasDerivAt_id' y).add_const z)
    change HasDerivAt (fun s ↦ F (s+z)) (D*1) y at hd
    simpa only [mul_one] using hd
  have hD₁ {s t : ℝ} (ht : 0 < r t) (hst : 0 < r (t+s)) :
      HasDerivAt (upperTailRootDifference h s) (T₁ s t) t :=
    ((hshift' (hb hst)).fun_sub (hb ht)).div_const (ell s)
  have hD₂ {s t : ℝ} (ht : 0 < r t) (hst : 0 < r (t+s)) :
      HasDerivAt (T₁ s) (T₂ s t) t := by
    have h := ((hshift' (hb₁ hst)).fun_sub (hb₁ ht)).div_const (ell s)
    exact h
  have hX (s : ℝ) (hs : 0 ≤ s) : X (d+s) ≤ x*Real.exp (-s) := calc
    _ ≤ x*Real.exp (-(20*s/11)) := by
      have hm := mul_le_mul_of_nonneg_left (upperTail_decay_envelope hh hhmax hd hs) hc
      dsimp [X, x]
      nlinarith only [hm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hx
  have henv (s : ℝ) (hs : 0 ≤ s) :
      |b₁ (d+s)| ≤ (2*x)*Real.exp (-s) ∧
      |b₂ (d+s)| ≤ (5*x)*Real.exp (-s) ∧
      |b₃ (d+s)| ≤ (10*x)*Real.exp (-s) := by
    obtain ⟨ha, hb, hc⟩ := upperTail_radical_derivatives hh hhmax (show 11 ≤ d+s by linarith)
    have hscale {k : ℝ} (hk : 0 ≤ k) :
        k*X (d+s) ≤ (k*x)*Real.exp (-s) :=
      (mul_le_mul_of_nonneg_left (hX s hs) hk).trans_eq (mul_assoc _ _ _).symm
    exact ⟨ha.trans (hscale (by norm_num)), hb.trans (hscale (by norm_num)),
      hc.trans (hscale (by norm_num))⟩
  have hr' (s : ℝ) (hs : 0 ≤ s) : 0 < r (d+s) := hr _ (by linarith)
  obtain ⟨hT, hTu⟩ := upperTail_dividedDifference_bound hu
    (show 0 ≤ 2*x by positivity) (show 0 ≤ 5*x by positivity)
    (fun s hs ↦ hshift (hb (hr' s hs))) (fun s hs ↦ hshift (hb₁ (hr' s hs)))
    (fun s hs ↦ (henv s hs).1) (fun s hs ↦ (henv s hs).2.1)
  obtain ⟨hTd, hTud⟩ := upperTail_dividedDifference_bound hu
    (show 0 ≤ 5*x by positivity) (show 0 ≤ 10*x by positivity)
    (fun s hs ↦ hshift (hb₁ (hr' s hs))) (fun s hs ↦ hshift (hb₂ (hr' s hs)))
    (fun s hs ↦ (henv s hs).2.1) (fun s hs ↦ (henv s hs).2.2)
  have hdLocal : (fun s ↦ deriv (upperTailRootDifference h s) d) =ᶠ[nhds u] fun s ↦ T₁ s d :=
    (eventually_gt_nhds hu).mono fun s hs ↦ (hD₁ (hr _ hd) (hr' s hs.le)).deriv
  have hddLocal : deriv (upperTailRootDifference h u) =ᶠ[nhds d] T₁ u := by
    have h₀ : ∀ᶠ s in nhds d, 0 < r s :=
      hR.continuous.continuousAt.eventually (Ioi_mem_nhds (hr _ hd))
    have h₁ : ∀ᶠ s in nhds d, 0 < r (s+u) :=
      (hR.continuous.comp (continuous_id.add continuous_const)).continuousAt.eventually
      (Ioi_mem_nhds (hr' u hu.le))
    filter_upwards [h₀, h₁] with s hs hsu
    exact (hD₁ hs hsu).deriv
  let Q : ℝ → ℝ := fun s ↦ b₃ (d+s)
  have hQc : ContinuousOn Q (uIcc 0 u) := by
    rw [uIcc_of_le hu.le]
    intro s hs
    have hsmooth : ContDiffAt ℝ 0 b₃ (d+s) := (hB₂ (hr' s hs.1)).derivWithin (by norm_num)
    exact (hsmooth.continuousAt.comp (continuousAt_const.add continuousAt_id)).continuousWithinAt
  have hInt : (∫ s in (0 : ℝ)..u, Q s) = b₂ (d+u) - b₂ d := by
    simpa only [add_zero] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs ↦
        hshift (hb₂ (hr' s (by rw [uIcc_of_le hu.le] at hs; exact hs.1))))
        hQc.intervalIntegrable)
  have hell : 0 < ell u := by
    apply sub_pos.mpr
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hTdd : |T₂ u d| ≤ 10*x := by
    change |(b₂ (d+u) - b₂ d)/ell u| ≤ _
    rw [← hInt, abs_div, abs_of_pos hell]
    exact (div_le_iff₀ hell).mpr
      (upperTail_integral_bound hu.le hQc (fun s hs ↦ (henv s hs.1).2.2))
  have hTb : ContDiffAt ℝ 2 (fun t ↦ b (t+u)) d := by
    have hshift : ContDiffAt ℝ 2 (fun t : ℝ ↦ t+u) d := by fun_prop
    have hr₂ : ContDiff ℝ 2 r := hR.of_le (by norm_num)
    have hrshift : ContDiffAt ℝ 2 (fun t ↦ r (t+u)) d :=
      hr₂.contDiffAt.comp d hshift
    exact hrshift.sqrt (hr' u hu.le).ne'
  have hT_smooth : ContDiffAt ℝ 2 (upperTailRootDifference h u) d :=
    (hTb.sub ((hB (hr d hd)).of_le (by norm_num))).div contDiffAt_const hell.ne'
  have hEll : DifferentiableAt ℝ ell u := by dsimp [ell]; fun_prop
  have hTu_diff : DifferentiableAt ℝ (fun s ↦ upperTailRootDifference h s d) u :=
    (((hshift (hb (hr' u hu.le))).sub_const (b d)).differentiableAt.fun_div hEll hell.ne')
  have hTd_diff : DifferentiableAt ℝ (fun s ↦ deriv (upperTailRootDifference h s) d) u :=
    ((((hshift (hb₁ (hr' u hu.le))).sub_const (b₁ d)).differentiableAt.fun_div hEll
      hell.ne')).congr_of_eventuallyEq hdLocal
  dsimp only
  change |upperTailRootDifference h u d| ≤ 2*x ∧
    |deriv (fun s ↦ upperTailRootDifference h s d) u| ≤ 4*x ∧
    |deriv (upperTailRootDifference h u) d| ≤ 5*x ∧
    |deriv (fun s ↦ deriv (upperTailRootDifference h s) d) u| ≤ 8*x ∧
    |deriv (deriv (upperTailRootDifference h u)) d| ≤ 10*x ∧
    ContDiffAt ℝ 2 (upperTailRootDifference h u) d ∧
    DifferentiableAt ℝ (fun s ↦ upperTailRootDifference h s d) u ∧
    DifferentiableAt ℝ (fun s ↦ deriv (upperTailRootDifference h s) d) u
  rw [(hD₁ (hr _ hd) (hr' u hu.le)).deriv, hdLocal.deriv_eq, hddLocal.deriv_eq,
    (hD₂ (hr _ hd) (hr' u hu.le)).deriv]
  simp only [add_zero] at hT hTu hTd hTud
  exact ⟨hT, hTu.trans (by linarith only [hx]), hTd, hTud.trans (by linarith only [hx]), hTdd,
    hT_smooth, hTu_diff, hTd_diff⟩

/-- The reciprocal scale loses factors of at most two and five under its
first two derivatives in the upper gap. -/
theorem upperTail_inverseScale_bounds {h c d : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hd : 11 ≤ d) :
    let X : ℝ → ℝ := fun t ↦ c * (upperTailGap h t)^2 * Real.exp (-(2*t))
    let R : ℝ → ℝ := fun t ↦ (X t)⁻¹
    0 < R d ∧ |deriv R d| ≤ 2*R d ∧ |deriv (deriv R) d| ≤ 5*R d := by
  let a := upperTailGap h
  let L := upperTailSlope h
  let X : ℝ → ℝ := fun t ↦ c * (a t)^2 * Real.exp (-(2*t))
  let R : ℝ → ℝ := fun t ↦ (X t)⁻¹
  let s : ℝ → ℝ := fun t ↦ 2*L t - 2
  have ha {t : ℝ} (ht : 0 < t) : 0 < a t := by
    have h := Real.exp_lt_exp.mpr (neg_lt_zero.mpr (mul_pos hh ht))
    rw [Real.exp_zero] at h
    exact div_pos (sub_pos.mpr h) hh
  have hx {t : ℝ} (ht : 0 < t) : 0 < X t :=
    mul_pos (mul_pos hc (sq_pos_of_pos (ha ht))) (Real.exp_pos _)
  have hX {t : ℝ} (ht : 0 < t) : HasDerivAt X (s t*X t) t := by
    have hda := hasDerivAt_upperTailGap (t := t) hh
    have hlog : Real.exp (-(h*t)) = L t*a t := by
      rw [← hda.deriv]
      exact (div_eq_iff (ha ht).ne').mp (upperTailGap_logDeriv hh ht)
    have hD := ((hda.pow 2).const_mul c).mul (hasDerivAt_exp_decay 2 t)
    change HasDerivAt X _ t at hD
    refine hD.congr_deriv ?_
    simp only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat, hlog, X, s]
    ring
  have hR {t : ℝ} (ht : 0 < t) : HasDerivAt R (-(s t)*R t) t := by
    have h := (hX ht).inv (hx ht).ne'
    refine h.congr_deriv ?_
    change -(s t*X t)/(X t)^2 = -(s t)*(X t)⁻¹
    field_simp [(hx ht).ne']
  have hd₀ : 0 < d := by linarith
  have hR' : deriv R =ᶠ[nhds d] fun t ↦ -(s t)*R t :=
    (eventually_gt_nhds hd₀).mono fun _ ht ↦ (hR ht).deriv
  have hs : HasDerivAt (fun t ↦ -(s t)) (-(2*deriv L d)) d := by
    have hL : HasDerivAt L (deriv L d) d :=
      (hasDerivAt_upperTailSlope hh hd₀).differentiableAt.hasDerivAt
    exact (((hL.const_mul 2).sub_const 2).neg)
  have hR₂ : deriv (deriv R) d = ((s d)^2 - 2*deriv L d)*R d := by
    have h := ((hs.mul (hR hd₀)).congr_of_eventuallyEq hR').deriv
    rw [h]
    ring
  obtain ⟨hL₀, hL₁, hL'₀, hL'₁, _, _⟩ := upperTailSlope_bounds hh hd₀
  have hLmax : L d ≤ 1/11 := hL₁.trans (one_div_le_one_div_of_le (by norm_num) hd)
  have hL'max : -deriv L d ≤ 1/121 := hL'₁.trans (by
    apply one_div_le_one_div_of_le (by norm_num)
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11) hd 2
    norm_num at h
    exact h)
  have hRpos : 0 < R d := inv_pos.mpr (hx hd₀)
  have hsb : |s d| ≤ 2 := by
    dsimp [s]
    exact abs_le.mpr ⟨by linarith only [hL₀], by linarith only [hLmax]⟩
  have hsq : (s d)^2 ≤ 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hsb 2
    simpa only [sq_abs, show (2 : ℝ)^2 = 4 by norm_num] using h
  have hfactor : 0 ≤ (s d)^2 - 2*deriv L d := by
    linarith only [sq_nonneg (s d), hL'₀]
  have hfactor' : (s d)^2 - 2*deriv L d ≤ 5 := by
    linarith only [hsq, hL'max]
  change 0 < R d ∧ |deriv R d| ≤ 2*R d ∧ |deriv (deriv R) d| ≤ 5*R d
  rw [(hR hd₀).deriv, hR₂, abs_mul, abs_neg, abs_of_pos hRpos]
  refine ⟨hRpos, mul_le_mul_of_nonneg_right hsb hRpos.le, ?_⟩
  rw [abs_of_nonneg (mul_nonneg hfactor hRpos.le)]
  exact mul_le_mul_of_nonneg_right hfactor' hRpos.le

/-- The quadratic error after cancelling the sum of the two square roots. -/
noncomputable def upperTailQuadratic (h u d : ℝ) : ℝ :=
  (upperTailRootDifference h u d)^2 *
    (((3+h)*(3+2*h)/2)*(upperTailGap h d)^2*Real.exp (-(2*d)))⁻¹

theorem upperTail_quadratic_bounds {h u d : ℝ} (hh : 0 < h) (hhmax : h ≤ 3/11)
    (hu : 0 < u) (hd : 11 ≤ d) :
    let N := upperTailQuadratic h
    let x := ((3+h)*(3+2*h)/2)*(upperTailGap h d)^2*Real.exp (-(2*d))
    |N u d| ≤ 4*x ∧ |deriv (fun s ↦ N s d) u| ≤ 16*x ∧
      |deriv (N u) d| ≤ 28*x ∧ |deriv (fun s ↦ deriv (N s) d) u| ≤ 104*x ∧
      |deriv (deriv (N u)) d| ≤ 190*x := by
  let T := upperTailRootDifference h
  let c : ℝ := (3+h)*(3+2*h)/2
  let X : ℝ → ℝ := fun t ↦ c*(upperTailGap h t)^2*Real.exp (-(2*t))
  let R : ℝ → ℝ := fun t ↦ (X t)⁻¹
  let x := X d
  let N := upperTailQuadratic h
  let a := T u d
  let U := deriv (fun s ↦ T s d) u
  let D := deriv (T u) d
  let M := deriv (fun s ↦ deriv (T s) d) u
  let DD := deriv (deriv (T u)) d
  let r := R d
  let dr := deriv R d
  let ddr := deriv (deriv R) d
  have hc : 0 < c := by dsimp [c]; positivity
  have hx : 0 < x := by
    have ha := upperTailGap_ge_three hh hhmax hd
    exact mul_pos (mul_pos hc (sq_pos_of_pos (by linarith only [ha]))) (Real.exp_pos _)
  have hxr : x*r = 1 := mul_inv_cancel₀ hx.ne'
  have hX : ContDiff ℝ 2 X := by unfold X upperTailGap; fun_prop
  have hRs : ContDiffAt ℝ 2 R d := hX.contDiffAt.inv hx.ne'
  obtain ⟨_, hr₁, hr₂⟩ := upperTail_inverseScale_bounds hh hc hd
  obtain ⟨ha, hu₁, hd₁, hm, hdd, hTs, hTu, hTdu⟩ :=
    upperTail_rootDifference_bounds hh hhmax hu hd
  have hN_d {s t : ℝ} (hT : DifferentiableAt ℝ (T s) t) (hR : DifferentiableAt ℝ R t) :
      HasDerivAt (N s)
        (2*T s t*deriv (T s) t*R t + (T s t)^2*deriv R t) t := by
    have h := ((hT.hasDerivAt.pow 2).mul hR.hasDerivAt)
    change HasDerivAt (N s) _ t at h
    exact h.congr_deriv (by simp only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat])
  have hNdu : deriv (fun s ↦ N s d) u = 2*a*U*r := by
    have h := ((hTu.hasDerivAt.pow 2).mul (hasDerivAt_const u r))
    change HasDerivAt (fun s ↦ N s d) _ u at h
    simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_zero, add_zero] using h.deriv
  have hNd : deriv (N u) d = 2*a*D*r + a^2*dr :=
    (hN_d (hTs.differentiableAt (by norm_num)) (hRs.differentiableAt (by norm_num))).deriv
  have hNd_u :
      deriv (fun s ↦ deriv (N s) d) u = 2*U*D*r + 2*a*M*r + 2*a*U*dr := by
    have hlocal : (fun s ↦ deriv (N s) d) =ᶠ[nhds u]
        fun s ↦ 2*T s d*deriv (T s) d*r + (T s d)^2*dr := by
      apply (eventually_gt_nhds hu).mono
      intro s hs
      obtain ⟨_, _, _, _, _, hTs, _, _⟩ := upperTail_rootDifference_bounds hh hhmax hs hd
      exact (hN_d (hTs.differentiableAt (by norm_num))
        (hRs.differentiableAt (by norm_num))).deriv
    have hL := ((hTu.hasDerivAt.const_mul 2).mul hTdu.hasDerivAt).mul_const r
    have hR := (hTu.hasDerivAt.pow 2).mul_const dr
    have h := ((hL.add hR).congr_of_eventuallyEq hlocal).deriv
    rw [h]
    dsimp [a, U, D, M]
    simp only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    ring
  have hNdd : deriv (deriv (N u)) d = 2*D^2*r + 2*a*DD*r + 4*a*D*dr + a^2*ddr := by
    have hTd : HasDerivAt (deriv (T u)) DD d :=
      ((hTs.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt
    have hRd : HasDerivAt (deriv R) ddr d :=
      ((hRs.derivWithin (m := 1) (by norm_num)).differentiableAt_one).hasDerivAt
    have hT := (hTs.differentiableAt (by norm_num)).hasDerivAt
    have hR := (hRs.differentiableAt (by norm_num)).hasDerivAt
    have hlocal : deriv (N u) =ᶠ[nhds d]
        fun t ↦ 2*T u t*deriv (T u) t*R t + (T u t)^2*deriv R t := by
      filter_upwards [hTs.eventually (by simp), hRs.eventually (by simp)] with t ht hr
      exact (hN_d (ht.differentiableAt (by norm_num)) (hr.differentiableAt (by norm_num))).deriv
    have hL := ((hT.const_mul 2).mul hTd).mul hR
    have hS := (hT.pow 2).mul hRd
    have h := ((hL.add hS).congr_of_eventuallyEq hlocal).deriv
    rw [h]
    dsimp [a, D, DD, r, dr, ddr]
    simp only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    ring
  have term {k a b z A B C : ℝ} (hk : 0 ≤ k)
      (ha : |a| ≤ A*x) (hb : |b| ≤ B*x) (hz : |z| ≤ C*r) :
      |k*a*b*z| ≤ (k*A*B*C)*x := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hk]
    have hkA := mul_le_mul_of_nonneg_left ha hk
    have hkB := mul_le_mul hkA hb (abs_nonneg _) ((mul_nonneg hk (abs_nonneg _)).trans hkA)
    have hkC := mul_le_mul hkB hz (abs_nonneg _)
      ((mul_nonneg (mul_nonneg hk (abs_nonneg _)) (abs_nonneg _)).trans hkB)
    apply hkC.trans_eq
    calc
      _ = (k*A*B*C)*x*(x*r) := by ring
      _ = _ := by rw [hxr, mul_one]
  have hr : |r| ≤ 1*r := by
    have hr := (upperTail_inverseScale_bounds hh hc hd).1
    change 0 < r at hr
    rw [abs_of_pos hr, one_mul]
  have h₀ : |a^2*r| ≤ 4*x := calc
    _ = |1*a*a*r| := congrArg abs (by ring)
    _ ≤ _ := (term (k := 1) (by norm_num) ha ha hr).trans_eq (by ring)
  have h₁ : |2*a*U*r| ≤ 16*x :=
    (term (k := 2) (by norm_num) ha hu₁ hr).trans_eq (by ring)
  have h₂ : |2*a*D*r| ≤ 20*x :=
    (term (k := 2) (by norm_num) ha hd₁ hr).trans_eq (by ring)
  have h₃ : |a^2*dr| ≤ 8*x := calc
    _ = |1*a*a*dr| := congrArg abs (by ring)
    _ ≤ _ := (term (k := 1) (by norm_num) ha ha hr₁).trans_eq (by ring)
  have h₄ : |2*U*D*r| ≤ 40*x :=
    (term (k := 2) (by norm_num) hu₁ hd₁ hr).trans_eq (by ring)
  have h₅ : |2*a*M*r| ≤ 32*x :=
    (term (k := 2) (by norm_num) ha hm hr).trans_eq (by ring)
  have h₆ : |2*a*U*dr| ≤ 32*x :=
    (term (k := 2) (by norm_num) ha hu₁ hr₁).trans_eq (by ring)
  have h₇ : |2*D^2*r| ≤ 50*x := by
    have h := term (k := 2) (by norm_num) hd₁ hd₁ hr
    simpa only [pow_two, mul_assoc] using h.trans_eq (show _ = 50*x by ring)
  have h₈ : |2*a*DD*r| ≤ 40*x :=
    (term (k := 2) (by norm_num) ha hdd hr).trans_eq (by ring)
  have h₉ : |4*a*D*dr| ≤ 80*x :=
    (term (k := 4) (by norm_num) ha hd₁ hr₁).trans_eq (by ring)
  have h₁₀ : |a^2*ddr| ≤ 20*x := calc
    _ = |1*a*a*ddr| := congrArg abs (by ring)
    _ ≤ _ := (term (k := 1) (by norm_num) ha ha hr₂).trans_eq (by ring)
  change |a^2*r| ≤ 4*x ∧ |deriv (fun s ↦ N s d) u| ≤ 16*x ∧
    |deriv (N u) d| ≤ 28*x ∧ |deriv (fun s ↦ deriv (N s) d) u| ≤ 104*x ∧
    |deriv (deriv (N u)) d| ≤ 190*x
  rw [hNdu, hNd, hNd_u, hNdd]
  refine ⟨h₀, h₁, ?_, ?_, ?_⟩
  · linarith only [abs_add_le (2*a*D*r) (a^2*dr), h₂, h₃]
  · linarith only [abs_add_le (2*U*D*r + 2*a*M*r) (2*a*U*dr),
      abs_add_le (2*U*D*r) (2*a*M*r), h₄, h₅, h₆]
  · linarith only [abs_add_le (2*D^2*r + 2*a*DD*r + 4*a*D*dr) (a^2*ddr),
      abs_add_le (2*D^2*r + 2*a*DD*r) (4*a*D*dr),
      abs_add_le (2*D^2*r) (2*a*DD*r), h₇, h₈, h₉, h₁₀]

#print axioms upperTail_average_derivative
#print axioms upperTail_quadratic_rationalization
#print axioms upperTailLambda_deriv_bounds
#print axioms upperTail_decay_envelope
#print axioms upperTail_radical_lower
#print axioms upperTail_rate_derivatives
#print axioms upperTail_radical_derivatives
#print axioms upperTail_rootDifference_bounds
#print axioms upperTail_inverseScale_bounds
#print axioms upperTail_quadratic_bounds

end RefinedBMV.PositiveCenter
