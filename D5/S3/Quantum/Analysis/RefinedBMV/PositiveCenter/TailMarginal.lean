/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/TailMarginal
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithmic derivative of the lower-gap marginal of the refined BMV kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.Regularized
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.UpperTail
import Mathlib.Tactic.FunProp

/-! # Logarithmic derivative bound for the upper-tail normalization -/

open Filter MeasureTheory
open scoped Topology

namespace RefinedBMV.PositiveCenter

open DimThree (gaps)
open SmallCorner (G G_pos hasDerivAt_G integralMarginalDerivative iteratedDeriv_G_eq_integral)

private theorem integral_weighted_exponent_ge_neg {y t : ℝ} (hy : -1 ≤ y) :
    -(∫ s in (0 : ℝ)..1, (1-s)*(y*s)*Real.exp (t*(y*s))) ≤
      ∫ s in (0 : ℝ)..1, (1-s)*Real.exp (t*(y*s)) := by
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro s hs
    have hys := mul_le_mul_of_nonneg_right hy hs.1
    have hys' : -(y*s) ≤ 1 := by linarith [hs.2]
    have hw := mul_nonneg (sub_nonneg.mpr hs.2) (Real.exp_pos (t*(y*s))).le
    nlinarith only [mul_le_mul_of_nonneg_right hys' hw]

private theorem neg_deriv_G_le {p : ℕ} (hp : 0 < p) {t : ℝ} (ht : t ≠ 0) :
    -deriv (G p 1) t ≤ G p 1 t := by
  let y : ℕ × ℕ × ℕ → ℝ := fun g ↦ 3*(g.2.2 : ℝ)/(p : ℝ)-1
  let f : ℕ × ℕ × ℕ → ℝ := fun g ↦ (y g)^2 *
    ∫ s in (0 : ℝ)..1, (1-s)*(y g*s)*Real.exp (t*(y g*s))
  let g₀ : ℕ × ℕ × ℕ → ℝ := fun g ↦ (y g)^2 *
    ∫ s in (0 : ℝ)..1, (1-s)*Real.exp (t*(y g*s))
  have hy (g : ℕ × ℕ × ℕ) : -1 ≤ y g := by
    have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
    have hz : 0 ≤ 3*(g.2.2 : ℝ)/(p : ℝ) := by positivity
    change -1 ≤ 3*(g.2.2 : ℝ)/(p : ℝ)-1
    linarith
  have hterm (g : ℕ × ℕ × ℕ) : -(f g) ≤ g₀ g := by
    have hi := integral_weighted_exponent_ge_neg (t := t) (hy g)
    have hm := mul_le_mul_of_nonneg_left hi (sq_nonneg (y g))
    simpa only [f, g₀, mul_neg] using hm
  have hsum (l : List (ℕ × ℕ × ℕ)) : -(l.map f).sum ≤ (l.map g₀).sum := by
    induction l with
    | nil => simp
    | cons g l ih =>
      simp only [List.map_cons, List.sum_cons]
      linarith only [ih, hterm g]
  have hval := iteratedDeriv_G_eq_integral hp one_ne_zero ht 0
  have hder := iteratedDeriv_G_eq_integral hp one_ne_zero ht 1
  rw [iteratedDeriv_zero] at hval
  rw [iteratedDeriv_one] at hder
  rw [hval, hder]
  unfold integralMarginalDerivative
  simp only [pow_one, pow_zero, mul_one]
  change -(((gaps p).map f).sum / ((gaps p).length : ℝ)) ≤
    ((gaps p).map g₀).sum / ((gaps p).length : ℝ)
  rw [← neg_div]
  exact div_le_div_of_nonneg_right (hsum (gaps p)) (by positivity)

/-- The logarithmic derivative of `u ↦ M(0,-u)` is at most `1+2/u`.
The exponential exponent in the normalized marginal is bounded above by
one in the negative-gap direction, uniformly in the degree. -/
theorem upperTail_marginal_logDeriv {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    deriv (fun x ↦ compositionMoment p 0 (-x)) u / compositionMoment p 0 (-u) ≤
      1 + 2/u := by
  let C : ℝ → ℝ := fun x ↦ compositionMoment p 0 (-x)
  have hId (x : ℝ) (hx : x ≠ 0) : C x = x^2 * G p 1 (-x) := by
    unfold C G
    field_simp [hx]
  have hnear : C =ᶠ[𝓝 u] (fun x ↦ x^2 * G p 1 (-x)) := by
    filter_upwards [eventually_ne_nhds hu.ne'] with x hx
    exact hId x hx
  have hn : -u ≠ 0 := neg_ne_zero.mpr hu.ne'
  have hg := hasDerivAt_G p one_ne_zero hn
  have hn' : HasDerivAt (fun x : ℝ ↦ -x) (-1) u :=
    HasDerivAt.neg (hasDerivAt_id' u)
  have hcom : HasDerivAt (fun x ↦ G p 1 (-x)) (-(deriv (G p 1) (-u))) u := by
    have h' := hg.comp u hn'
    change HasDerivAt (fun x ↦ G p 1 (-x)) _ u at h'
    simpa only [mul_neg_one, hg.deriv] using h'
  have hD := (hasDerivAt_pow 2 u).mul hcom
  have hop : deriv C u = 2*u*G p 1 (-u) + u^2*(-deriv (G p 1) (-u)) := by
    rw [hnear.deriv_eq]
    change deriv ((fun x : ℝ ↦ x^2) * fun x ↦ G p 1 (-x)) u = _
    rw [hD.deriv]
    norm_num
  change deriv C u / C u ≤ 1+2/u
  rw [hId u hu.ne', hop]
  have hG := G_pos hp (by norm_num : (0 : ℝ) < 1) hn
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hu) hG)).2
  calc
    _ ≤ 2*u*G p 1 (-u) + u^2*G p 1 (-u) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (neg_deriv_G_le hp hn) (sq_nonneg u))
    _ = _ := by field_simp [hu.ne'] <;> ring

/-- The actual marginal of the refined BMV kernel meets the tail scale
lower bound used by the mixed sign estimate. -/
theorem upperTail_marginal_scale {p : ℕ} (hp : 0 < p) {u : ℝ} (hu : 0 < u) :
    (1/4 : ℝ) ≤ 1 + 2/(Real.exp u-1) -
      (deriv (fun x ↦ compositionMoment p 0 (-x)) u / compositionMoment p 0 (-u))/2 :=
  upperTail_baseline_scale hu (upperTail_marginal_logDeriv hp hu)

#print axioms upperTail_marginal_logDeriv
#print axioms upperTail_marginal_scale

end RefinedBMV.PositiveCenter
