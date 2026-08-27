/- GID: D5/S3/Constants/Characterizations/ExponentialFlowUniqueness
   generality: G
   mirror-B: D5/B/S3/Constants/Characterizations/ExponentialFlowUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive normalized multiplicative C1 flows are exponential. -/

import Mathlib

/- Library-search audit trail (2026-08-27):
   * D5 has no theorem characterizing positive real solutions of the multiplicative Cauchy
     equation; existing exponential-flow hits concern matrix-valued dynamics.
   * Pinned mathlib has no continuous multiplicative-Cauchy classification theorem for real
     functions. Its `exp_unique_of_derivative_eq_self` applies only to formal power series.
   * Mathlib supplies the exact local ingredients reused below: `HasDerivAt.unique`,
     `Real.hasDerivAt_exp`, and `is_const_of_deriv_eq_zero`.
   * Loogle returned zero matches for the full classification type. LeanSearch and GitHub Lean
     code search returned only exponential primitives, formal power series, or unrelated
     functional equations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Characterizations.ExponentialFlowUniqueness

/-- A positive `C¹` real flow that turns addition into multiplication and whose derivative at
zero is one agrees pointwise with the real exponential. -/
theorem exponential_flow_unique
    (E : ℝ → ℝ)
    (hpositive : ∀ x, 0 < E x)
    (hregular : ContDiff ℝ 1 E)
    (hmul : ∀ x y, E (x + y) = E x * E y)
    (hnormalized : deriv E 0 = 1) :
    ∀ x, E x = Real.exp x := by
  intro x
  have hdifferentiable : Differentiable ℝ E := hregular.differentiable_one
  have hzero : E 0 = 1 := by
    have hidempotent := hmul 0 0
    simp only [zero_add] at hidempotent
    nlinarith [hpositive 0]
  have hderiv_self (t : ℝ) : deriv E t = E t := by
    have hflow :
        (fun y : ℝ => E (t + y)) = fun y : ℝ => E t * E y := by
      funext y
      exact hmul t y
    have hderiv := congrArg (fun f : ℝ → ℝ => deriv f 0) hflow
    simpa only [deriv_comp_const_add, add_zero, deriv_const_mul_field,
      hnormalized, mul_one] using hderiv
  let ratio : ℝ → ℝ := fun t => E t / Real.exp t
  have hratio_differentiable : Differentiable ℝ ratio := by
    dsimp [ratio]
    exact hdifferentiable.fun_div Real.differentiable_exp Real.exp_ne_zero
  have hratio_deriv (t : ℝ) : deriv ratio t = 0 := by
    have hquotient :=
      (hdifferentiable t).hasDerivAt.fun_div
        (Real.hasDerivAt_exp t) (Real.exp_ne_zero t)
    have hquotient_ratio :
        HasDerivAt ratio
          ((deriv E t * Real.exp t - E t * Real.exp t) / Real.exp t ^ 2) t := by
      simpa [ratio] using hquotient
    have hzero_deriv : HasDerivAt ratio 0 t := by
      simpa [hderiv_self t] using hquotient_ratio
    exact hzero_deriv.deriv
  have hratio_const :=
    is_const_of_deriv_eq_zero hratio_differentiable hratio_deriv 0 x
  have hratio_one : E x / Real.exp x = 1 := by
    simpa [ratio, hzero] using hratio_const.symm
  exact (div_eq_one_iff_eq (Real.exp_ne_zero x)).mp hratio_one

/-- Reverse probe: the public theorem fixes the flow's value at one, hence its exponential
normalization. -/
example
    (E : ℝ → ℝ)
    (hpositive : ∀ x, 0 < E x)
    (hregular : ContDiff ℝ 1 E)
    (hmul : ∀ x y, E (x + y) = E x * E y)
    (hnormalized : deriv E 0 = 1) :
    E 1 = Real.exp 1 :=
  exponential_flow_unique E hpositive hregular hmul hnormalized 1

/-- Trivialization probe: the zero flow is smooth and multiplicative, but it fails both the
strictly positive codomain and the derivative normalization. -/
example :
    (ContDiff ℝ 1 (fun _ : ℝ => (0 : ℝ)) ∧
        ∀ x y : ℝ, (fun _ : ℝ => (0 : ℝ)) (x + y) =
          (fun _ : ℝ => (0 : ℝ)) x * (fun _ : ℝ => (0 : ℝ)) y) ∧
      ¬ ((∀ x : ℝ, 0 < (fun _ : ℝ => (0 : ℝ)) x) ∧
        deriv (fun _ : ℝ => (0 : ℝ)) 0 = 1) := by
  constructor
  · constructor
    · fun_prop
    · simp
  · simp

#print axioms exponential_flow_unique

end D5.S3.Constants.Characterizations.ExponentialFlowUniqueness
