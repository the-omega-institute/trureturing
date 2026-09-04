/- GID: D5/S3/Quantum/MetricExpectationAsymptotics
   generality: G
   mirror-B: D5/B/S3/Quantum/MetricExpectationAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Standard endpoint asymptotics of an abstract upper incomplete-Gamma
   factor imply the stated small-parameter pole and large-parameter limit. -/

import Mathlib

/- Library-search audit trail (2026-09-04):
   * `MetricExponentReduction` already owns the independent mechanism by which
     an inverse-linear metric weight lowers a quadratic repulsion exponent.
   * Repository and pinned-Mathlib searches found ordinary `Gamma`, the lower
     `Complex.partialGamma`, and `Real.Gamma_one_half_eq`, but no reusable upper
     incomplete-Gamma declaration with the tail asymptotic needed here.
   * The atom does not specify the conditional probability law from which its
     exact expectation identity could be derived. Accordingly this module
     formalizes the displayed closed form and proves its endpoint consequences
     from the two standard upper incomplete-Gamma asymptotics; it does not claim
     to derive that closed form as an expectation.
   * Positivity and a nonzero zero-endpoint limit make every division used in
     the asymptotic argument nondegenerate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.MetricExpectationAsymptotics

open Filter Set
open scoped Topology

/-- The positive argument `2 * lambda^2` occurring in the source formula. -/
def scaledArgument (lambda : ℝ) : ℝ := 2 * lambda ^ 2

/-- The displayed closed form, parameterized by its upper incomplete-Gamma
factor because that special function is not available in pinned Mathlib. -/
noncomputable def metricExpectationClosedForm
    (upperGammaHalf : ℝ -> ℝ) (lambda : ℝ) : ℝ :=
  1 / (4 * lambda ^ 2) +
    Real.exp (-scaledArgument lambda) /
      (Real.sqrt 2 * lambda * upperGammaHalf (scaledArgument lambda))

/-- The first-order correction after removing the leading pole. -/
noncomputable def normalizedCorrection
    (upperGammaHalf : ℝ -> ℝ) (lambda : ℝ) : ℝ :=
  (4 * lambda ^ 2 * metricExpectationClosedForm upperGammaHalf lambda - 1) / lambda

private theorem scaledArgument_tendsto_nhdsGE_zero :
    Tendsto scaledArgument (𝓝[>] (0 : ℝ)) (𝓝[≥] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have lambda_limit :
        Tendsto (fun lambda : ℝ => lambda) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    change Tendsto (fun lambda : ℝ => 2 * lambda ^ 2) (𝓝[>] 0) (𝓝 0)
    simpa using (lambda_limit.pow 2).const_mul 2
  · exact Filter.Eventually.of_forall fun lambda => by
      simp only [mem_Ici, scaledArgument]
      positivity

private theorem scaledArgument_tendsto_atTop :
    Tendsto scaledArgument atTop atTop := by
  have square_limit : Tendsto (fun lambda : ℝ => lambda ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  change Tendsto (fun lambda : ℝ => 2 * lambda ^ 2) atTop atTop
  exact Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) square_limit

private theorem sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by
  positivity

/-- If the abstract upper incomplete-Gamma factor has its standard finite,
nonzero value at zero and its standard normalized tail, then the displayed
closed form has the source's small-parameter leading pole, a finite first-order
relative correction, and limit one at infinity. -/
theorem metric_expectation_closed_form_asymptotics
    (upperGammaHalf : ℝ -> ℝ) (gammaAtZero : ℝ)
    (gammaAtZero_ne : gammaAtZero ≠ 0)
    (upperGammaHalf_pos : ∀ x, 0 ≤ x -> 0 < upperGammaHalf x)
    (upperGammaHalf_at_zero :
      Tendsto upperGammaHalf (𝓝[≥] (0 : ℝ)) (𝓝 gammaAtZero))
    (upperGammaHalf_tail :
      Tendsto
        (fun x : ℝ => Real.sqrt x * Real.exp x * upperGammaHalf x)
        atTop (𝓝 1)) :
    Tendsto
        (fun lambda : ℝ =>
          4 * lambda ^ 2 * metricExpectationClosedForm upperGammaHalf lambda)
        (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (normalizedCorrection upperGammaHalf) (𝓝[>] 0)
        (𝓝 ((4 / Real.sqrt 2) / gammaAtZero)) ∧
      Tendsto (metricExpectationClosedForm upperGammaHalf) atTop (𝓝 1) := by
  have lambda_limit :
      Tendsto (fun lambda : ℝ => lambda) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have exponent_limit :
      Tendsto (fun lambda : ℝ => -scaledArgument lambda) (𝓝[>] 0) (𝓝 0) := by
    simpa [scaledArgument] using (lambda_limit.pow 2).const_mul (-2)
  have exp_limit :
      Tendsto (fun lambda : ℝ => Real.exp (-scaledArgument lambda))
        (𝓝[>] 0) (𝓝 1) := by
    exact Real.tendsto_exp_nhds_zero_nhds_one.comp exponent_limit
  have upper_limit :
      Tendsto (fun lambda : ℝ => upperGammaHalf (scaledArgument lambda))
        (𝓝[>] 0) (𝓝 gammaAtZero) :=
    upperGammaHalf_at_zero.comp scaledArgument_tendsto_nhdsGE_zero
  have coefficient_limit :
      Tendsto (fun _ : ℝ => 4 / Real.sqrt 2) (𝓝[>] 0)
        (𝓝 (4 / Real.sqrt 2)) :=
    tendsto_const_nhds
  have correction_raw_limit :
      Tendsto
        (fun lambda : ℝ =>
          (4 / Real.sqrt 2) * Real.exp (-scaledArgument lambda) /
            upperGammaHalf (scaledArgument lambda))
        (𝓝[>] 0) (𝓝 ((4 / Real.sqrt 2) / gammaAtZero)) := by
    simpa [div_eq_mul_inv, mul_assoc] using
      (coefficient_limit.mul exp_limit).mul (upper_limit.inv₀ gammaAtZero_ne)
  have correction_identity :
      (normalizedCorrection upperGammaHalf) =ᶠ[𝓝[>] 0]
        (fun lambda : ℝ =>
          (4 / Real.sqrt 2) * Real.exp (-scaledArgument lambda) /
            upperGammaHalf (scaledArgument lambda)) := by
    filter_upwards [self_mem_nhdsWithin] with lambda lambda_pos
    simp only [mem_Ioi] at lambda_pos
    have scaled_nonneg : 0 ≤ scaledArgument lambda := by
      rw [scaledArgument]
      positivity
    have upper_ne : upperGammaHalf (scaledArgument lambda) ≠ 0 :=
      (upperGammaHalf_pos _ scaled_nonneg).ne'
    rw [normalizedCorrection, metricExpectationClosedForm]
    field_simp [ne_of_gt lambda_pos, sqrt_two_ne_zero, upper_ne]
    ring
  have correction_limit :
      Tendsto (normalizedCorrection upperGammaHalf) (𝓝[>] 0)
        (𝓝 ((4 / Real.sqrt 2) / gammaAtZero)) :=
    correction_raw_limit.congr' correction_identity.symm
  have normalized_identity :
      (fun lambda : ℝ =>
        4 * lambda ^ 2 * metricExpectationClosedForm upperGammaHalf lambda) =ᶠ[𝓝[>] 0]
      (fun lambda : ℝ => 1 + lambda * normalizedCorrection upperGammaHalf lambda) := by
    filter_upwards [self_mem_nhdsWithin] with lambda lambda_pos
    simp only [mem_Ioi] at lambda_pos
    rw [normalizedCorrection]
    field_simp [ne_of_gt lambda_pos]
    ring
  have normalized_limit :
      Tendsto
        (fun lambda : ℝ =>
          4 * lambda ^ 2 * metricExpectationClosedForm upperGammaHalf lambda)
        (𝓝[>] 0) (𝓝 1) := by
    have raw_limit :
        Tendsto
          (fun lambda : ℝ =>
            1 + lambda * normalizedCorrection upperGammaHalf lambda)
          (𝓝[>] 0)
          (𝓝 (1 + 0 * ((4 / Real.sqrt 2) / gammaAtZero))) :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).add
          (lambda_limit.mul correction_limit)
    have raw_limit' :
        Tendsto
          (fun lambda : ℝ =>
            1 + lambda * normalizedCorrection upperGammaHalf lambda)
          (𝓝[>] 0) (𝓝 1) := by
      simpa using raw_limit
    exact raw_limit'.congr' normalized_identity.symm
  have denominator_limit :
      Tendsto (fun lambda : ℝ => 4 * lambda ^ 2) atTop atTop := by
    have square_limit : Tendsto (fun lambda : ℝ => lambda ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num)
    exact Tendsto.const_mul_atTop (by norm_num) square_limit
  have pole_limit :
      Tendsto (fun lambda : ℝ => 1 / (4 * lambda ^ 2)) atTop (𝓝 0) :=
    denominator_limit.const_div_atTop 1
  have tail_limit :
      Tendsto
        (fun lambda : ℝ =>
          Real.sqrt (scaledArgument lambda) *
            Real.exp (scaledArgument lambda) *
            upperGammaHalf (scaledArgument lambda))
        atTop (𝓝 1) :=
    upperGammaHalf_tail.comp scaledArgument_tendsto_atTop
  have tail_reciprocal_limit :
      Tendsto
        (fun lambda : ℝ =>
          (Real.sqrt (scaledArgument lambda) *
            Real.exp (scaledArgument lambda) *
            upperGammaHalf (scaledArgument lambda))⁻¹)
        atTop (𝓝 1) := by
    simpa using tail_limit.inv₀ one_ne_zero
  have tail_identity :
      (fun lambda : ℝ =>
        (Real.sqrt (scaledArgument lambda) *
          Real.exp (scaledArgument lambda) *
          upperGammaHalf (scaledArgument lambda))⁻¹) =ᶠ[atTop]
      (fun lambda : ℝ =>
        Real.exp (-scaledArgument lambda) /
          (Real.sqrt 2 * lambda * upperGammaHalf (scaledArgument lambda))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda lambda_pos
    have scaled_nonneg : 0 ≤ scaledArgument lambda := by
      rw [scaledArgument]
      positivity
    have upper_ne : upperGammaHalf (scaledArgument lambda) ≠ 0 :=
      (upperGammaHalf_pos _ scaled_nonneg).ne'
    have sqrt_scaled :
        Real.sqrt (scaledArgument lambda) = Real.sqrt 2 * lambda := by
      rw [scaledArgument, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_sq_eq_abs, abs_of_pos lambda_pos]
    rw [sqrt_scaled, Real.exp_neg]
    field_simp [ne_of_gt lambda_pos, sqrt_two_ne_zero, upper_ne, Real.exp_ne_zero]
  have regular_limit :
      Tendsto
        (fun lambda : ℝ =>
          Real.exp (-scaledArgument lambda) /
            (Real.sqrt 2 * lambda * upperGammaHalf (scaledArgument lambda)))
        atTop (𝓝 1) :=
    tail_reciprocal_limit.congr' tail_identity
  refine ⟨normalized_limit, correction_limit, ?_⟩
  change Tendsto
    (fun lambda : ℝ =>
      1 / (4 * lambda ^ 2) +
        Real.exp (-scaledArgument lambda) /
          (Real.sqrt 2 * lambda * upperGammaHalf (scaledArgument lambda)))
    atTop (𝓝 1)
  simpa only [zero_add] using pole_limit.add regular_limit

#print axioms metric_expectation_closed_form_asymptotics

end D5.S3.Quantum.MetricExpectationAsymptotics
