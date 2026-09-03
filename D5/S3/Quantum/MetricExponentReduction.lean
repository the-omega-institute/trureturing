/- GID: D5/S3/Quantum/MetricExponentReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/MetricExponentReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A metric weight asymptotic to m divided by lambda converts a density asymptotic to c lambda squared into a weighted density asymptotic to mc lambda, with an exact model witnessing sharp exponent loss. -/

import Mathlib

/- Library-search audit trail (2026-09-04):
   * D5 searches for pseudo-Hermitian, Krein/CPT, GUE, level-repulsion,
     fluctuating metric, and exponent-reduction spellings found no whole target.
   * Pinned Mathlib has the ordinary Gamma function but no upper incomplete
     Gamma declaration matching the source's exact expectation formula, so that
     formula is not postulated here. Mathlib's `Filter.Tendsto.mul` and
     `tendsto_inv_nhdsGT_zero` directly supply the general asymptotic mechanism.
   * The theorem is stated on the positive-side filter and every displayed
     division is justified there by `lambda > 0`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.MetricExponentReduction

open Filter Set
open scoped Topology

/-- If `lambda * metricWeight lambda` tends to a positive coefficient `m` and
`density lambda / lambda^2` tends to a positive coefficient `c`, then the
metric-weighted density divided by `lambda` tends to `m*c`. Thus an inverse
linear metric weight lowers a quadratic small-spacing exponent to one. -/
theorem inverse_metric_reduces_quadratic_exponent
    (metricWeight density : ℝ -> ℝ) (metricCoefficient densityCoefficient : ℝ)
    (metricCoefficient_pos : 0 < metricCoefficient)
    (densityCoefficient_pos : 0 < densityCoefficient)
    (metric_limit : Tendsto (fun lambda => lambda * metricWeight lambda)
      (𝓝[>] 0) (𝓝 metricCoefficient))
    (density_limit : Tendsto (fun lambda => density lambda / lambda ^ 2)
      (𝓝[>] 0) (𝓝 densityCoefficient)) :
    Tendsto (fun lambda => metricWeight lambda * density lambda / lambda)
        (𝓝[>] 0) (𝓝 (metricCoefficient * densityCoefficient)) ∧
      0 < metricCoefficient * densityCoefficient := by
  have product_limit := metric_limit.mul density_limit
  have identity :
      (fun lambda =>
        (lambda * metricWeight lambda) * (density lambda / lambda ^ 2)) =ᶠ[𝓝[>] 0]
      (fun lambda => metricWeight lambda * density lambda / lambda) := by
    filter_upwards [self_mem_nhdsWithin] with lambda lambda_pos
    simp only [mem_Ioi] at lambda_pos
    field_simp [ne_of_gt lambda_pos]
  exact ⟨product_limit.congr' identity, mul_pos metricCoefficient_pos densityCoefficient_pos⟩

/-- The exponent reduction is sharp and its hypotheses are jointly
satisfiable. The explicit model `w(lambda)=m/lambda`, `d(lambda)=c*lambda^2`
has exact linear weighted density on every positive lambda, while its
quadratic normalization diverges at zero. -/
theorem inverse_metric_linear_model_is_sharp
    (metricCoefficient densityCoefficient : ℝ)
    (metricCoefficient_pos : 0 < metricCoefficient)
    (densityCoefficient_pos : 0 < densityCoefficient) :
    let metricWeight : ℝ -> ℝ := fun lambda => metricCoefficient / lambda
    let density : ℝ -> ℝ := fun lambda => densityCoefficient * lambda ^ 2
    (forall lambda, 0 < lambda ->
        metricWeight lambda * density lambda =
          (metricCoefficient * densityCoefficient) * lambda) ∧
      Tendsto (fun lambda => metricWeight lambda * density lambda / lambda)
        (𝓝[>] 0) (𝓝 (metricCoefficient * densityCoefficient)) ∧
      Tendsto (fun lambda => metricWeight lambda * density lambda / lambda ^ 2)
        (𝓝[>] 0) atTop := by
  dsimp
  have exact_linear : forall lambda : ℝ, 0 < lambda ->
      metricCoefficient / lambda * (densityCoefficient * lambda ^ 2) =
        metricCoefficient * densityCoefficient * lambda := by
    intro lambda lambda_pos
    field_simp [ne_of_gt lambda_pos]
  constructor
  · exact exact_linear
  constructor
  · have eventually_constant :
        (fun lambda : ℝ =>
          metricCoefficient / lambda * (densityCoefficient * lambda ^ 2) / lambda) =ᶠ[𝓝[>] 0]
        (fun _ => metricCoefficient * densityCoefficient) := by
        filter_upwards [self_mem_nhdsWithin] with lambda lambda_pos
        simp only [mem_Ioi] at lambda_pos
        rw [exact_linear lambda lambda_pos]
        field_simp [ne_of_gt lambda_pos]
    exact tendsto_const_nhds.congr' eventually_constant.symm
  · have reciprocal_limit :
        Tendsto (fun lambda : ℝ =>
          (metricCoefficient * densityCoefficient) * lambda⁻¹)
          (𝓝[>] 0) atTop :=
        Tendsto.const_mul_atTop
          (mul_pos metricCoefficient_pos densityCoefficient_pos)
          tendsto_inv_nhdsGT_zero
    apply reciprocal_limit.congr'
    filter_upwards [self_mem_nhdsWithin] with lambda lambda_pos
    simp only [mem_Ioi] at lambda_pos
    rw [exact_linear lambda lambda_pos]
    field_simp [ne_of_gt lambda_pos]

#print axioms inverse_metric_reduces_quadratic_exponent
#print axioms inverse_metric_linear_model_is_sharp

end D5.S3.Quantum.MetricExponentReduction
