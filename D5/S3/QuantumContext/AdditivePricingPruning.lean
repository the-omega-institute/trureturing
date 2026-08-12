/- GID: D5/S3/QuantumContext/AdditivePricingPruning
   generality: G
   mirror-B: D5/B/S3/QuantumContext/AdditivePricingPruning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify additive context invariance and exact qutrit higher-degree pruning. -/

/- Library-search audit trail (2026-08-13):
   * `Matrix.trace_sum`, `Matrix.mul_sum`, and `Matrix.mul_one` give the general finite
     complete-context identity without coordinate expansion.
   * The frozen qutrit context certificates and exact quartic totals provide the degree-four
     leg; `norm_num` computes the corresponding degree-six totals over the same matrices.
   * The certificate is an exact two-context statement echo. It asserts no random-basis
     variance, sampled spectral statistic, or approximation of an unformalized real number.
-/

import D5.S3.QuantumContext.QuarticContextWitness

namespace D5.S3.QuantumContext.AdditivePricingPruning

open D5.S3.Quantum.FiniteDimensional
open D5.S3.QuantumContext.QuarticContextWitness
open scoped BigOperators ComplexOrder

/-- A finite matrix family resolves the identity. No orthogonality or idempotence is needed
for the additive-total identity. -/
def IsCompleteContext {n i : Type*} [Fintype n] [DecidableEq n] [Fintype i]
    (context : i -> Matrix n n ℂ) : Prop :=
  ∑ k, context k = 1

/-- The additive Born total of a matrix over a finite context. It is quadratic in pure-state
amplitudes, in contrast with the higher-degree prices below. -/
noncomputable def additiveContextTotal {n i : Type*} [Fintype n] [Fintype i]
    (rho : Matrix n n ℂ) (context : i -> Matrix n n ℂ) : ℂ :=
  ∑ k, bornProbability rho (context k)

/-- Additive pricing over any finite complete context is the trace of the priced matrix. -/
theorem additive_total_eq_trace {n i : Type*} [Fintype n] [DecidableEq n] [Fintype i]
    (rho : Matrix n n ℂ) (context : i -> Matrix n n ℂ)
    (hContext : IsCompleteContext context) :
    additiveContextTotal rho context = Matrix.trace rho := by
  classical
  calc
    additiveContextTotal rho context = Matrix.trace (∑ k, rho * context k) := by
      simp [additiveContextTotal, bornProbability, Matrix.trace_sum]
    _ = Matrix.trace (rho * ∑ k, context k) := by rw [Matrix.mul_sum]
    _ = Matrix.trace rho := by rw [hContext, Matrix.mul_one]

/-- A trace-one matrix has additive total one in every finite complete context. -/
theorem additive_total_context_invariant {n i : Type*}
    [Fintype n] [DecidableEq n] [Fintype i]
    (rho : Matrix n n ℂ) (hTrace : Matrix.trace rho = 1)
    (context : i -> Matrix n n ℂ) (hContext : IsCompleteContext context) :
    additiveContextTotal rho context = 1 := by
  rw [additive_total_eq_trace rho context hContext, hTrace]

/-- Cube a projection's real Born weight, giving degree six in pure-state amplitudes. -/
noncomputable def sexticPrice (rho projection : QutritMatrix) : ℝ :=
  (bornProbability rho projection).re ^ 3

/-- Total sextic price assigned to the three outcomes of one qutrit context. -/
noncomputable def sexticContextTotal
    (rho : QutritMatrix) (context : Fin 3 -> QutritMatrix) : ℝ :=
  ∑ k, sexticPrice rho (context k)

/-- The coordinate context has three sextic contributions `(1/3)^3`, totaling `1/9`. -/
theorem standard_sextic_total :
    sexticContextTotal uniformDensity standardProjection = 1 / 9 := by
  norm_num [sexticContextTotal, sexticPrice, bornProbability, uniformDensity,
    standardProjection, alignedProjection, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, Matrix.cons_val_two]

/-- The aligned context has sextic contributions `1`, `0`, and `0`. -/
theorem aligned_sextic_total :
    sexticContextTotal uniformDensity alignedProjection = 1 := by
  norm_num [sexticContextTotal, sexticPrice, bornProbability, uniformDensity,
    alignedProjection, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.cons_val_two]

/-- Exact finite pruning certificate: degree two is invariant across the two complete contexts,
while the displayed degree-four and degree-six totals have strict context gaps. -/
theorem harmonic_spectral_pruning_certificate :
    (additiveContextTotal uniformDensity standardProjection = 1 ∧
      additiveContextTotal uniformDensity alignedProjection = 1) ∧
    (quarticContextTotal uniformDensity standardProjection = 1 / 3 ∧
      quarticContextTotal uniformDensity alignedProjection = 1) ∧
    (sexticContextTotal uniformDensity standardProjection = 1 / 9 ∧
      sexticContextTotal uniformDensity alignedProjection = 1) ∧
    quarticContextTotal uniformDensity standardProjection <
      quarticContextTotal uniformDensity alignedProjection ∧
    sexticContextTotal uniformDensity standardProjection <
      sexticContextTotal uniformDensity alignedProjection := by
  have hTrace : Matrix.trace uniformDensity = 1 := uniform_density_is_state.2
  have hStandard : IsCompleteContext standardProjection :=
    standard_context_is_projective.2
  have hAligned : IsCompleteContext alignedProjection :=
    aligned_context_is_projective.2
  rw [additive_total_context_invariant uniformDensity hTrace standardProjection hStandard,
    additive_total_context_invariant uniformDensity hTrace alignedProjection hAligned,
    standard_quartic_total, aligned_quartic_total, standard_sextic_total,
    aligned_sextic_total]
  norm_num

/-- The exact Born controls have zero defect, hence lie strictly within `10^-16`, while the
quartic context gap is strictly larger than that tolerance. -/
theorem born_control_numerical_tolerance_certificate :
    |(additiveContextTotal uniformDensity standardProjection).re - 1| = 0 ∧
    |(additiveContextTotal uniformDensity alignedProjection).re - 1| = 0 ∧
    (1 : ℝ) / 10 ^ 16 <
      |quarticContextTotal uniformDensity standardProjection -
        quarticContextTotal uniformDensity alignedProjection| := by
  have hCertificate := harmonic_spectral_pruning_certificate
  rw [hCertificate.1.1, hCertificate.1.2, hCertificate.2.1.1,
    hCertificate.2.1.2]
  norm_num

/-- The hypotheses and conclusions are jointly inhabited by a positive trace-one qutrit state
and two complete contexts with a positive additive total and a strict quartic separation. -/
theorem additive_pricing_anti_vacuity_witness :
    ∃ rho : QutritMatrix,
      rho.PosSemidef ∧
      Matrix.trace rho = 1 ∧
      IsCompleteContext standardProjection ∧
      IsCompleteContext alignedProjection ∧
      0 < (additiveContextTotal rho standardProjection).re ∧
      quarticContextTotal rho standardProjection <
        quarticContextTotal rho alignedProjection := by
  refine ⟨uniformDensity, uniform_density_is_state.1, uniform_density_is_state.2,
    standard_context_is_projective.2, aligned_context_is_projective.2, ?_, ?_⟩
  · rw [additive_total_eq_trace uniformDensity standardProjection
      standard_context_is_projective.2, uniform_density_is_state.2]
    norm_num
  · exact quartic_pricing_context_counterexample.2.2

end D5.S3.QuantumContext.AdditivePricingPruning
