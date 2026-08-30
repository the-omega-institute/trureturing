/- GID: D5/S3/Quantum/Entanglement/BellPairLocalGlobalResidual
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/BellPairLocalGlobalResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Orthogonal Bell pure states share both marginals; diagonal pairs are excluded. -/

import D5.S3.Quantum.Entanglement.LocalMarginalCorrelationBlindSpot

/- Library-search audit trail (2026-08-31):
   * Repository searches by Bell-state names, equal-partial-trace shapes, source
     digest, neighboring marginal theorems, abstract residuals, and relative-phase
     vocabulary found no orthogonal Bell pure-state pair with both marginals equal.
   * The nearest repository hit, `relativePhaseDensityWitness`, concerns a single
     qubit and diagonal readout, not a bipartite state and its two partial traces.
   * Loogle exact hits `Matrix.trace_vecMulVec`,
     `Matrix.posSemidef_vecMulVec_self_star`, and `Matrix.rank_vecMulVec_le`.
   * LeanSearch returned the same three outer-product facts. Neither service found
     a packaged Bell-pair local-global residual theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Entanglement.BellPairLocalGlobalResidual

open D5.S3.Quantum.Entanglement.LocalMarginalCorrelationBlindSpot
open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses
open D5.S3.QuantumBounds.CHSHWitness

/-- The unnormalized coefficient matrix of the negative-phase Bell vector. -/
def bellMinusCoefficients : QubitMatrix := !![1, 0; 0, -1]

/-- The negative-phase Bell vector `(00 - 11) / sqrt(2)`. -/
noncomputable def bellMinusVector : Fin 2 × Fin 2 → ℂ :=
  fun index => bellMinusCoefficients index.1 index.2 / (Real.sqrt 2 : ℂ)

/-- The rank-one density matrix of the negative-phase Bell vector. -/
noncomputable def bellMinusDensity : TwoQubitMatrix :=
  Matrix.vecMulVec bellMinusVector (star bellMinusVector)

/-- The two-qubit instance of the quantum local-global residual: two density
matrices are distinct globally but agree after tracing out either factor. -/
def twoQubitLocalGlobalResidual : Set (TwoQubitMatrix × TwoQubitMatrix) :=
  {pair |
    pair.1.PosSemidef ∧
      Matrix.trace pair.1 = 1 ∧
      pair.2.PosSemidef ∧
      Matrix.trace pair.2 = 1 ∧
      traceEnvironment pair.1 = traceEnvironment pair.2 ∧
      traceFirstFactor pair.1 = traceFirstFactor pair.2 ∧
      pair.1 ≠ pair.2}

private theorem complex_sqrt_two_inv_mul_self :
    (Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹ = (2 : Complex)⁻¹ := by
  have realIdentity := congrArg (fun value : Real => (value : Complex))
    TsirelsonInequality.sqrt_two_inv_mul_self
  simpa using realIdentity

private theorem bell_minus_vector_normalized :
    bellMinusVector ⬝ᵥ star bellMinusVector = 1 := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [bellMinusVector, bellMinusCoefficients, div_eq_mul_inv,
    complex_sqrt_two_inv_mul_self]

private theorem bell_vectors_orthogonal :
    star bellVector ⬝ᵥ bellMinusVector = 0 := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [bellVector, bellCoefficients, bellMinusVector, bellMinusCoefficients,
    div_eq_mul_inv, complex_sqrt_two_inv_mul_self]

private theorem bell_minus_density_pos : bellMinusDensity.PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star bellMinusVector

private theorem bell_minus_density_trace : Matrix.trace bellMinusDensity = 1 := by
  rw [bellMinusDensity, Matrix.trace_vecMulVec]
  exact bell_minus_vector_normalized

private theorem bell_minus_density_rank_one : Matrix.rank bellMinusDensity = 1 := by
  have upper : Matrix.rank bellMinusDensity ≤ 1 := by
    simpa only [bellMinusDensity] using
      Matrix.rank_vecMulVec_le bellMinusVector (star bellMinusVector)
  have positive : 0 < Matrix.rank bellMinusDensity := by
    rw [Matrix.rank_eq_finrank_span_cols]
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    let index : Fin 2 × Fin 2 := (0, 0)
    let column : Submodule.span Complex (Set.range bellMinusDensity.col) :=
      ⟨bellMinusDensity.col index, Submodule.subset_span ⟨index, rfl⟩⟩
    refine ⟨column, ?_⟩
    intro hzero
    have hvalue := congrFun (congrArg Subtype.val hzero) index
    norm_num [column, index, bellMinusDensity, bellMinusVector, bellMinusCoefficients,
      Matrix.vecMulVec_apply, div_eq_mul_inv, complex_sqrt_two_inv_mul_self] at hvalue
  exact Nat.le_antisymm upper positive

private theorem bell_minus_second_marginal :
    traceEnvironment bellMinusDensity = (1 / 2 : Complex) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceEnvironment, bellMinusDensity, bellMinusVector, bellMinusCoefficients,
      Matrix.vecMulVec_apply, Fin.sum_univ_two, div_eq_mul_inv,
      complex_sqrt_two_inv_mul_self]

private theorem bell_minus_first_marginal :
    traceFirstFactor bellMinusDensity = (1 / 2 : Complex) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceFirstFactor, bellMinusDensity, bellMinusVector, bellMinusCoefficients,
      Matrix.vecMulVec_apply, Fin.sum_univ_two, div_eq_mul_inv,
      complex_sqrt_two_inv_mul_self]

private theorem classical_second_marginal :
    traceEnvironment classicalCorrelatedDensity =
      (1 / 2 : Complex) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceEnvironment, classicalCorrelatedDensity, Fin.sum_univ_two]

private theorem classical_first_marginal :
    traceFirstFactor classicalCorrelatedDensity =
      (1 / 2 : Complex) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceFirstFactor, classicalCorrelatedDensity, Fin.sum_univ_two]

private theorem bell_density_ne_bell_minus_density :
    bellDensity ≠ bellMinusDensity := by
  intro h
  have hentry := congrFun (congrFun h (0, 0)) (1, 1)
  norm_num [bellDensity, bellVector, bellCoefficients, bellMinusDensity,
    bellMinusVector, bellMinusCoefficients, Matrix.vecMulVec_apply,
    div_eq_mul_inv, complex_sqrt_two_inv_mul_self] at hentry

/-- The positive- and negative-phase Bell densities are rank-one states in the
two-qubit local-global residual, and their defining vectors are orthogonal. -/
theorem bell_pair_local_global_residual :
    (bellDensity, bellMinusDensity) ∈ twoQubitLocalGlobalResidual ∧
      Matrix.rank bellDensity = 1 ∧
      Matrix.rank bellMinusDensity = 1 ∧
      star bellVector ⬝ᵥ bellMinusVector = 0 := by
  rcases local_marginal_correlation_blind_spot 2 2 (by omega) (by omega) (by omega) with
    ⟨_, _, _, _, _, hBellPos, hBellTrace, hBellRank, _, _, _,
      hBellSecond, hBellFirst, _⟩
  have secondMarginalsEqual :
      traceEnvironment bellDensity = traceEnvironment bellMinusDensity := by
    calc
      traceEnvironment bellDensity =
          traceEnvironment classicalCorrelatedDensity := hBellSecond
      _ = (1 / 2 : Complex) • (1 : QubitMatrix) := classical_second_marginal
      _ = traceEnvironment bellMinusDensity := bell_minus_second_marginal.symm
  have firstMarginalsEqual :
      traceFirstFactor bellDensity = traceFirstFactor bellMinusDensity := by
    calc
      traceFirstFactor bellDensity =
          traceFirstFactor classicalCorrelatedDensity := hBellFirst
      _ = (1 / 2 : Complex) • (1 : QubitMatrix) := classical_first_marginal
      _ = traceFirstFactor bellMinusDensity := bell_minus_first_marginal.symm
  refine ⟨?_, hBellRank, bell_minus_density_rank_one, bell_vectors_orthogonal⟩
  exact ⟨hBellPos, hBellTrace, bell_minus_density_pos, bell_minus_density_trace,
    secondMarginalsEqual, firstMarginalsEqual, bell_density_ne_bell_minus_density⟩

#print axioms bell_pair_local_global_residual

/-- Complete knowledge of both one-qubit marginals does not determine the
two-qubit global density matrix. -/
theorem two_qubit_local_global_residual_nonempty :
    twoQubitLocalGlobalResidual.Nonempty :=
  ⟨(bellDensity, bellMinusDensity), bell_pair_local_global_residual.1⟩

#print axioms two_qubit_local_global_residual_nonempty

/-- Degenerate equal pairs, including the zero and identity pairs, never enter
the residual: global distinctness is a load-bearing part of its definition. -/
theorem diagonal_pair_not_mem_two_qubit_local_global_residual
    (rho : TwoQubitMatrix) :
    (rho, rho) ∉ twoQubitLocalGlobalResidual := by
  simp [twoQubitLocalGlobalResidual]

#print axioms diagonal_pair_not_mem_two_qubit_local_global_residual

end D5.S3.Quantum.Entanglement.BellPairLocalGlobalResidual
