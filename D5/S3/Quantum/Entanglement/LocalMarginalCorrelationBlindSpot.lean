/- GID: D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete local marginals leave the full bipartite correlation sector unread. -/

import D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition

/- Library-search audit trail (2026-08-24):
   * Exact family hits `localASector`, `localBSector`, `correlationSector`,
     `bipartiteTraceZero`, and `bipartite_sector_decomposition` construct the
     source's local and correlation sectors and prove their dimensions and
     orthogonal decomposition. They are imported and applied directly.
   * Exact family hits `bellDensity`, `bell_density_is_state`,
     `bell_pure_state_has_maximally_mixed_marginal`, and `traceEnvironment`
     construct the Bell state and its canonical second-factor trace.
   * Repository searches found no first-factor partial trace, explicit
     classically correlated Bell mixture, or theorem packaging the local blind
     spot with the two equal-marginal global states.
   * Pinned Mathlib exact hits `Matrix.PosSemidef.diagonal`,
     `Submodule.finrank_sup_add_finrank_inf_eq`, and orthogonality-disjointness
     are used below. `loogle` and `leansearch` are absent from PATH. -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

namespace D5.S3.Quantum.Entanglement.LocalMarginalCorrelationBlindSpot

open D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.QubitWitnesses
open D5.S3.QuantumBounds.CHSHWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

/-- Trace the first factor out of a two-qubit density matrix by summing equal
first-factor indices. -/
def traceFirstFactor (joint : TwoQubitMatrix) : QubitMatrix :=
  fun i j => ∑ a, joint (a, i) (a, j)

/-- The explicit classical mixture assigning weight one half to each of the
correlated computational-basis states `00` and `11`. -/
def classicalCorrelatedDensity : TwoQubitMatrix :=
  Matrix.diagonal fun index => if index.1 = index.2 then (1 / 2 : Complex) else 0

private theorem complex_sqrt_two_inv_mul_self :
    (Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹ = (2 : Complex)⁻¹ := by
  have realIdentity := congrArg (fun value : Real => (value : Complex))
    TsirelsonInequality.sqrt_two_inv_mul_self
  simpa using realIdentity

private theorem classical_correlated_density_pos :
    classicalCorrelatedDensity.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro index
  by_cases h : index.1 = index.2
  · simp [h]
  · simp [h]

private theorem classical_correlated_density_trace :
    Matrix.trace classicalCorrelatedDensity = 1 := by
  simp [Matrix.trace, classicalCorrelatedDensity, Fintype.sum_prod_type]

private theorem classical_correlated_density_not_idempotent :
    Not (classicalCorrelatedDensity * classicalCorrelatedDensity =
      classicalCorrelatedDensity) := by
  intro h
  have h00 := congrFun (congrFun h (0, 0)) (0, 0)
  norm_num [classicalCorrelatedDensity, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two] at h00

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

private theorem bell_first_marginal :
    traceFirstFactor bellDensity = (1 / 2 : Complex) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceFirstFactor, bellDensity, bellVector, bellCoefficients,
      Matrix.vecMulVec_apply, Fin.sum_univ_two, complex_sqrt_two_inv_mul_self]

private theorem bell_ne_classical_correlated_density :
    bellDensity ≠ classicalCorrelatedDensity := by
  intro h
  have hentry := congrFun (congrFun h (0, 0)) (1, 1)
  norm_num [bellDensity, bellVector, bellCoefficients,
    Matrix.vecMulVec_apply, classicalCorrelatedDensity,
    complex_sqrt_two_inv_mul_self] at hentry

/-- Reading both locally complete marginal sectors leaves precisely the
orthogonal correlation sector unread. Its dimension and its proportion of all
traceless directions have the stated formulas. The Bell density and the
explicit classical correlated mixture witness that equal local marginals do
not determine the global state. -/
theorem local_marginal_correlation_blind_spot
    (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) (_hproduct : 1 < m * n) :
    localASector m n ⊔ localBSector m n ⊔ correlationSector m n =
        bipartiteTraceZero m n ∧
      Module.finrank ℝ ↥(localASector m n ⊔ localBSector m n) =
        (m ^ 2 - 1) + (n ^ 2 - 1) ∧
      Module.finrank ℝ (correlationSector m n) =
        (m ^ 2 - 1) * (n ^ 2 - 1) ∧
      (Module.finrank ℝ (correlationSector m n) : ℝ) /
          Module.finrank ℝ (bipartiteTraceZero m n) =
        (((m ^ 2 - 1) * (n ^ 2 - 1) : Nat) : ℝ) /
          (((m ^ 2) * (n ^ 2) - 1 : Nat) : ℝ) ∧
      Submodule.IsOrtho (𝕜 := ℝ)
        (localASector m n ⊔ localBSector m n) (correlationSector m n) ∧
      bellDensity.PosSemidef ∧
      Matrix.trace bellDensity = 1 ∧
      Matrix.rank bellDensity = 1 ∧
      classicalCorrelatedDensity.PosSemidef ∧
      Matrix.trace classicalCorrelatedDensity = 1 ∧
      Not (classicalCorrelatedDensity * classicalCorrelatedDensity =
        classicalCorrelatedDensity) ∧
      traceEnvironment bellDensity =
        traceEnvironment classicalCorrelatedDensity ∧
      traceFirstFactor bellDensity =
        traceFirstFactor classicalCorrelatedDensity ∧
      bellDensity ≠ classicalCorrelatedDensity := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero n := ⟨by omega⟩
  rcases bipartite_sector_decomposition m n with
    ⟨hdecomp, hAB, hAC, hBC, hA, hB, hC⟩
  have hABorthogonal :
      localASector m n ⊔ localBSector m n ⟂ correlationSector m n := by
    rw [Submodule.isOrtho_sup_left]
    exact ⟨hAC, hBC⟩
  have hABdim :
      Module.finrank ℝ ↥(localASector m n ⊔ localBSector m n) =
        (m ^ 2 - 1) + (n ^ 2 - 1) := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (localASector m n) (localBSector m n)
    rw [hAB.disjoint.eq_bot, finrank_bot, add_zero, hA, hB] at hdim
    exact hdim
  have hTraceDim :
      Module.finrank ℝ (bipartiteTraceZero m n) = (m * n) ^ 2 - 1 := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (localASector m n ⊔ localBSector m n) (correlationSector m n)
    rw [hABorthogonal.disjoint.eq_bot, finrank_bot, add_zero,
      hABdim, hC] at hdim
    rw [hdecomp] at hdim
    rw [hdim, sector_dimension_sum]
  have hRatio :
      (Module.finrank ℝ (correlationSector m n) : ℝ) /
          Module.finrank ℝ (bipartiteTraceZero m n) =
        (((m ^ 2 - 1) * (n ^ 2 - 1) : Nat) : ℝ) /
          (((m ^ 2) * (n ^ 2) - 1 : Nat) : ℝ) := by
    rw [hC, hTraceDim]
    congr 2
    congr 1
    ring
  rcases bell_pure_state_has_maximally_mixed_marginal with
    ⟨_, hBellPos, hBellTrace, hBellRank, _, hBellSecond, _⟩
  refine ⟨hdecomp, hABdim, hC, hRatio, hABorthogonal,
    hBellPos, hBellTrace, hBellRank,
    classical_correlated_density_pos, classical_correlated_density_trace,
    classical_correlated_density_not_idempotent, ?_, ?_,
    bell_ne_classical_correlated_density⟩
  · rw [hBellSecond, classical_second_marginal]
  · rw [bell_first_marginal, classical_first_marginal]

#print axioms local_marginal_correlation_blind_spot

end D5.S3.Quantum.Entanglement.LocalMarginalCorrelationBlindSpot
