/- GID: D5/S3/Quantum/Entanglement/BellPureStateMixedMarginal
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/BellPureStateMixedMarginal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The pure Bell density has the maximally mixed one-qubit marginal. -/

import D5.S3.Quantum.EnvironmentRecords
import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.QuantumBounds.CHSHWitness

/- Library-search audit trail (2026-08-23):
   * Exact family hits `bellVector`, `bellDensity`, and `bell_density_is_state`
     construct the normalized Bell amplitude and its positive trace-one density.
   * Exact family hits `rankOneDensity`, `pure_state_handshake`, and
     `traceEnvironment` supply the canonical rank-one purity and partial-trace
     operations; they are imported and applied directly.
   * Pinned Mathlib exact hits `Matrix.rank_vecMulVec_le` and
     `TsirelsonInequality.sqrt_two_inv_mul_self` supply the rank upper bound and
     normalization arithmetic. No exact Bell partial-trace theorem was found. -/

noncomputable section

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal

open D5.S3.Quantum.EnvironmentRecords
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.QubitWitnesses
open D5.S3.QuantumBounds.CHSHWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem complex_sqrt_two_inv_mul_self :
    (Real.sqrt 2 : Complex)⁻¹ * (Real.sqrt 2 : Complex)⁻¹ = (2 : Complex)⁻¹ := by
  have realIdentity := congrArg (fun value : Real => (value : Complex))
    TsirelsonInequality.sqrt_two_inv_mul_self
  simpa using realIdentity

private theorem bell_vector_normalized : star bellVector ⬝ᵥ bellVector = 1 := by
  simp only [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [bellVector, bellCoefficients, complex_sqrt_two_inv_mul_self]

private theorem bell_density_rank_one : Matrix.rank bellDensity = 1 := by
  have upper : Matrix.rank bellDensity <= 1 := by
    simpa only [bellDensity] using
      Matrix.rank_vecMulVec_le bellVector (star bellVector)
  have positive : 0 < Matrix.rank bellDensity := by
    rw [Matrix.rank_eq_finrank_span_cols]
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    let index : Fin 2 × Fin 2 := (0, 0)
    let column : Submodule.span Complex (Set.range bellDensity.col) :=
      ⟨bellDensity.col index, Submodule.subset_span ⟨index, rfl⟩⟩
    refine ⟨column, ?_⟩
    intro hzero
    have hvalue := congrFun (congrArg Subtype.val hzero) index
    norm_num [column, index, bellDensity, bellVector, bellCoefficients,
      Matrix.vecMulVec_apply, complex_sqrt_two_inv_mul_self] at hvalue
  exact Nat.le_antisymm upper positive

private theorem bell_marginal :
    traceEnvironment bellDensity = (1 / 2 : Complex) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [traceEnvironment, bellDensity, bellVector, bellCoefficients,
      Matrix.vecMulVec_apply, Fin.sum_univ_two, complex_sqrt_two_inv_mul_self]

private theorem half_identity_not_idempotent :
    let reduced : QubitMatrix := (1 / 2 : Complex) • (1 : QubitMatrix)
    Not (reduced * reduced = reduced) := by
  dsimp only
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The normalized Bell vector constructs a nonzero rank-one, idempotent global
density matrix. Tracing out the second qubit gives exactly one half of the
identity, and that reduced density is not idempotent. -/
theorem bell_pure_state_has_maximally_mixed_marginal :
    star bellVector ⬝ᵥ bellVector = 1 /\
      bellDensity.PosSemidef /\
      Matrix.trace bellDensity = 1 /\
      Matrix.rank bellDensity = 1 /\
      bellDensity * bellDensity = bellDensity /\
      traceEnvironment bellDensity = (1 / 2 : Complex) • (1 : QubitMatrix) /\
      Not (traceEnvironment bellDensity * traceEnvironment bellDensity =
        traceEnvironment bellDensity) := by
  have pure := pure_state_handshake bellVector bell_vector_normalized
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) Complex)
  refine ⟨bell_vector_normalized, bell_density_is_state.1,
    bell_density_is_state.2, bell_density_rank_one, ?_, bell_marginal, ?_⟩
  · simpa only [rankOneDensity, bellDensity] using pure.1
  · rw [bell_marginal]
    exact half_identity_not_idempotent

#print axioms bell_pure_state_has_maximally_mixed_marginal

end D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal
