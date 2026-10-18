/- GID: D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/StrongSubadditivityRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.conjecture; result=D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.result; claim=D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.conjecture
   digest: Canonical density states and partial traces for a Bell pair with an independent qubit. -/

import D5.S3.Quantum.Subentropy.Basic
import D5.S3.Quantum.Subentropy.UniformValues
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal

/-! Density-state relabelling and the exact marginals of the Bell-pair witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation

open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.QuantumBounds.CHSHWitness
open D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.UniformValues

/-- Relabel a density matrix by a bijection, without changing its entries. -/
def reindexState {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (rho : DensityState A) : DensityState B := by
  refine ⟨CStarMatrix.ofMatrix
    ((CStarMatrix.ofMatrix.symm rho.1).submatrix e.symm e.symm), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((density_posSemidef rho).submatrix e.symm).nonneg
  · change (∑ b : B, rho.1 (e.symm b) (e.symm b)) = 1
    exact (e.symm.sum_comp (fun a : A =>
      (CStarMatrix.ofMatrix.symm rho.1) a a)).trans rho.2.2

/-- The associativity bijection only changes the grouping of subsystem labels. -/
def reassocState {A B C : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (rho : DensityState ((A × B) × C)) : DensityState (A × (B × C)) :=
  reindexState (Equiv.prodAssoc A B C) rho

/-- The maximally mixed qubit density. -/
def uniformTwo : DensityState (Fin 2) := by
  refine ⟨CStarMatrix.ofMatrix (Matrix.diagonal fun _ : Fin 2 => (1 / 2 : ℂ)), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact (Matrix.PosSemidef.diagonal (fun _ => by norm_num [Complex.le_def])).nonneg
  · change Matrix.trace (Matrix.diagonal fun _ : Fin 2 => (1 / 2 : ℂ)) = 1
    norm_num [Matrix.trace, Fin.sum_univ_two]

/-- The existing normalized Bell density, packaged in the canonical state carrier. -/
def bellState : DensityState (Fin 2 × Fin 2) :=
  ⟨CStarMatrix.ofMatrix bellDensity,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv bell_density_is_state.1.nonneg,
    bell_density_is_state.2⟩

/-- A Bell pair on the first two qubits and an independent maximally mixed third qubit. -/
def witness : DensityState ((Fin 2 × Fin 2) × Fin 2) :=
  productState bellState uniformTwo

/-- Tracing out the first Bell qubit leaves the maximally mixed second qubit. -/
private theorem marginalLeft_bellState : marginalLeft bellState = uniformTwo := by
  have h := bell_pure_state_has_maximally_mixed_marginal
  have hright := h.2.2.2.2.2.1
  apply Subtype.ext
  apply congrArg CStarMatrix.ofMatrix
  change partialTraceLeft bellDensity = Matrix.diagonal (fun _ : Fin 2 => (1 / 2 : ℂ))
  have hsym : partialTraceLeft bellDensity = partialTraceRight bellDensity := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [partialTraceLeft, partialTraceRight, Fin.sum_univ_two,
        bellDensity, bellVector, D5.S3.Quantum.QubitWitnesses.bellCoefficients,
        Matrix.vecMulVec_apply]
  rw [hsym]
  change D5.S3.Quantum.EnvironmentRecords.traceEnvironment bellDensity = _
  rw [hright]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- An independent third subsystem stays independent after tracing out the first one. -/
private theorem marginalLeft_reassoc_productState {A B C : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (rho : DensityState (A × B)) (sigma : DensityState C) :
    marginalLeft (reassocState (productState rho sigma)) =
      productState (marginalLeft rho) sigma := by
  apply Subtype.ext
  apply congrArg CStarMatrix.ofMatrix
  ext ⟨b, c⟩ ⟨d, e⟩
  change (∑ a : A, rho.1 (a, b) (a, d) * sigma.1 c e) =
    (∑ a : A, rho.1 (a, b) (a, d)) * sigma.1 c e
  exact (Finset.sum_mul ..).symm

/-- The three marginal states of the Bell-pair counterexample. -/
private theorem witness_marginals :
    marginalRight witness = bellState ∧
      marginalLeft (marginalRight witness) = uniformTwo ∧
      marginalLeft (reassocState witness) = productState uniformTwo uniformTwo := by
  have hab : marginalRight witness = bellState :=
    marginalRight_productState bellState uniformTwo
  refine ⟨hab, ?_, ?_⟩
  · exact (congrArg marginalLeft hab).trans marginalLeft_bellState
  · exact (marginalLeft_reassoc_productState bellState uniformTwo).trans
      (congrArg (fun rho : DensityState (Fin 2) => productState rho uniformTwo)
        marginalLeft_bellState)

private theorem uniform_product_matrix :
    CStarMatrix.ofMatrix.symm (productState uniformTwo uniformTwo).1 =
      Matrix.diagonal (fun _ : Fin 2 × Fin 2 => (1 / 4 : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [uniformTwo, productState, Matrix.kroneckerMap_apply,
      CStarMatrix.ofMatrix_apply]

/-- The Bell pair embeds a third-qubit amplitude isometrically into three qubits. -/
private def bellEmbedding : Matrix ((Fin 2 × Fin 2) × Fin 2) (Fin 2) ℂ :=
  fun row col => if row.2 = col then bellVector row.1 else 0

private theorem bellEmbedding_isometry :
    bellEmbedding.conjTranspose * bellEmbedding = 1 := by
  have hv : (∑ i, star (bellVector i) * bellVector i) = 1 :=
    bell_pure_state_has_maximally_mixed_marginal.1
  ext c d
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, bellEmbedding,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    simpa [Fintype.sum_prod_type, Fin.sum_univ_two] using hv

private theorem witness_isometric :
    CStarMatrix.ofMatrix.symm witness.1 =
      bellEmbedding * (CStarMatrix.ofMatrix.symm uniformTwo.1) *
        bellEmbedding.conjTranspose := by
  ext ⟨ij, c⟩ ⟨kl, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [witness, productState, bellState, uniformTwo,
      Matrix.mul_apply, Matrix.conjTranspose_apply, bellEmbedding,
      Fin.sum_univ_two, bellDensity, Matrix.vecMulVec_apply,
      Matrix.kroneckerMap_apply, CStarMatrix.ofMatrix_apply] <;> ring

/-- Strong subadditivity for the determinant-integral subentropy and the canonical marginals. -/
def conjecture : Prop :=
  ∀ (A B C : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (rho : DensityState ((A × B) × C)),
    subentropy rho + subentropy (marginalLeft (marginalRight rho)) ≤
      subentropy (marginalRight rho) + subentropy (marginalLeft (reassocState rho))

private theorem witness_gap :
    subentropy witness + subentropy (marginalLeft (marginalRight witness)) -
      (subentropy (marginalRight witness) + subentropy (marginalLeft (reassocState witness))) =
        1 / 12 := by
  have hu : subentropy uniformTwo = Real.log 2 - 1 / 2 := by
    simpa [subentropy, uniformTwo] using
      (subentropy_uniformTwo (ι := Fin 2) (by decide))
  have hpure : subentropy bellState = 0 := by
    unfold subentropy
    change matrixSubentropy bellDensity = 0
    exact matrixSubentropy_pure bellVector
      bell_pure_state_has_maximally_mixed_marginal.1
  have hw : subentropy witness = subentropy uniformTwo := by
    unfold subentropy
    rw [witness_isometric]
    exact matrixSubentropy_isometric_embedding _ _ bellEmbedding_isometry
  have hfour : subentropy (productState uniformTwo uniformTwo) = Real.log 4 - 13 / 12 := by
    unfold subentropy
    rw [uniform_product_matrix]
    simpa using (subentropy_uniformFour (ι := Fin 2 × Fin 2) (by decide))
  have hlog : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rcases witness_marginals with ⟨hab, hb, hbc⟩
  rw [hb, hab, hbc, hw, hu, hpure, hfour, hlog]
  ring

/-- The Bell-pair witness violates strong subadditivity by exactly one twelfth. -/
theorem result : ¬ conjecture := by
  intro h
  have hssa := h (Fin 2) (Fin 2) (Fin 2) witness
  have hgap := witness_gap
  linarith

end D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation
