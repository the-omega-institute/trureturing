/- GID: D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.claim; result=D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.result; claim=D5/S3/Quantum/Information/ConditionalDomainSubalgebraRefutation.claim
   digest: Two-qubit conditional domains need not be closed under multiplication. -/

import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Foundation.FiniteStateChannel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Information.ConditionalDomainSubalgebraRefutation

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

/-- The conditional domain in the second tensor factor, as in Definition 5.5. -/
def conditionalDomainB (ν : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {B | Commute (partialTraceRight ν) (partialTraceRight (ν * (1 ⊗ₖ B)))}

/-- The conditional domain in the first tensor factor, as in Definition 5.5. -/
def conditionalDomainA (ν : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {A | Commute (partialTraceLeft ν) (partialTraceLeft ((A ⊗ₖ 1) * ν))}

/-- The two-qubit subalgebra suspicion in footnote 13 of arXiv:2102.01529v3. -/
def claim : Prop :=
  ∀ ν : DensityState (Fin 2 × Fin 2),
    IsUnit (partialTraceRight ν.1) → IsUnit (partialTraceLeft ν.1) →
    ∃ S T : StarSubalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ),
      (S : Set _) = conditionalDomainB ν.1 ∧ (T : Set _) = conditionalDomainA ν.1

private def witnessMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q =>
    !![!![(11 : ℂ), 1; 1, 7], !![1, 0; 0, -1];
       !![1, 0; 0, -1], !![9, -1; -1, 5]] p.1 q.1 p.2 q.2 / 32

private def gramRows (k : Fin 4) (p : Fin 2 × Fin 2) : ℂ :=
  ![!![(1 : ℂ), 1; 0, 0], !![1, 0; 1, 0],
    !![0, 1; 0, -1], !![0, 0; 1, -1]] k p.1 p.2

private def diagonalWeights (p : Fin 2 × Fin 2) : ℂ :=
  !![(9 : ℂ), 5; 7, 3] p.1 p.2

private theorem witness_gram : witnessMatrix = (1 / 32 : ℝ) •
    (Matrix.diagonal diagonalWeights +
      ∑ k : Fin 4, Matrix.vecMulVec (gramRows k) (star (gramRows k))) := by
  ext p q
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [witnessMatrix.eq_1, diagonalWeights.eq_1, gramRows.eq_1, Matrix.diagonal_apply,
      Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Pi.star_apply, Fin.sum_univ_four, smul_eq_mul, Matrix.cons_val_two,
      Matrix.cons_val_three]

private theorem witness_positive : witnessMatrix.PosSemidef := by
  rw [witness_gram]
  apply Matrix.PosSemidef.smul _ (by norm_num : (0 : ℝ) ≤ 1 / 32)
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.diagonal
    intro p
    rcases p with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      apply Complex.nonneg_iff.mpr <;> norm_num [diagonalWeights.eq_1]
  · exact Matrix.posSemidef_sum Finset.univ
      (fun k _ => Matrix.posSemidef_vecMulVec_self_star (gramRows k))

private theorem witness_marginal_right :
    partialTraceRight witnessMatrix = !![(9 / 16 : ℂ), 0; 0, 7 / 16] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceRight, witnessMatrix.eq_1, Fin.sum_univ_two]

private theorem witness_marginal_left :
    partialTraceLeft witnessMatrix = !![(5 / 8 : ℂ), 0; 0, 3 / 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceLeft, witnessMatrix.eq_1, Fin.sum_univ_two]

private theorem witness_trace : Matrix.trace witnessMatrix = 1 := by
  rw [← trace_partialTraceRight, witness_marginal_right]
  norm_num [Matrix.trace, Fin.sum_univ_two]

private def witnessState : DensityState (Fin 2 × Fin 2) :=
  ⟨CStarMatrix.ofMatrix witnessMatrix,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv witness_positive.nonneg, witness_trace⟩

private theorem witness_right_unit : IsUnit (partialTraceRight witnessMatrix) := by
  rw [witness_marginal_right, Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  norm_num [Matrix.det_fin_two]

private theorem witness_left_unit : IsUnit (partialTraceLeft witnessMatrix) := by
  rw [witness_marginal_left, Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  norm_num [Matrix.det_fin_two]

private theorem witness_transform (B : Matrix (Fin 2) (Fin 2) ℂ) :
    partialTraceRight (witnessMatrix * (1 ⊗ₖ B)) =
      !![(11 * B 0 0 + B 0 1 + B 1 0 + 7 * B 1 1) / 32, (B 0 0 - B 1 1) / 32;
         (B 0 0 - B 1 1) / 32, (9 * B 0 0 - B 0 1 - B 1 0 + 5 * B 1 1) / 32] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTraceRight, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, witnessMatrix.eq_1] <;> ring

private theorem witness_upper_mem :
    Matrix.single 0 1 (1 : ℂ) ∈ conditionalDomainB witnessMatrix := by
  change Commute _ _
  rw [witness_marginal_right, witness_transform]
  simpa [Matrix.diagonal_fin_two, Matrix.single_apply] using
    (Matrix.commute_diagonal ![(9 / 16 : ℂ), 7 / 16] ![(1 / 32 : ℂ), -1 / 32])

private theorem witness_lower_mem :
    Matrix.single 1 0 (1 : ℂ) ∈ conditionalDomainB witnessMatrix := by
  change Commute _ _
  rw [witness_marginal_right, witness_transform]
  simpa [Matrix.diagonal_fin_two, Matrix.single_apply] using
    (Matrix.commute_diagonal ![(9 / 16 : ℂ), 7 / 16] ![(1 / 32 : ℂ), -1 / 32])

private theorem witness_corner_not_mem :
    Matrix.single 0 0 (1 : ℂ) ∉ conditionalDomainB witnessMatrix := by
  intro h
  change Commute _ _ at h
  rw [witness_marginal_right, witness_transform] at h
  have entry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h.eq
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply] at entry

private theorem witness_no_subalgebra :
    ¬ ∃ S : StarSubalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ),
      (S : Set _) = conditionalDomainB witnessMatrix := by
  rintro ⟨S, hS⟩
  have upper : Matrix.single 0 1 (1 : ℂ) ∈ S := by
    rw [← SetLike.mem_coe, hS]
    exact witness_upper_mem
  have lower : Matrix.single 1 0 (1 : ℂ) ∈ S := by
    rw [← SetLike.mem_coe, hS]
    exact witness_lower_mem
  have corner : Matrix.single 0 1 (1 : ℂ) * Matrix.single 1 0 (1 : ℂ) ∈ S :=
    S.mul_mem upper lower
  rw [Matrix.single_mul_single_same, one_mul] at corner
  apply witness_corner_not_mem
  rw [← hS]
  exact corner

/-- A positive two-qubit state with invertible marginals refutes the suspicion. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨S, T, hS, _⟩ := h witnessState witness_right_unit witness_left_unit
  exact witness_no_subalgebra ⟨S, hS⟩

end D5.S3.Quantum.Information.ConditionalDomainSubalgebraRefutation
