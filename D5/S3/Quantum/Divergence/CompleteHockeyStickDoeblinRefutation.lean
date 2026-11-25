/- GID: D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation.claim; result=D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation.result; claim=D5/S3/Quantum/Divergence/CompleteHockeyStickDoeblinRefutation.claim
   digest: A Hermitian Choi minorant refutes the proposed complete hockey-stick Doeblin bound. -/

import D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation

/-! George–Hirche–Nuradha–Wilde, arXiv:2503.22823v3, Definition 4 and §9.2(1). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.CompleteHockeyStickDoeblinRefutation

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker
open CompleteHockeyStickRefutation (channel completeCoefficient)
open ConditionalHockeyStickOrthogonalReduction (act posSemidef_blockDiagonal)
open D5.S3.Quantum.Foundation.FiniteKrausChannel

open private channel_action ray e₀ b from
  D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation

-- The native Choi matrix is output-first. Swap both indices for the paper's order.
local notation "J" =>
  Matrix.submatrix
    (PhyslibLeaf.MatrixMap.choi_matrix
      (CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
        (channel.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)))
    Prod.swap Prod.swap

private def output (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if i = 0 then !![1, 0; 0, 0] else !![16 / 25, 12 / 25; 12 / 25, 9 / 25]

private def witness : Matrix (Fin 2) (Fin 2) ℂ :=
  !![13 / 25, 6 / 25; 6 / 25, -(3 / 25)]

private theorem choi_block :
    J = (Matrix.blockDiagonal output).submatrix Prod.swap Prod.swap := by
  ext ⟨i, x⟩ ⟨j, y⟩
  change act channel (Matrix.single i j 1) x y = Matrix.blockDiagonal output (x, i) (y, j)
  rw [channel_action]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply,
    ray, Matrix.vecMulVec_apply, Pi.star_apply]
  fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y <;>
    norm_num [Matrix.blockDiagonal_apply, output, e₀, b, map_ofNat, map_div₀]

private theorem output_sub_witness_psd (i : Fin 2) : (output i - witness).PosSemidef := by
  let v : Fin 2 → ℂ := if i = 0 then ![2, -1] else ![1, 2]
  have h : output i - witness = (3 / 25 : ℝ) • vecMulVec v (star v) := by
    ext x y
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      norm_num [output, witness, v, Complex.real_smul, map_ofNat, map_div₀]
  rw [h]
  exact (posSemidef_vecMulVec_self_star v).smul (by norm_num)

/-- The proposed bound at gamma two applied to every feasible Hermitian minorant. -/
def claim : Prop :=
  ∀ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian →
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ H) ≤ J →
    completeCoefficient channel 2 false ≤ 1 - H.trace.re

private theorem certificate :
    ∃ H : Matrix (Fin 2) (Fin 2) ℂ,
      H = !![13 / 25, 6 / 25; 6 / 25, -(3 / 25)] ∧
      H.IsHermitian ∧ H.trace = 2 / 5 ∧
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ H) ≤ J ∧
      1 - H.trace.re < completeCoefficient channel 2 false := by
  have hHerm : witness.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [witness, Matrix.conjTranspose_apply, map_ofNat, map_div₀]
  have htrace : witness.trace = 2 / 5 := by
    norm_num [witness, Matrix.trace, Fin.sum_univ_two]
  refine ⟨witness, rfl, hHerm, htrace, ?_, ?_⟩
  · rw [choi_block, ← sub_nonneg, Matrix.nonneg_iff_posSemidef]
    have hblocks :
        (Matrix.blockDiagonal output).submatrix Prod.swap Prod.swap -
            ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ witness) =
          (Matrix.blockDiagonal (fun i => output i - witness)).submatrix Prod.swap Prod.swap := by
      ext ⟨i, x⟩ ⟨j, y⟩
      by_cases hij : i = j
      · subst j
        simp [Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply]
      · simp [Matrix.blockDiagonal_apply, Matrix.kroneckerMap_apply, hij]
    rw [hblocks, ← Matrix.blockDiagonal'_submatrix_eq_blockDiagonal]
    exact ((posSemidef_blockDiagonal _ output_sub_witness_psd).submatrix
      (Prod.toSigma ∘ Prod.swap)).submatrix Prod.swap
  · rw [htrace]
    norm_num
    linarith [CompleteHockeyStickRefutation.result.2.2]

/-- A feasible Hermitian witness with trace two fifths violates the proposed bound at gamma two. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨H, _, hHerm, _, hChoi, hStrict⟩ := certificate
  exact (not_le_of_gt hStrict) (h H hHerm hChoi)

#print axioms result

end D5.S3.Quantum.Divergence.CompleteHockeyStickDoeblinRefutation
