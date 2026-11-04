/- GID: D5/S3/Quantum/Reduction/PositiveCoarseRefinementRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Reduction/PositiveCoarseRefinementRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Reduction/PositiveCoarseRefinementRefutation.claim; result=D5/S3/Quantum/Reduction/PositiveCoarseRefinementRefutation.result; claim=D5/S3/Quantum/Reduction/PositiveCoarseRefinementRefutation.claim
   digest: A positive two-record refinement of the qubit depolarizing map has a non-CP transpose record. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
namespace D5.S3.Quantum.Reduction.PositiveCoarseRefinementRefutation
set_option autoImplicit false
set_option relaxedAutoImplicit false

private def transpose_half : MatrixMap (Fin 2) (Fin 2) ℂ where
  toFun X := (1 / 2 : ℂ) • Xᵀ
  map_add' X Y := by simp [Matrix.transpose_add, smul_add]
  map_smul' c X := by simp [Matrix.transpose_smul, smul_smul, mul_comm]

private def reduction_half : MatrixMap (Fin 2) (Fin 2) ℂ where
  toFun X := (1 / 2 : ℂ) • ((Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Xᵀ)
  map_add' X Y := by simp [Matrix.trace_add, Matrix.transpose_add, add_smul]; module
  map_smul' c X := by simp [Matrix.trace_smul, Matrix.transpose_smul, smul_sub, smul_smul]; module

private theorem branches_positive : transpose_half.IsPositive ∧ reduction_half.IsPositive := by
  constructor
  · intro X hX
    exact hX.transpose.smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 2)
  · intro X hX
    let U : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;-1,0]
    have he : (Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Xᵀ = U * X * Uᴴ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [U, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          Matrix.smul_apply, Matrix.one_apply, Matrix.vecMul, dotProduct] <;> ring
    change ((1 / 2 : ℂ) • ((Matrix.trace X) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Xᵀ)).PosSemidef
    rw [he]
    exact (hX.mul_mul_conjTranspose_same U).smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 1 / 2)

private theorem branch_effects (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (transpose_half X) = (1 / 2 : ℂ) * Matrix.trace X ∧
    Matrix.trace (reduction_half X) = (1 / 2 : ℂ) * Matrix.trace X := by
  constructor <;> simp [transpose_half, reduction_half, Matrix.trace, Fin.sum_univ_two,
    Matrix.smul_apply, Matrix.one_apply, Matrix.sub_apply] <;> ring

private theorem coarse_cp : (transpose_half + reduction_half).IsCompletelyPositive := by
  let r : ℝ := Real.sqrt (1 / 2)
  have hr : (r : ℂ) * (r : ℂ) = 1 / 2 := by
    have hrR : r * r = (1 / 2 : ℝ) :=
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    calc
      (r : ℂ) * (r : ℂ) = ((r * r : ℝ) : ℂ) := (Complex.ofReal_mul r r).symm
      _ = ((1 / 2 : ℝ) : ℂ) := congrArg Complex.ofReal hrR
      _ = 1 / 2 := by norm_num
  have hr2 : (r : ℂ) ^ 2 = 1 / 2 := by simpa only [pow_two] using hr
  let K : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
    fun ij => (r : ℂ) • Matrix.single ij.1 ij.2 1
  have he : transpose_half + reduction_half = MatrixMap.of_kraus K K := by
    ext X i j
    fin_cases i <;> fin_cases j <;>
      simp [transpose_half, reduction_half, MatrixMap.of_kraus, K,
        Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.single, Matrix.trace, Matrix.one_apply,
        Matrix.smul_apply, mul_add, add_mul, hr] <;> ring_nf <;> simp [hr2]
  rw [he]
  exact MatrixMap.of_kraus_isCompletelyPositive K

private theorem transpose_not_cp : ¬ transpose_half.IsCompletelyPositive := by
  intro h
  let v : Fin 2 × Fin 2 → ℂ := fun i => if i.1 = i.2 then 1 else 0
  let w : Fin 2 × Fin 2 → ℂ := fun i => if i = (0,1) then 1 else if i = (1,0) then -1 else 0
  have hZ := posSemidef_vecMulVec_self_star v
  have hh := (h 2 hZ).dotProduct_mulVec_nonneg w
  norm_num [MatrixMap.kron_def, transpose_half, v, w, dotProduct, Matrix.mulVec,
    Matrix.vecMulVec, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.single,
    Matrix.smul_apply, Matrix.transpose_apply] at hh

/-- Positive fine records of a general completely positive coarse map need
not themselves be completely positive, even with both effects equal to I/2. -/
def claim : Prop := ∀ S T : MatrixMap (Fin 2) (Fin 2) ℂ,
  S.IsPositive → T.IsPositive →
  (∀ X, Matrix.trace (S X) = (1 / 2 : ℂ) * Matrix.trace X ∧
    Matrix.trace (T X) = (1 / 2 : ℂ) * Matrix.trace X) →
  (S + T).IsCompletelyPositive → S.IsCompletelyPositive

theorem result : ¬ claim := by
  intro h
  exact transpose_not_cp (h transpose_half reduction_half branches_positive.1
    branches_positive.2 branch_effects coarse_cp)

#print axioms result
end D5.S3.Quantum.Reduction.PositiveCoarseRefinementRefutation
