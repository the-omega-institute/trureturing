/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48pFrameUnimodular
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48pFrameUnimodular
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The norm-twelve catalogue frame gives an integral inverse for the P48p Gram matrix. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSyndromeFrame
import D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero

/-!
# Unimodularity of the P48p Gram matrix

The column dot products of the catalogue frame are divisible by twelve. Dividing
them by twelve gives the integral Gram inverse, and frame orthogonality fixes the
sign of the determinant.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameUnimodular

open scoped Matrix
open P48pSyndromeFrame (p48pFrameRows p48pGram p48pFrameRows_orthogonal p48pCatalogueData)
open HalfFockSpectralFiberSource (actualInverse)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
-- Kernel reduction checks all 48 column dot products for each fixed column.
/-- Each column dot product of the catalogue frame is divisible by twelve. -/
theorem p48pFrame_column_dot_dvd (i j : Fin 48) :
    (12 : ℤ) ∣ (p48pFrameRowsᵀ * p48pFrameRows) i j := by
  have hRow : List.ofFn (fun c : Fin 48 =>
      (List.ofFn (fun r : Fin 48 => p48pFrameRows r i * p48pFrameRows r c)).sum % 12) =
      List.ofFn (fun _ : Fin 48 => (0 : ℤ)) := by
    fin_cases i <;> decide +kernel
  rw [Int.dvd_iff_emod_eq_zero]
  simpa only [List.sum_ofFn, Matrix.mul_apply, Matrix.transpose_apply] using
    congrFun (List.ofFn_injective hRow) j

/-- The integral Gram inverse, computed by dividing the column dot products by twelve. -/
def p48pGramInverse : Matrix (Fin 48) (Fin 48) ℤ :=
  fun i j => (p48pFrameRowsᵀ * p48pFrameRows) i j / 12

private theorem twelve_smul_gramInverse :
    (12 : ℤ) • p48pGramInverse = p48pFrameRowsᵀ * p48pFrameRows := by
  apply Matrix.ext
  intro i j
  exact Int.mul_ediv_cancel_of_dvd (p48pFrame_column_dot_dvd i j)

private theorem frame_det_identity :
    p48pFrameRows.det * p48pGram.det * p48pFrameRows.det =
      (12 : ℤ) ^ Fintype.card (Fin 48) := by
  simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one]
    using congrArg Matrix.det p48pFrameRows_orthogonal

/-- Multiplying the frame-derived inverse on the right gives the identity over ℤ. -/
theorem p48pGram_mul_inverse : p48pGram * p48pGramInverse = 1 := by
  have hFrameDet : p48pFrameRows.det ≠ 0 := by
    intro h
    apply pow_ne_zero (Fintype.card (Fin 48)) (by decide : (12 : ℤ) ≠ 0)
    simpa only [h, zero_mul] using frame_det_identity.symm
  have hFrameRegular : IsRegular p48pFrameRows :=
    Matrix.isRegular_of_isLeftRegular_det (fun _ _ h => mul_left_cancel₀ hFrameDet h)
  have hScaled : (12 : ℤ) • (p48pFrameRows * (p48pGram * p48pGramInverse)) =
      (12 : ℤ) • p48pFrameRows := by
    calc
      _ = (p48pFrameRows * p48pGram) * ((12 : ℤ) • p48pGramInverse) := by
        rw [Matrix.mul_smul, Matrix.mul_assoc p48pFrameRows p48pGram p48pGramInverse]
      _ = (p48pFrameRows * p48pGram * p48pFrameRowsᵀ) * p48pFrameRows := by
        rw [twelve_smul_gramInverse, ← Matrix.mul_assoc]
      _ = _ := by rw [p48pFrameRows_orthogonal, Matrix.smul_mul, Matrix.one_mul]
  apply hFrameRegular.left
  change p48pFrameRows * (p48pGram * p48pGramInverse) = p48pFrameRows * 1
  rw [Matrix.mul_one]
  exact Matrix.ext fun i j =>
    mul_left_cancel₀ (by decide : (12 : ℤ) ≠ 0) (congrFun (congrFun hScaled i) j)

/-- Multiplying the frame-derived inverse on the left gives the identity over ℤ. -/
theorem p48pGram_inverse_mul : p48pGramInverse * p48pGram = 1 :=
  mul_eq_one_comm.mp p48pGram_mul_inverse

theorem p48pGram_det_isUnit : IsUnit p48pGram.det :=
  Matrix.isUnit_det_of_right_inverse p48pGram_mul_inverse

/-- Frame orthogonality fixes the positive sign of the unit determinant. -/
theorem p48pGram_det_eq_one : p48pGram.det = 1 := by
  have hPos : 0 < p48pGram.det := by
    by_contra! hNonpos
    have hProduct : p48pFrameRows.det * p48pGram.det * p48pFrameRows.det ≤ 0 := by
      rw [mul_right_comm p48pFrameRows.det p48pGram.det p48pFrameRows.det]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) hNonpos
    rw [frame_det_identity] at hProduct
    exact (not_le_of_gt (pow_pos (by decide : (0 : ℤ) < 12) _)) hProduct
  rcases Int.isUnit_iff.mp p48pGram_det_isUnit with h | h
  · exact h
  · rw [h] at hPos
    exact False.elim ((by decide : ¬ (0 : ℤ) < -1) hPos)

/-- The lattice construction's complex inverse is the cast of the frame-derived inverse. -/
theorem p48p_actualInverse_eq :
    actualInverse p48pCatalogueData = p48pGramInverse.map (Int.castRingHom ℂ) := by
  change (p48pGram⁻¹).map (Int.castRingHom ℂ) = _
  rw [Matrix.inv_eq_right_inv p48pGram_mul_inverse]

#print axioms p48pFrame_column_dot_dvd
#print axioms p48pGramInverse
#print axioms p48pGram_mul_inverse
#print axioms p48pGram_inverse_mul
#print axioms p48pGram_det_isUnit
#print axioms p48pGram_det_eq_one
#print axioms p48p_actualInverse_eq

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameUnimodular
