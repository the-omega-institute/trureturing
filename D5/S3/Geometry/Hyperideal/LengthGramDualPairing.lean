/- GID: D5/S3/Geometry/Hyperideal/LengthGramDualPairing
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramDualPairing
   mirror-E: none(waiver:dual-pairing)
   anchors: []
   utility: none
   digest: The inverse-Gram dual vectors pair with the realizing rows by Kronecker delta. -/

import D5.S3.Geometry.Hyperideal.LengthGramBody
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Inverse-Gram dual vectors are paired with the realizing rows by the Kronecker delta. -/

noncomputable section
open scoped BigOperators Matrix
open D5.S3.Geometry.Hyperideal.LengthGramBody
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.LengthGramDualPairing

def dualVector (G M : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : Fin 4 → ℝ :=
  (G⁻¹ i) ᵥ* M

theorem dual_pairing
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j,
      lorentz (M i) (M j) = lengthGram l i j)
    (hdet : (lengthGram l).det < 0) (i j : Fin 4) :
    lorentz (dualVector (lengthGram l) M i) (M j) = if i = j then 1 else 0 := by
  have hdetne : (lengthGram l).det ≠ 0 := ne_of_lt hdet
  have hinv : (lengthGram l)⁻¹ * lengthGram l = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdetne)
  have hentry : ∑ k, (lengthGram l)⁻¹ i k * lengthGram l k j =
      if i = j then 1 else 0 := by
    have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) hinv
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  unfold dualVector lorentz
  simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  calc
    ∑ x, ∑ k, ![(1 : ℝ), 1, 1, -1] x *
        ((lengthGram l)⁻¹ i k * M k x) * M j x =
      ∑ k, (lengthGram l)⁻¹ i k *
        (∑ x, ![(1 : ℝ), 1, 1, -1] x * M k x * M j x) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = ∑ k, (lengthGram l)⁻¹ i k * lengthGram l k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← hM k j]
      rfl
    _ = if i = j then 1 else 0 := hentry

#print axioms dual_pairing
end D5.S3.Geometry.Hyperideal.LengthGramDualPairing
