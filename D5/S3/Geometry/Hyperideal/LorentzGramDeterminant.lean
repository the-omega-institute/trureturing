/- GID: D5/S3/Geometry/Hyperideal/LorentzGramDeterminant
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LorentzGramDeterminant
   mirror-E: none(waiver:lorentz-gram-determinant)
   anchors: []
   utility: none
   digest: Lorentz Gram determinant is the negative square of the realizing determinant. -/

import D5.S3.Geometry.Hyperideal.LengthGramBody
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! The determinant of a four-dimensional Lorentz Gram matrix is a negative square. -/

open scoped Matrix
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.LorentzGramDeterminant

def lorentzMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![(1 : ℝ), 1, 1, -1]

theorem lorentz_gram_determinant
    (M G : Matrix (Fin 4) (Fin 4) ℝ)
    (hG : ∀ i j, D5.S3.Geometry.Hyperideal.LengthGramBody.lorentz (M i) (M j) = G i j) :
    G.det = -(M.det)^2 := by
  have hfactor : G = M * lorentzMatrix * M.transpose := by
    ext i j
    symm
    simpa [Matrix.mul_apply, Matrix.transpose_apply, lorentzMatrix,
      D5.S3.Geometry.Hyperideal.LengthGramBody.lorentz,
      Fin.sum_univ_succ] using hG i j
  rw [hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hdet : lorentzMatrix.det = -(1 : ℝ) := by
    simp [lorentzMatrix, Matrix.det_diagonal, Fin.prod_univ_succ]
  rw [hdet]
  ring

theorem length_gram_determinant_factorization
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j,
      D5.S3.Geometry.Hyperideal.LengthGramBody.lorentz (M i) (M j) =
        D5.S3.Geometry.Hyperideal.LengthGramBody.lengthGram l i j) :
    (D5.S3.Geometry.Hyperideal.LengthGramBody.lengthGram l).det = -(M.det)^2 := by
  apply lorentz_gram_determinant M
    (D5.S3.Geometry.Hyperideal.LengthGramBody.lengthGram l)
  exact hM

#print axioms lorentz_gram_determinant
#print axioms length_gram_determinant_factorization

end D5.S3.Geometry.Hyperideal.LorentzGramDeterminant

