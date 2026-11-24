/- GID: D5/S3/Quantum/Matrix/Tensor/KroneckerSqrt
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive square roots of finite complex Kronecker products. -/

import Mathlib.Analysis.Matrix.Order

namespace D5.S3.Quantum.Matrix.Tensor.KroneckerSqrt

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

/-- The positive square root of a Kronecker product of positive semidefinite
matrices is the Kronecker product of their positive square roots. -/
theorem sqrt_kronecker {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (A : (Matrix a a ℂ)) (B : (Matrix b b ℂ))
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (A ⊗ₖ B) = CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  apply CFC.sqrt_unique
  · rw [← Matrix.mul_kronecker_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      CFC.sqrt_mul_sqrt_self B hB.nonneg]
  · exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).kronecker
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))).nonneg

end D5.S3.Quantum.Matrix.Tensor.KroneckerSqrt
