/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48pFramePositive
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48pFramePositive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The checked norm-twelve frame proves positivity of the P48p catalogue Gram. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSyndromeFrame
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive definiteness of the P48p catalogue Gram matrix

Let `G` be the catalogue Gram matrix, `U` the norm-twelve frame rows, and
`F = G * Uᵀ` the pairing matrix. After casting to the reals, the checked
identity `U * F = 12 • 1` makes `F` invertible. The identity
`F * Fᵀ = 12 • G` then expresses `G` as a positive scalar multiple of
a positive definite matrix.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSyndromeFrame

open scoped Matrix

/-- The concrete P48p Gram matrix is positive definite over the reals. -/
theorem p48pGram_posDef : Matrix.PosDef (p48pGram.map (Int.cast : ℤ → ℝ)) := by
  let cast : Matrix (Fin 48) (Fin 48) ℤ →+* Matrix (Fin 48) (Fin 48) ℝ :=
    (Int.castRingHom ℝ).mapMatrix
  have cast_smul (A : Matrix (Fin 48) (Fin 48) ℤ) :
      cast ((12 : ℤ) • A) = (12 : ℝ) • cast A := by
    ext i j
    change (↑((12 : ℤ) • A i j) : ℝ) = (12 : ℝ) • (A i j : ℝ)
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, smul_eq_mul]
  have cast_transpose (A : Matrix (Fin 48) (Fin 48) ℤ) :
      cast Aᵀ = (cast A)ᵀ := rfl
  let U := cast p48pFrameRows
  let F := cast p48pPairingFrame
  have hUF : U * F = (12 : ℝ) • 1 := by
    have h := p48pFrameRows_orthogonal
    rw [Matrix.mul_assoc, ← p48pPairingFrame_eq] at h
    simpa only [map_mul, cast_smul, map_one] using congrArg cast h
  have h12 : (0 : ℝ) < 12 := by norm_num
  have hF : IsUnit F := isUnit_iff_exists_inv'.2 ⟨(12 : ℝ)⁻¹ • U, by
    rw [Matrix.smul_mul, hUF, smul_smul, inv_mul_cancel₀ h12.ne', one_smul]⟩
  have hGram : F * Fᵀ = (12 : ℝ) • cast p48pGram := by
    simpa only [map_mul, cast_transpose, cast_smul] using
      congrArg cast p48pPairingFrame_mul_transpose
  have hPos : Matrix.PosDef (F * Fᵀ) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.mul_conjTranspose_self F (Matrix.vecMul_injective_of_isUnit hF)
  rw [hGram] at hPos
  change Matrix.PosDef (cast p48pGram)
  simpa only [smul_smul, inv_mul_cancel₀ h12.ne', one_smul] using hPos.smul (inv_pos.mpr h12)

#print axioms p48pGram_posDef

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSyndromeFrame
