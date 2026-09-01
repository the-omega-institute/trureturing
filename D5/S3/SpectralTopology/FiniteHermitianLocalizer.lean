/- GID: D5/S3/SpectralTopology/FiniteHermitianLocalizer
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/FiniteHermitianLocalizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite block localizer is Hermitian and its zero-position-scale square splits into the two singular Gram blocks. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# Finite Hermitian spectral localizer

For a finite Hermitian position matrix `X`, a possibly non-Hermitian operator
`H`, a spatial center `x`, spectral point `z`, and real localization scale
`kappa`, define the block matrix

`L = [[kappa (X-xI), H-zI], [(H-zI)ᴴ, -kappa (X-xI)]]`.

The localizer is Hermitian.  At zero position scale its square is block
diagonal with the two singular Gram matrices `B Bᴴ` and `Bᴴ B`, where
`B = H-zI`.  This is the finite algebraic entry point for point-gap topology.

This file does not define a bulk invariant, prove a bulk-boundary theorem,
identify a K-theory class, or establish perturbation stability of the
localizer signature.  Those are later finite layers.
-/

/- Library-search audit trail (2026-09-01):
   * `HorizonEffectiveIndex` owns singular values and the contraction defect
     `I-HᴴH`, but no spatial-spectral block localizer.
   * `HermitianKernelNegativeSquares` and `RHLinalg.negIndex` own finite
     Hermitian inertia tools, not the localizer below.
   * Repository search found no owner of a point-gap block localizer or its
     zero-scale singular-Gram square identity.
   * Pinned Mathlib supplies Hermitian matrices, block matrices, conjugate
     transpose, and block multiplication. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.SpectralTopology.FiniteHermitianLocalizer

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Hermitian spatial block at center `x` and localization scale `kappa`. -/
def positionBlock
    (kappa x : ℝ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (kappa : ℂ) • (X - (x : ℂ) • 1)

/-- Point-gap defect of `H` at the complex spectral point `z`. -/
def pointGapBlock
    (H : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  H - z • 1

/-- Finite one-dimensional Hermitian spectral localizer. -/
def finiteHermitianLocalizer
    (kappa x : ℝ) (X H : Matrix n n ℂ) (z : ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks
    (positionBlock kappa x X)
    (pointGapBlock H z)
    (pointGapBlock H z)ᴴ
    (-positionBlock kappa x X)

/-- The spatial block is Hermitian when the position matrix is Hermitian. -/
theorem positionBlock_isHermitian
    (kappa x : ℝ) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (positionBlock kappa x X).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [positionBlock, Matrix.one_apply, hX i j]

/-- The finite block localizer is Hermitian. -/
theorem finiteHermitianLocalizer_isHermitian
    (kappa x : ℝ) {X : Matrix n n ℂ} (hX : X.IsHermitian)
    (H : Matrix n n ℂ) (z : ℂ) :
    (finiteHermitianLocalizer kappa x X H z).IsHermitian := by
  let hPosition := positionBlock_isHermitian kappa x hX
  apply Matrix.IsHermitian.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [finiteHermitianLocalizer] using hPosition i j
  · simp [finiteHermitianLocalizer, pointGapBlock]
  · simp [finiteHermitianLocalizer, pointGapBlock]
  · simpa [finiteHermitianLocalizer] using congrArg Neg.neg (hPosition i j)

/-- At zero position scale the diagonal spatial blocks vanish. -/
theorem finiteHermitianLocalizer_zero_scale
    (x : ℝ) (X H : Matrix n n ℂ) (z : ℂ) :
    finiteHermitianLocalizer 0 x X H z =
      Matrix.fromBlocks 0 (pointGapBlock H z)
        (pointGapBlock H z)ᴴ 0 := by
  simp [finiteHermitianLocalizer, positionBlock]

/-- The square of the zero-scale localizer is the block diagonal pair of
left and right singular Gram matrices. -/
theorem finiteHermitianLocalizer_zero_scale_sq
    (x : ℝ) (X H : Matrix n n ℂ) (z : ℂ) :
    finiteHermitianLocalizer 0 x X H z *
        finiteHermitianLocalizer 0 x X H z =
      Matrix.fromBlocks
        (pointGapBlock H z * (pointGapBlock H z)ᴴ) 0 0
        ((pointGapBlock H z)ᴴ * pointGapBlock H z) := by
  rw [finiteHermitianLocalizer_zero_scale,
    Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

/-- The zero-scale localizer vanishes only when the point-gap block vanishes. -/
theorem finiteHermitianLocalizer_zero_scale_eq_zero_iff
    (x : ℝ) (X H : Matrix n n ℂ) (z : ℂ) :
    finiteHermitianLocalizer 0 x X H z = 0 ↔
      pointGapBlock H z = 0 := by
  rw [finiteHermitianLocalizer_zero_scale]
  constructor
  · intro h
    ext i j
    have hij := congr_fun (congr_fun h (Sum.inl i)) (Sum.inr j)
    simpa using hij
  · intro h
    simp [h]

example :
    (finiteHermitianLocalizer 0 0
      (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0) = 0 := by
  simp [finiteHermitianLocalizer, positionBlock, pointGapBlock]

#print axioms positionBlock_isHermitian
#print axioms finiteHermitianLocalizer_isHermitian
#print axioms finiteHermitianLocalizer_zero_scale
#print axioms finiteHermitianLocalizer_zero_scale_sq
#print axioms finiteHermitianLocalizer_zero_scale_eq_zero_iff

end

end D5.S3.SpectralTopology.FiniteHermitianLocalizer
