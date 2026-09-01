/- GID: D5/S3/SpectralTopology/FinitePointGapLocalizer
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/FinitePointGapLocalizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite point-gap unit gives an explicit inverse for the zero-scale Hermitian localizer. -/

import D5.S3.SpectralTopology.FiniteHermitianLocalizer
import Mathlib.Tactic

/-!
# Finite point-gap localizer

A finite operator has a point gap at `z` when `H-zI` is a unit in the finite
matrix ring.  The corresponding zero-position-scale localizer

`[[0,B],[Bᴴ,0]]`

has the explicit inverse

`[[0,(B⁻¹)ᴴ],[B⁻¹,0]]`.

Thus every finite point gap opens a Hermitian localizer gap.  This direction is
purely algebraic and does not require normality of `H`.

The reverse implication, quantitative smallest-singular-value estimates, and
homotopy stability of a signature index are intentionally separated into the
next finite layers.
-/

/- Library-search audit trail (2026-09-01):
   * `FiniteHermitianLocalizer` owns the block localizer and its zero-scale
     square decomposition.
   * `HorizonEffectiveIndex` owns singular-value contraction defects, but not
     point gaps at a general complex spectral point.
   * Repository search found no explicit inverse for the off-diagonal
     point-gap localizer.
   * Pinned Mathlib supplies matrix units, conjugate transpose of products,
     and block multiplication. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.SpectralTopology.FinitePointGapLocalizer

open D5.S3.SpectralTopology.FiniteHermitianLocalizer

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- A finite point gap means that the shifted operator is a matrix unit. -/
def HasFinitePointGap (H : Matrix n n ℂ) (z : ℂ) : Prop :=
  IsUnit (pointGapBlock H z)

/-- Off-diagonal Hermitian localizer attached directly to a matrix block. -/
def offDiagonalLocalizer (block : Matrix n n ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 0 block blockᴴ 0

/-- Explicit inverse built from a unit point-gap block. -/
def offDiagonalLocalizerInverse
    (block : (Matrix n n ℂ)ˣ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 0 ((block⁻¹ : Matrix n n ℂ)ᴴ)
    (block⁻¹ : Matrix n n ℂ) 0

/-- The point-gap localizer times its explicit inverse is the identity. -/
theorem offDiagonalLocalizer_mul_inverse
    (block : (Matrix n n ℂ)ˣ) :
    offDiagonalLocalizer (block : Matrix n n ℂ) *
        offDiagonalLocalizerInverse block = 1 := by
  rw [offDiagonalLocalizer, offDiagonalLocalizerInverse,
    Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

/-- The explicit inverse times the point-gap localizer is the identity. -/
theorem offDiagonalLocalizer_inverse_mul
    (block : (Matrix n n ℂ)ˣ) :
    offDiagonalLocalizerInverse block *
        offDiagonalLocalizer (block : Matrix n n ℂ) = 1 := by
  rw [offDiagonalLocalizer, offDiagonalLocalizerInverse,
    Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

/-- The off-diagonal localizer of a matrix unit is itself a unit. -/
def offDiagonalLocalizerUnit
    (block : (Matrix n n ℂ)ˣ) :
    (Matrix (n ⊕ n) (n ⊕ n) ℂ)ˣ where
  val := offDiagonalLocalizer (block : Matrix n n ℂ)
  inv := offDiagonalLocalizerInverse block
  val_inv := offDiagonalLocalizer_mul_inverse block
  inv_val := offDiagonalLocalizer_inverse_mul block

/-- A finite point gap opens the zero-position-scale Hermitian localizer gap. -/
theorem zero_scale_localizer_isUnit_of_pointGap
    (x : ℝ) (X H : Matrix n n ℂ) (z : ℂ)
    (hGap : HasFinitePointGap H z) :
    IsUnit (finiteHermitianLocalizer 0 x X H z) := by
  let block : (Matrix n n ℂ)ˣ := hGap.unit
  refine ⟨offDiagonalLocalizerUnit block, ?_⟩
  change offDiagonalLocalizer (block : Matrix n n ℂ) =
    finiteHermitianLocalizer 0 x X H z
  rw [finiteHermitianLocalizer_zero_scale]
  rw [hGap.unit_spec]
  rfl

/-- The inverse of the zero-scale localizer is the off-diagonal matrix formed
from the inverse point-gap block. -/
theorem zero_scale_localizer_explicit_inverse
    (x : ℝ) (X H : Matrix n n ℂ) (z : ℂ)
    (hGap : HasFinitePointGap H z) :
    finiteHermitianLocalizer 0 x X H z *
        offDiagonalLocalizerInverse hGap.unit = 1 ∧
      offDiagonalLocalizerInverse hGap.unit *
        finiteHermitianLocalizer 0 x X H z = 1 := by
  have hLocalizer :
      finiteHermitianLocalizer 0 x X H z =
        offDiagonalLocalizer (hGap.unit : Matrix n n ℂ) := by
    rw [finiteHermitianLocalizer_zero_scale, hGap.unit_spec]
    rfl
  rw [hLocalizer]
  exact ⟨offDiagonalLocalizer_mul_inverse hGap.unit,
    offDiagonalLocalizer_inverse_mul hGap.unit⟩

/-- The identity operator has a point gap at zero. -/
theorem identity_hasFinitePointGap_zero :
    HasFinitePointGap (1 : Matrix n n ℂ) 0 := by
  simp [HasFinitePointGap, pointGapBlock]

example :
    IsUnit
      (finiteHermitianLocalizer 0 0
        (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 0) := by
  exact zero_scale_localizer_isUnit_of_pointGap 0 0 1 0
    identity_hasFinitePointGap_zero

#print axioms offDiagonalLocalizer_mul_inverse
#print axioms offDiagonalLocalizer_inverse_mul
#print axioms zero_scale_localizer_isUnit_of_pointGap
#print axioms zero_scale_localizer_explicit_inverse
#print axioms identity_hasFinitePointGap_zero

end

end D5.S3.SpectralTopology.FinitePointGapLocalizer
