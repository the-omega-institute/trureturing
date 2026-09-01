/- GID: D5/S3/Weil/Pick/CompletePickInterpolationProperty
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/CompletePickInterpolationProperty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Matrix-valued finite Pick data define complete kernel contractivity and a precise complete interpolation property. -/

import D5.S3.Weil.Pick.DeBrangesRovnyakKernel
import Mathlib.Tactic

/-!
# Finite complete Pick interpolation property

For matrix-valued data `W_i`, the finite block Pick matrix has entries

`(I - W_i W_j^*) K(x_i,x_j)`.

A matrix-valued multiplier is completely kernel-contractive at its matrix size
when all of its finite block Pick matrices are positive semidefinite.  A
Hermitian kernel has the finite complete Pick interpolation property when
every consistent positive Pick datum admits such an interpolating multiplier.

Repeated interpolation nodes are required to carry identical values.  This is
the ordinary consistency condition needed for any function-valued
interpolant.  The zero kernel is shown to satisfy the resulting property,
providing an inhabited exact model.

This module defines and inhabits the finite property.  It does not prove that a
nonzero classical kernel has the property, construct a reproducing-kernel
Hilbert space, or identify the property with any particular complete Pick
factorization theorem.
-/

/- Library-search audit trail (2026-09-01):
   * `FinitePickPositivity` owns scalar finite Pick matrices.
   * `DeBrangesRovnyakKernel` owns the scalar defect-kernel identity.
   * Repository search found no matrix-valued block Pick matrix or complete
     interpolation property.
   * Pinned Mathlib supplies block-index matrices, conjugate transpose,
     positive semidefiniteness, and finite classical choice. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Pick.CompletePickInterpolationProperty

open D5.S3.Weil.Pick.HermitianKernelNegativeSquares
open D5.S3.Weil.Pick.FinitePickPositivity

noncomputable section

universe u

variable {Point : Type u}

/-- Matrix-valued finite Pick matrix at matrix size `dimension`. -/
def operatorPickMatrix
    (kernel : HermitianKernel Point)
    {dimension nodesCount : ℕ}
    (nodes : Fin nodesCount → Point)
    (values : Fin nodesCount → Matrix (Fin dimension) (Fin dimension) ℂ) :
    Matrix (Fin nodesCount × Fin dimension)
      (Fin nodesCount × Fin dimension) ℂ :=
  fun left right =>
    ((1 : Matrix (Fin dimension) (Fin dimension) ℂ) left.2 right.2 -
        (values left.1 * (values right.1)ᴴ) left.2 right.2) *
      kernel.value (nodes left.1) (nodes right.1)

/-- Repeated nodes must carry the same target matrix. -/
def ConsistentMatrixInterpolationData
    {dimension nodesCount : ℕ}
    (nodes : Fin nodesCount → Point)
    (values : Fin nodesCount → Matrix (Fin dimension) (Fin dimension) ℂ) : Prop :=
  ∀ i j, nodes i = nodes j → values i = values j

/-- A matrix-valued function interpolates the prescribed finite data. -/
def InterpolatesMatrixData
    {dimension nodesCount : ℕ}
    (nodes : Fin nodesCount → Point)
    (values : Fin nodesCount → Matrix (Fin dimension) (Fin dimension) ℂ)
    (multiplier : Point → Matrix (Fin dimension) (Fin dimension) ℂ) : Prop :=
  ∀ i, multiplier (nodes i) = values i

/-- Complete kernel contractivity at one finite matrix size. -/
def IsCompletelyKernelContractive
    (kernel : HermitianKernel Point) {dimension : ℕ}
    (multiplier : Point → Matrix (Fin dimension) (Fin dimension) ℂ) : Prop :=
  ∀ (nodesCount : ℕ) (nodes : Fin nodesCount → Point),
    (operatorPickMatrix kernel nodes
      (fun i => multiplier (nodes i))).PosSemidef

/-- Finite complete Pick interpolation property. -/
def HasCompletePickInterpolationProperty
    (kernel : HermitianKernel Point) : Prop :=
  ∀ (dimension nodesCount : ℕ)
    (nodes : Fin nodesCount → Point)
    (values : Fin nodesCount → Matrix (Fin dimension) (Fin dimension) ℂ),
    ConsistentMatrixInterpolationData nodes values →
    (operatorPickMatrix kernel nodes values).PosSemidef →
    ∃ multiplier : Point → Matrix (Fin dimension) (Fin dimension) ℂ,
      IsCompletelyKernelContractive kernel multiplier ∧
        InterpolatesMatrixData nodes values multiplier

/-- Block Pick matrices over the zero kernel vanish. -/
theorem operatorPickMatrix_zeroKernel
    {dimension nodesCount : ℕ}
    (nodes : Fin nodesCount → Point)
    (values : Fin nodesCount → Matrix (Fin dimension) (Fin dimension) ℂ) :
    operatorPickMatrix zeroHermitianKernel nodes values = 0 := by
  ext left right
  simp [operatorPickMatrix, zeroHermitianKernel]

/-- Every matrix-valued function is completely contractive for the zero
kernel. -/
theorem every_matrix_multiplier_contracts_zeroKernel
    {dimension : ℕ}
    (multiplier : Point → Matrix (Fin dimension) (Fin dimension) ℂ) :
    IsCompletelyKernelContractive zeroHermitianKernel multiplier := by
  intro nodesCount nodes
  rw [operatorPickMatrix_zeroKernel]
  exact Matrix.PosSemidef.zero

/-- Classical extension of consistent finite matrix data. -/
def extendConsistentMatrixData
    {dimension nodesCount : ℕ}
    (nodes : Fin nodesCount → Point)
    (values : Fin nodesCount → Matrix (Fin dimension) (Fin dimension) ℂ) :
    Point → Matrix (Fin dimension) (Fin dimension) ℂ :=
  fun point =>
    if h : ∃ i, nodes i = point then values (Classical.choose h) else 0

/-- Consistency makes the classical extension interpolate every prescribed
node. -/
theorem extendConsistentMatrixData_interpolates
    {dimension nodesCount : ℕ}
    (nodes : Fin nodesCount → Point)
    (values : Fin nodesCount → Matrix (Fin dimension) (Fin dimension) ℂ)
    (hConsistent : ConsistentMatrixInterpolationData nodes values) :
    InterpolatesMatrixData nodes values
      (extendConsistentMatrixData nodes values) := by
  intro i
  unfold extendConsistentMatrixData
  let hExists : ∃ j, nodes j = nodes i := ⟨i, rfl⟩
  rw [dif_pos hExists]
  exact hConsistent _ i (Classical.choose_spec hExists)

/-- The zero Hermitian kernel satisfies the finite complete Pick interpolation
property. -/
theorem zeroKernel_hasCompletePickInterpolationProperty :
    HasCompletePickInterpolationProperty
      (zeroHermitianKernel : HermitianKernel Point) := by
  intro dimension nodesCount nodes values hConsistent _
  refine ⟨extendConsistentMatrixData nodes values, ?_, ?_⟩
  · exact every_matrix_multiplier_contracts_zeroKernel _
  · exact extendConsistentMatrixData_interpolates nodes values hConsistent

/-- The complete property immediately produces an interpolant for every
consistent admissible datum. -/
theorem completePick_interpolant_exists
    {kernel : HermitianKernel Point}
    (hComplete : HasCompletePickInterpolationProperty kernel)
    {dimension nodesCount : ℕ}
    (nodes : Fin nodesCount → Point)
    (values : Fin nodesCount → Matrix (Fin dimension) (Fin dimension) ℂ)
    (hConsistent : ConsistentMatrixInterpolationData nodes values)
    (hPick : (operatorPickMatrix kernel nodes values).PosSemidef) :
    ∃ multiplier,
      IsCompletelyKernelContractive kernel multiplier ∧
        InterpolatesMatrixData nodes values multiplier :=
  hComplete dimension nodesCount nodes values hConsistent hPick

/-- Complete kernel contractivity is stable under pointwise equality. -/
theorem isCompletelyKernelContractive_congr
    (kernel : HermitianKernel Point) {dimension : ℕ}
    {first second : Point → Matrix (Fin dimension) (Fin dimension) ℂ}
    (hEqual : first = second)
    (hFirst : IsCompletelyKernelContractive kernel first) :
    IsCompletelyKernelContractive kernel second := by
  subst second
  exact hFirst

example :
    HasCompletePickInterpolationProperty
      (zeroHermitianKernel : HermitianKernel Unit) :=
  zeroKernel_hasCompletePickInterpolationProperty

#print axioms operatorPickMatrix_zeroKernel
#print axioms every_matrix_multiplier_contracts_zeroKernel
#print axioms extendConsistentMatrixData_interpolates
#print axioms zeroKernel_hasCompletePickInterpolationProperty
#print axioms completePick_interpolant_exists
#print axioms isCompletelyKernelContractive_congr

end

end D5.S3.Weil.Pick.CompletePickInterpolationProperty
