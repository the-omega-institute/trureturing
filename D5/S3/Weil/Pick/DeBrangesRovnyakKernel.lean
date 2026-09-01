/- GID: D5/S3/Weil/Pick/DeBrangesRovnyakKernel
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/DeBrangesRovnyakKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Scalar multiplier defects form Hermitian de Branges-Rovnyak kernels whose Gram matrices are exactly finite Pick matrices. -/

import D5.S3.Weil.Pick.FinitePickPositivity
import Mathlib.Tactic

/-!
# de Branges-Rovnyak defect kernel

Given a Hermitian kernel `K` and scalar function `phi`, define

`K^phi(x,y) = (1 - phi(x) conj(phi(y))) K(x,y)`.

The sampled Gram matrices of this defect kernel are exactly the finite Pick
matrices.  Consequently, positivity of the de Branges-Rovnyak kernel is
identical to kernel contractivity of the multiplier.  The zero multiplier
recovers the original kernel, while the constant unit multiplier produces the
zero kernel.

This module freezes the kernel identity only.  It does not construct the
associated reproducing-kernel Hilbert space, prove a complete Pick theorem, or
identify a multiplier norm with an operator norm.
-/

/- Library-search audit trail (2026-09-01):
   * `FinitePickPositivity` owns positive kernels, finite Pick matrices, and
     kernel contractivity.
   * Existing Xi and toroidal de Branges candidates are specialized theory
     atoms and do not own this generic scalar defect-kernel interface.
   * Repository search found no generic de Branges-Rovnyak kernel with the
     exact finite Gram/Pick identity.
   * Pinned Mathlib supplies complex conjugation and finite matrices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Pick.DeBrangesRovnyakKernel

open D5.S3.Weil.Pick.HermitianKernelNegativeSquares
open D5.S3.Weil.Pick.FinitePickPositivity

noncomputable section

universe u

variable {Point : Type u}

/-- Scalar de Branges-Rovnyak defect kernel. -/
def deBrangesRovnyakKernel
    (kernel : HermitianKernel Point) (multiplier : Point → ℂ) :
    HermitianKernel Point where
  value x y :=
    (1 - multiplier x * star (multiplier y)) * kernel.value x y
  conj_symm := by
    intro x y
    simp [kernel.conj_symm]
    ring

/-- Sampled defect-kernel Gram matrices are finite Pick matrices. -/
theorem deBrangesRovnyakKernel_gramMatrix
    (kernel : HermitianKernel Point) (multiplier : Point → ℂ)
    {n : ℕ} (points : Fin n → Point) :
    (deBrangesRovnyakKernel kernel multiplier).gramMatrix points =
      finitePickMatrix kernel multiplier points := by
  rfl

/-- Kernel contractivity is exactly positivity of the de Branges-Rovnyak
defect kernel. -/
theorem isPositiveKernel_deBrangesRovnyak_iff
    (kernel : HermitianKernel Point) (multiplier : Point → ℂ) :
    IsPositiveKernel (deBrangesRovnyakKernel kernel multiplier) ↔
      IsKernelContractiveMultiplier kernel multiplier := by
  rfl

/-- The zero multiplier leaves the kernel unchanged. -/
theorem deBrangesRovnyakKernel_zero
    (kernel : HermitianKernel Point) :
    deBrangesRovnyakKernel kernel (fun _ => 0) = kernel := by
  apply HermitianKernel.ext
  funext x y
  simp [deBrangesRovnyakKernel]

/-- The constant unit multiplier annihilates the defect kernel. -/
theorem deBrangesRovnyakKernel_one
    (kernel : HermitianKernel Point) :
    deBrangesRovnyakKernel kernel (fun _ => 1) =
      zeroHermitianKernel := by
  apply HermitianKernel.ext
  funext x y
  simp [deBrangesRovnyakKernel, zeroHermitianKernel]

/-- A positive kernel gives a positive defect kernel for the zero multiplier. -/
theorem deBrangesRovnyakKernel_zero_positive
    {kernel : HermitianKernel Point}
    (hPositive : IsPositiveKernel kernel) :
    IsPositiveKernel (deBrangesRovnyakKernel kernel (fun _ => 0)) := by
  rw [deBrangesRovnyakKernel_zero]
  exact hPositive

/-- The defect kernel of the unit multiplier is positive because it is zero. -/
theorem deBrangesRovnyakKernel_one_positive
    (kernel : HermitianKernel Point) :
    IsPositiveKernel (deBrangesRovnyakKernel kernel (fun _ => 1)) := by
  rw [deBrangesRovnyakKernel_one]
  exact zeroHermitianKernel_isPositive

/-- The finite Pick matrix of the unit multiplier vanishes. -/
theorem finitePickMatrix_one
    (kernel : HermitianKernel Point)
    {n : ℕ} (points : Fin n → Point) :
    finitePickMatrix kernel (fun _ => 1) points = 0 := by
  rw [← deBrangesRovnyakKernel_gramMatrix,
    deBrangesRovnyakKernel_one]
  ext i j
  rfl

example :
    deBrangesRovnyakKernel
      (zeroHermitianKernel : HermitianKernel Unit) (fun _ => 1) =
      zeroHermitianKernel := by
  exact deBrangesRovnyakKernel_one _

#print axioms deBrangesRovnyakKernel_gramMatrix
#print axioms isPositiveKernel_deBrangesRovnyak_iff
#print axioms deBrangesRovnyakKernel_zero
#print axioms deBrangesRovnyakKernel_one
#print axioms deBrangesRovnyakKernel_zero_positive
#print axioms deBrangesRovnyakKernel_one_positive
#print axioms finitePickMatrix_one

end

end D5.S3.Weil.Pick.DeBrangesRovnyakKernel
