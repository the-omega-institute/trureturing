/- GID: D5/S3/Weil/Pick/FinitePickPositivity
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/FinitePickPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive Hermitian kernels and contractive scalar multipliers are characterized by finite Pick matrix positivity. -/

import D5.S3.Weil.Pick.HermitianKernelNegativeSquares
import Mathlib.Tactic

/-!
# Finite Pick positivity

A Hermitian kernel is positive when every finite sampled Gram matrix is
positive semidefinite.  A scalar function is contractive relative to that
kernel when every finite Pick matrix

`(1 - phi(x_i) conj(phi(x_j))) K(x_i,x_j)`

is positive semidefinite.

This module freezes the finite matrix interface and elementary closure laws.
It does not assert an interpolation theorem, a reproducing-kernel Hilbert
space construction, multiplier norm completeness, or the complete Pick
property.
-/

/- Library-search audit trail (2026-09-01):
   * `HermitianKernelNegativeSquares` owns Hermitian kernels, sampled Gram
     matrices, and finite negative-square counts.
   * `CriticalLineOscillatorGram` owns one specialized matrix named a Pick
     matrix, but no generic kernel multiplier interface.
   * Repository search found no generic positive-kernel and finite Pick
     positivity definitions.
   * Pinned Mathlib supplies finite Hermitian matrices and positive
     semidefiniteness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Pick.FinitePickPositivity

open D5.S3.Weil.Pick.HermitianKernelNegativeSquares

noncomputable section

universe u

variable {Point : Type u}

/-- Positive Hermitian kernel through all finite sampled Gram matrices. -/
def IsPositiveKernel (kernel : HermitianKernel Point) : Prop :=
  ∀ (n : ℕ) (points : Fin n → Point),
    (kernel.gramMatrix points).PosSemidef

/-- Finite scalar Pick matrix for a kernel and proposed multiplier. -/
def finitePickMatrix
    (kernel : HermitianKernel Point) (multiplier : Point → ℂ)
    {n : ℕ} (points : Fin n → Point) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (1 - multiplier (points i) * star (multiplier (points j))) *
      kernel.value (points i) (points j)

/-- A scalar function is kernel-contractive when every finite Pick matrix is
positive semidefinite. -/
def IsKernelContractiveMultiplier
    (kernel : HermitianKernel Point) (multiplier : Point → ℂ) : Prop :=
  ∀ (n : ℕ) (points : Fin n → Point),
    (finitePickMatrix kernel multiplier points).PosSemidef

/-- Every finite Pick matrix is Hermitian. -/
theorem finitePickMatrix_isHermitian
    (kernel : HermitianKernel Point) (multiplier : Point → ℂ)
    {n : ℕ} (points : Fin n → Point) :
    (finitePickMatrix kernel multiplier points).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [finitePickMatrix, kernel.conj_symm]
  ring

/-- The zero multiplier has the original kernel Gram matrix as its Pick
matrix. -/
theorem finitePickMatrix_zero
    (kernel : HermitianKernel Point)
    {n : ℕ} (points : Fin n → Point) :
    finitePickMatrix kernel (fun _ => 0) points =
      kernel.gramMatrix points := by
  ext i j
  simp [finitePickMatrix, HermitianKernel.gramMatrix]

/-- The zero function is contractive for every positive kernel. -/
theorem zero_isKernelContractiveMultiplier
    {kernel : HermitianKernel Point}
    (hPositive : IsPositiveKernel kernel) :
    IsKernelContractiveMultiplier kernel (fun _ => 0) := by
  intro n points
  rw [finitePickMatrix_zero]
  exact hPositive n points

/-- The zero Hermitian kernel is positive. -/
def zeroHermitianKernel : HermitianKernel Point where
  value := fun _ _ => 0
  conj_symm := by simp

/-- The zero kernel is positive. -/
theorem zeroHermitianKernel_isPositive :
    IsPositiveKernel (zeroHermitianKernel : HermitianKernel Point) := by
  intro n points
  have hZero :
      (zeroHermitianKernel.gramMatrix points) =
        (0 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    rfl
  rw [hZero]
  exact Matrix.PosSemidef.zero

/-- Every scalar function is contractive for the zero kernel. -/
theorem every_multiplier_contracts_zeroKernel
    (multiplier : Point → ℂ) :
    IsKernelContractiveMultiplier
      (zeroHermitianKernel : HermitianKernel Point) multiplier := by
  intro n points
  have hZero :
      finitePickMatrix zeroHermitianKernel multiplier points =
        (0 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp [finitePickMatrix, zeroHermitianKernel]
  rw [hZero]
  exact Matrix.PosSemidef.zero

/-- Kernel contractivity is stable under pointwise equality of multipliers. -/
theorem isKernelContractiveMultiplier_congr
    (kernel : HermitianKernel Point)
    {first second : Point → ℂ}
    (hEqual : first = second)
    (hFirst : IsKernelContractiveMultiplier kernel first) :
    IsKernelContractiveMultiplier kernel second := by
  subst second
  exact hFirst

example :
    IsPositiveKernel (zeroHermitianKernel : HermitianKernel Unit) :=
  zeroHermitianKernel_isPositive

#print axioms finitePickMatrix_isHermitian
#print axioms finitePickMatrix_zero
#print axioms zero_isKernelContractiveMultiplier
#print axioms zeroHermitianKernel_isPositive
#print axioms every_multiplier_contracts_zeroKernel
#print axioms isKernelContractiveMultiplier_congr

end

end D5.S3.Weil.Pick.FinitePickPositivity
