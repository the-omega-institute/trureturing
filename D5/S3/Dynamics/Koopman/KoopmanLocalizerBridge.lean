/- GID: D5/S3/Dynamics/Koopman/KoopmanLocalizerBridge
   generality: G
   mirror-B: D5/B/S3/Dynamics/Koopman/KoopmanLocalizerBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite permutation Koopman pullback has an explicit unit matrix and therefore opens a zero-centered point-gap localizer. -/

import D5.S3.Dynamics.Koopman.FiniteKoopmanUnitary
import D5.S3.SpectralTopology.FinitePointGapLocalizer
import Mathlib.Tactic

/-!
# Finite Koopman-localizer bridge

A finite permutation update has the matrix

`K(i,j) = 1` when `j = update(i)` and `0` otherwise.

Its matrix-vector action is exactly the discrete Koopman pullback.  The matrix
for the inverse permutation is a two-sided inverse, so the Koopman matrix is a
unit.  Consequently zero is a finite point gap and the associated zero-scale
Hermitian localizer is invertible.

This module gives a finite algebraic bridge.  It does not define an infinite
Koopman operator spectrum, a bulk topological invariant, a localizer index, or
Pollicott-Ruelle resonances.
-/

/- Library-search audit trail (2026-09-01):
   * `DiscreteKoopmanOperator` owns the pullback action.
   * `FiniteKoopmanUnitary` owns finite permutation norm preservation and
     inverse pullback.
   * `FinitePointGapLocalizer` owns the point-gap to localizer-unit theorem.
   * Repository search found no explicit Koopman permutation matrix connecting
     those owners.
   * Pinned Mathlib supplies finite matrix multiplication and finite sums. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Dynamics.Koopman.KoopmanLocalizerBridge

open D5.S3.Dynamics.Koopman.DiscreteKoopmanOperator
open D5.S3.SpectralTopology.FiniteHermitianLocalizer
open D5.S3.SpectralTopology.FinitePointGapLocalizer

noncomputable section

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Matrix of finite permutation Koopman pullback. -/
def finiteKoopmanMatrix
    (update : Equiv.Perm State) : Matrix State State ℂ :=
  fun row column => if column = update row then 1 else 0

/-- The finite Koopman matrix acts exactly by pullback. -/
theorem finiteKoopmanMatrix_mulVec
    (update : Equiv.Perm State) (observable : State → ℂ) :
    (finiteKoopmanMatrix update).mulVec observable =
      discreteKoopmanOperator (update : State → State) observable := by
  funext state
  unfold Matrix.mulVec finiteKoopmanMatrix discreteKoopmanOperator
  rw [Finset.sum_eq_single (update state)]
  · simp
  · intro other _ hOther
    simp [hOther]
  · intro hMissing
    exact (hMissing (Finset.mem_univ _)).elim

/-- The inverse-permutation Koopman matrix is a right inverse. -/
theorem finiteKoopmanMatrix_mul_inverse
    (update : Equiv.Perm State) :
    finiteKoopmanMatrix update * finiteKoopmanMatrix update.symm = 1 := by
  ext row column
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (update row)]
  · simp [finiteKoopmanMatrix, Matrix.one_apply]
  · intro other _ hOther
    simp [finiteKoopmanMatrix, hOther]
  · intro hMissing
    exact (hMissing (Finset.mem_univ _)).elim

/-- The inverse-permutation Koopman matrix is a left inverse. -/
theorem finiteKoopmanMatrix_inverse_mul
    (update : Equiv.Perm State) :
    finiteKoopmanMatrix update.symm * finiteKoopmanMatrix update = 1 := by
  ext row column
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (update.symm row)]
  · simp [finiteKoopmanMatrix, Matrix.one_apply]
  · intro other _ hOther
    simp [finiteKoopmanMatrix, hOther]
  · intro hMissing
    exact (hMissing (Finset.mem_univ _)).elim

/-- Koopman permutation matrix as a unit. -/
def finiteKoopmanMatrixUnit
    (update : Equiv.Perm State) : (Matrix State State ℂ)ˣ where
  val := finiteKoopmanMatrix update
  inv := finiteKoopmanMatrix update.symm
  val_inv := finiteKoopmanMatrix_mul_inverse update
  inv_val := finiteKoopmanMatrix_inverse_mul update

/-- Zero is a point gap for every finite permutation Koopman matrix. -/
theorem finiteKoopmanMatrix_has_pointGap_zero
    (update : Equiv.Perm State) :
    HasFinitePointGap (finiteKoopmanMatrix update) 0 := by
  unfold HasFinitePointGap pointGapBlock
  simpa using (finiteKoopmanMatrixUnit update).isUnit

/-- Zero-scale Hermitian localizer of a finite permutation Koopman matrix is a
unit. -/
theorem finiteKoopmanLocalizer_isUnit
    (update : Equiv.Perm State) :
    IsUnit
      (finiteHermitianLocalizer 0 0
        (0 : Matrix State State ℂ)
        (finiteKoopmanMatrix update) 0) := by
  exact zero_scale_localizer_isUnit_of_pointGap
    0 0 (finiteKoopmanMatrix update) 0
    (finiteKoopmanMatrix_has_pointGap_zero update)

/-- The inverse localizer is built explicitly from the inverse-permutation
Koopman matrix. -/
theorem finiteKoopmanLocalizer_explicit_inverse
    (update : Equiv.Perm State) :
    let localizer :=
      finiteHermitianLocalizer 0 0
        (0 : Matrix State State ℂ)
        (finiteKoopmanMatrix update) 0
    let inverse :=
      offDiagonalLocalizerInverse (finiteKoopmanMatrixUnit update)
    localizer * inverse = 1 ∧ inverse * localizer = 1 := by
  dsimp
  have hGap := finiteKoopmanMatrix_has_pointGap_zero update
  simpa [finiteKoopmanMatrixUnit, pointGapBlock] using
    zero_scale_localizer_explicit_inverse
      0 (0 : Matrix State State ℂ)
      (finiteKoopmanMatrix update) 0 hGap

example :
    IsUnit
      (finiteHermitianLocalizer 0 0
        (0 : Matrix (Fin 1) (Fin 1) ℂ)
        (finiteKoopmanMatrix (1 : Equiv.Perm (Fin 1))) 0) :=
  finiteKoopmanLocalizer_isUnit _

#print axioms finiteKoopmanMatrix_mulVec
#print axioms finiteKoopmanMatrix_mul_inverse
#print axioms finiteKoopmanMatrix_inverse_mul
#print axioms finiteKoopmanMatrix_has_pointGap_zero
#print axioms finiteKoopmanLocalizer_isUnit
#print axioms finiteKoopmanLocalizer_explicit_inverse

end

end D5.S3.Dynamics.Koopman.KoopmanLocalizerBridge
