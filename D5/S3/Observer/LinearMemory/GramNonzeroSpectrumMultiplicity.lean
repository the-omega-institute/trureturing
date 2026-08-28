/- GID: D5/S3/Observer/LinearMemory/GramNonzeroSpectrumMultiplicity
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/GramNonzeroSpectrumMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rectangular adjoint Gram matrices have the same nonzero spectrum with multiplicity. -/

import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/- Library-search audit trail (2026-08-28):
   * D5 and pinned-Mathlib searches found no exact theorem equating the
     nonzero spectra of the two rectangular Gram matrices with algebraic
     multiplicity.
   * `Matrix.charpoly_mul_comm'` supplies the rectangular characteristic-
     polynomial identity. `Polynomial.rootMultiplicity_mul` cancels its
     powers of `X` at a nonzero scalar; both are applied directly below.
   * No new definition or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.GramNonzeroSpectrumMultiplicity

/-- The state and protocol Gram matrices of a rectangular `RCLike` matrix
have the same nonzero roots of their characteristic polynomials, and every
such root has the same algebraic multiplicity on both sides. -/
theorem gram_nonzero_spectrum_with_algebraic_multiplicity
    {K m n : Type*} [RCLike K]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n K) (lambda : K) (lambda_ne_zero : lambda ≠ 0) :
    ((M.conjTranspose * M).charpoly.IsRoot lambda ↔
      (M * M.conjTranspose).charpoly.IsRoot lambda) ∧
    Polynomial.rootMultiplicity lambda ((M.conjTranspose * M).charpoly) =
      Polynomial.rootMultiplicity lambda ((M * M.conjTranspose).charpoly) := by
  have comparison := Matrix.charpoly_mul_comm' M.conjTranspose M
  have leftNonzero :
      Polynomial.X ^ Fintype.card m * (M.conjTranspose * M).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic (M.conjTranspose * M)).ne_zero
  have rightNonzero :
      Polynomial.X ^ Fintype.card n * (M * M.conjTranspose).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      (Matrix.charpoly_monic (M * M.conjTranspose)).ne_zero
  have multiplicities :=
    congrArg (Polynomial.rootMultiplicity lambda) comparison
  rw [Polynomial.rootMultiplicity_mul leftNonzero,
    Polynomial.rootMultiplicity_mul rightNonzero] at multiplicities
  have xPowMultiplicity (k : Nat) :
      Polynomial.rootMultiplicity lambda (Polynomial.X ^ k) = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    intro root
    have powerZero : lambda ^ k = 0 := by
      simpa [Polynomial.IsRoot] using root
    exact (pow_ne_zero k lambda_ne_zero) powerZero
  have multiplicityEquality :
      Polynomial.rootMultiplicity lambda ((M.conjTranspose * M).charpoly) =
        Polynomial.rootMultiplicity lambda ((M * M.conjTranspose).charpoly) := by
    simpa [xPowMultiplicity] using multiplicities
  constructor
  · rw [← Polynomial.rootMultiplicity_pos
      (Matrix.charpoly_monic (M.conjTranspose * M)).ne_zero,
      ← Polynomial.rootMultiplicity_pos
        (Matrix.charpoly_monic (M * M.conjTranspose)).ne_zero,
      multiplicityEquality]
  · exact multiplicityEquality

#print axioms gram_nonzero_spectrum_with_algebraic_multiplicity

end D5.S3.Observer.LinearMemory.GramNonzeroSpectrumMultiplicity
