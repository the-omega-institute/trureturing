/- GID: D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan, mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic, mathlib/module/Mathlib.Algebra.Polynomial.Degree.Defs]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.claim; result=D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.result; claim=D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.claim
   digest: The literal exact-degree assertion in Cigler v2 Conjecture 16 fails at k=1 and m=0. -/

import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CatalanPowerHankel.CiglerSixteenDegreeRefutation

noncomputable section

/-!
Johann Cigler, arXiv:2308.07642v2, Section 3, Conjecture 16, equation (30).
The coefficients are defined by the actual Catalan series, not by a proposed
closed formula. All determinant sizes and all permitted integer shifts remain
in the claim. Equation (6) already records the known all-order evaluation
D_{1,0}(N) = D_{1,1}(N) = 1; only the empty and singleton cases are needed here.

For k >= 1 and m >= 1-k, the integers k, 2*k-1 and k+m are positive.
Their conversions to naturals in the powers and binomial coefficient therefore
preserve their values. The polygonal expression is evaluated in the rationals,
so in particular the subtraction j-4 at j=3 is integer subtraction.
An explicit natural d with Q.degree = d expresses the actual degree, excludes
the zero polynomial, and introduces no truncation or padded-degree convention.
Reciprocity is stated directly at nonzero complex arguments, with exponent
Q.natDegree, the actual degree of a nonzero Q.
-/

/-- The Catalan generating series, with its natural coefficients cast into R. -/
def catalanSeries (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.catalanSeries.map (Nat.castRingHom R)

/-- Coefficients of the actual r-th power, extended by zero to negative indices. -/
def catalanPowerCoeff (R : Type*) [CommRing R] (r : ℕ) (t : ℤ) : R :=
  if 0 ≤ t then PowerSeries.coeff t.toNat (catalanSeries R ^ r) else 0

/-- The full finite Hankel determinant, including its empty determinant. -/
def hankel (R : Type*) [CommRing R] (r : ℕ) (m : ℤ) (N : ℕ) : R :=
  (Matrix.of fun i j : Fin N => catalanPowerCoeff R r ((i : ℤ) + j + m)).det

/-- The entire formal generating series of Hankel determinants. -/
def hankelSeries (R : Type*) [CommRing R] (r : ℕ) (m : ℤ) : PowerSeries R :=
  PowerSeries.mk (hankel R r m)

/-- The source's second j-gonal expression, using exact rational arithmetic. -/
def polygonalNumber (j t : ℤ) : ℚ :=
  (t : ℚ) * (((j : ℚ) - 2) * (t : ℚ) + ((j : ℚ) - 4)) / 2

/-- The left side of (30), with every determinant coefficient retained. -/
def numeratorSeries (R : Type*) [CommRing R] (k m : ℤ) : PowerSeries R :=
  (1 + (-1 : PowerSeries R) ^ k.toNat * PowerSeries.X ^ (2 * k - 1).toNat) ^
    ((k + m).toNat.choose 2 + 1) * hankelSeries R (2 * k - 1).toNat m

/-- The source's reciprocity equality, using the polynomial's actual degree. -/
def palindromic (Q : Polynomial ℂ) : Prop :=
  ∀ x : ℂ, x ≠ 0 → x ^ Q.natDegree * Q.eval x⁻¹ = Q.eval x

/-- The source's negative reciprocity equality, with the printed minus sign. -/
def skewPalindromic (Q : Polynomial ℂ) : Prop :=
  ∀ x : ℂ, x ≠ 0 → x ^ Q.natDegree * Q.eval x⁻¹ = -Q.eval x

/-- The whole literal Conjecture 16 over the usual complex coefficient realization. -/
def claim : Prop :=
  ∀ k m : ℤ, 1 ≤ k → 1 - k ≤ m → ∃ Q : Polynomial ℂ,
    numeratorSeries ℂ k m = (Q : PowerSeries ℂ) ∧
    (∃ d : ℕ, Q.degree = (d : WithBot ℕ) ∧
      (d : ℚ) = polygonalNumber (2 * k + 1) (m + k - 1) + (k : ℚ)) ∧
    (palindromic Q ∨ skewPalindromic Q) ∧
    (k % 4 = 1 → Even m → palindromic Q) ∧
    (k % 4 = 3 → Odd m → palindromic Q) ∧
    (k % 4 = 0 ∨ k % 4 = 2 → m % 4 = 0 ∨ m % 4 = 1 → palindromic Q)

private theorem hankel_empty (R : Type*) [CommRing R] (r : ℕ) (m : ℤ) :
    hankel R r m 0 = 1 :=
  Matrix.det_isEmpty

private theorem hankel_one_zero (R : Type*) [CommRing R] : hankel R 1 0 1 = 1 := by
  simp [hankel, Matrix.det_fin_one, catalanPowerCoeff, catalanSeries,
    PowerSeries.coeff_map]

private theorem boundary_linear (R : Type*) [CommRing R] :
    PowerSeries.coeff 1 ((1 - PowerSeries.X) * hankelSeries R 1 0) = 0 := by
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul 0]
  simp [hankelSeries, hankel_empty, hankel_one_zero]

private theorem boundary_no_degree_one (R : Type*) [CommRing R] (Q : Polynomial R)
    (hseries : (1 - PowerSeries.X) * hankelSeries R 1 0 = (Q : PowerSeries R))
    (hdegree : Q.degree = (1 : WithBot ℕ)) : False := by
  have hcoeff := congrArg (PowerSeries.coeff 1) hseries
  rw [boundary_linear, Polynomial.coeff_coe] at hcoeff
  exact Polynomial.coeff_ne_zero_of_eq_degree hdegree hcoeff.symm

/-- The allowed boundary k=1, m=0 contradicts the literal exact-degree equality. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨Q, hseries, ⟨d, hdegree, hvalue⟩, _⟩ := h 1 0 (by decide) (by decide)
  have hd : d = 1 := by
    norm_num [polygonalNumber] at hvalue
    exact_mod_cast hvalue
  subst d
  apply boundary_no_degree_one ℂ Q _ hdegree
  simpa [numeratorSeries, sub_eq_add_neg] using hseries

end

end D5.S3.Combinatorics.CatalanPowerHankel.CiglerSixteenDegreeRefutation
