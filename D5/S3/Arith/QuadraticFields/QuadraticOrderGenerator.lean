/- GID: D5/S3/Arith/QuadraticFields/QuadraticOrderGenerator
   generality: G
   mirror-B: D5/B/S3/Arith/QuadraticFields/QuadraticOrderGenerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual maximal-order generator and its Kummer-Dedekind exponent and minimal polynomial. -/

import D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

namespace D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal

open Polynomial QuadraticAlgebra
open scoped NumberField

/-- The defining polynomial of the coordinate generator of an integer quadratic algebra. -/
noncomputable def orderPolynomial (a b : ℤ) : ℤ[X] := X ^ 2 - C b * X - C a

/-- The two coordinate basis vectors prove minimality over the integers themselves. -/
theorem orderGenerator_minpoly (a b : ℤ) :
    minpoly ℤ (ω : QuadraticAlgebra ℤ a b) = orderPolynomial a b := by
  apply minpoly.eq_of_linearIndependent (A := ℤ) (x := (ω : QuadraticAlgebra ℤ a b)) (n := 2)
  · rw [show orderPolynomial a b = X ^ 2 - (C b * X + C a) by
      unfold orderPolynomial
      ring]
    exact monic_X_pow_sub (by simpa using! (degree_linear_lt (a := b) (b := a)))
  · simp only [orderPolynomial, map_sub, map_mul, map_pow, aeval_X, aeval_C]
    ext <;> simp [sq] <;> ring
  · rw [show orderPolynomial a b = C 1 * X ^ 2 + C (-b) * X + C (-a) by
      simp only [orderPolynomial, Polynomial.C_1, Polynomial.C_neg]
      ring]
    simpa using! (degree_quadratic (a := (1 : ℤ)) (b := -b) (c := -a) one_ne_zero)
  · convert (QuadraticAlgebra.basis a b).linearIndependent using 1
    funext i
    fin_cases i <;> simp

namespace PrimeImaginary

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- The half-integral generator in the actual ring of integers. -/
noncomputable def integralGenerator : 𝓞 (Field p) :=
  maximalOrderEquiv p (ω : QuadraticAlgebra ℤ (orderA p) 1)

/-- The maximality theorem discharges the exponent condition of Kummer-Dedekind at
every rational prime, rather than leaving an assumed index-coprimality condition. -/
theorem integralGenerator_exponent : RingOfIntegers.exponent (integralGenerator p) = 1 := by
  rw [RingOfIntegers.exponent_eq_one_iff]
  have h := AlgHom.map_adjoin_singleton (maximalOrderEquiv p).toAlgHom
    (ω : QuadraticAlgebra ℤ (orderA p) 1)
  rw [QuadraticAlgebra.adjoin_omega_eq_top, Algebra.map_top] at h
  exact h.symm.trans ((AlgHom.range_eq_top (maximalOrderEquiv p).toAlgHom).mpr (maximalOrderEquiv p).surjective)

/-- Its integer minimal polynomial is X squared minus X plus (p+1)/4. -/
theorem integralGenerator_minpoly :
    minpoly ℤ (integralGenerator p) = X ^ 2 - X - C (orderA p) := by
  rw [integralGenerator, minpoly.algEquiv_eq, orderGenerator_minpoly, orderPolynomial]
  simp

end PrimeImaginary

end D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal
