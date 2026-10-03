/- GID: D5/S3/Arith/Primes/FibonacciRecurrencePolynomialRoots
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciRecurrencePolynomialRoots
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema]
   utility: none
   digest: Exact complex root multiset for odd plus-recurrence polynomials. -/

import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialChebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciRecurrencePolynomialRoots

open Polynomial
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialChebyshev

theorem odd_recurrence_polynomial_root_multiset (r : ℕ) :
    (Polynomial.map (algebraMap ℤ ℂ)
        (fibonacciRecurrencePolynomial (2 * r + 1))).roots =
      (Multiset.range (2 * r)).map (fun k : ℕ =>
        (-2 * Complex.I) *
          (Real.cos ((k + 1) * Real.pi / (2 * r + 1)) : ℂ)) := by
  have hscaled (m : ℕ) :
      ((Polynomial.Chebyshev.U ℂ (m : ℤ)).comp (C (Complex.I / 2) * X)).roots =
        (Multiset.range m).map (fun k : ℕ =>
          (-2 * Complex.I) *
            (Real.cos ((k + 1) * Real.pi / (m + 1)) : ℂ)) := by
    have hsplit : (Polynomial.Chebyshev.U ℝ (m : ℤ)).Splits := by
      rw [splits_iff_card_roots, Polynomial.Chebyshev.roots_U_real,
        ← Finset.card_def, Finset.card_image_of_injOn]
      · rw [Finset.card_range, natDegree_eq_of_degree_eq_some
          (Polynomial.Chebyshev.degree_U_natCast ℝ m)]
      · exact (Finset.range m).nodup_map_iff_injOn.mp
          (Polynomial.Chebyshev.roots_U_real_nodup m)
    have hmap :
        (Polynomial.Chebyshev.U ℂ (m : ℤ)).roots =
          (Polynomial.Chebyshev.U ℝ (m : ℤ)).roots.map (algebraMap ℝ ℂ) := by
      have hmap0 := Polynomial.Splits.roots_map_of_injective hsplit
        (algebraMap ℝ ℂ).injective
      simpa only [Polynomial.Chebyshev.map_U] using hmap0
    have hcomp :
        ((Polynomial.Chebyshev.U ℂ (m : ℤ)).comp (C (Complex.I / 2) * X)).roots =
          (Polynomial.Chebyshev.U ℂ (m : ℤ)).roots.map
            (fun x => (Complex.I / 2)⁻¹ * x) := by
      simpa using (Polynomial.roots_comp_C_mul_X_add_C
        (Polynomial.Chebyshev.U ℂ (m : ℤ)) (Complex.I / 2) 0
        (isUnit_iff_ne_zero.mpr (by
          intro h
          apply Complex.I_ne_zero
          calc
            Complex.I = 2 * (Complex.I / 2) := by ring
            _ = 2 * 0 := by rw [h]
            _ = 0 := by ring)))
    rw [hcomp, hmap, Polynomial.Chebyshev.roots_U_real]
    have hinj : Set.InjOn
        (fun k : ℕ => Real.cos ((k + 1) * Real.pi / (m + 1)))
        (↑(Finset.range m) : Set ℕ) := by
      exact (Finset.range m).nodup_map_iff_injOn.mp
        (Polynomial.Chebyshev.roots_U_real_nodup m)
    rw [Finset.image_val_of_injOn hinj]
    simp only [Multiset.map_map, Function.comp_apply]
    change Multiset.map
        (fun k : ℕ => (Complex.I / 2)⁻¹ *
          (algebraMap ℝ ℂ) (Real.cos ((k + 1) * Real.pi / (m + 1))))
        (Multiset.range m) = _
    have hfun :
        (fun k : ℕ => (Complex.I / 2)⁻¹ *
          (algebraMap ℝ ℂ) (Real.cos ((k + 1) * Real.pi / (m + 1)))) =
        (fun k : ℕ => (-2 * Complex.I) *
          (Real.cos ((k + 1) * Real.pi / (m + 1)) : ℂ)) := by
      funext k
      field_simp
      norm_num [Complex.I_mul_I]
    rw [hfun]
  have hbridge := fibonacci_recurrence_polynomial_chebyshev (2 * r)
  rw [hbridge]
  change (C ((-Complex.I) ^ (2 * r)) *
      (Polynomial.Chebyshev.U ℂ ((2 * r : ℕ) : ℤ)).comp
        (C (Complex.I / 2) * X)).roots = _
  rw [roots_C_mul]
  · simpa [show 2 * r + 1 = (2 * r) + 1 by omega] using hscaled (2 * r)
  · exact pow_ne_zero _ (by simp)

#print axioms odd_recurrence_polynomial_root_multiset

end D5.S3.Arith.Primes.FibonacciRecurrencePolynomialRoots
