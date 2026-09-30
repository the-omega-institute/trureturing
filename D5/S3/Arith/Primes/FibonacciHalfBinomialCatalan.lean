/- GID: D5/S3/Arith/Primes/FibonacciHalfBinomialCatalan
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciHalfBinomialCatalan
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan,
     mathlib/module/Mathlib.RingTheory.PowerSeries.Binomial]
   utility: none
   digest: The half-binomial coefficients are signed dyadic Catalan numbers. -/

import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciHalfBinomialCatalan

open PowerSeries

theorem half_binomial_catalan (n : ℕ) :
    Ring.choose (1/2 : ℚ) (n + 1) =
      (-1 : ℚ)^n * (catalan n : ℚ) / (2 : ℚ)^(2*n + 1) ∧
    ∃ z : ℤ, (2 : ℚ)^(2*n + 1) * Ring.choose (1/2 : ℚ) (n + 1) = (z : ℚ) := by
  let C : ℚ⟦X⟧ := catalanSeries.map (Nat.castRingHom ℚ)
  let T : ℚ⟦X⟧ := rescale (-1/4 : ℚ) C
  let S : ℚ⟦X⟧ := 1 + (PowerSeries.C (1/2 : ℚ)) * X * T
  let B : ℚ⟦X⟧ := binomialSeries ℚ (1/2 : ℚ)
  have hC : C^2 * X + 1 = C := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      catalanSeries_sq_mul_X_add_one
    simpa only [C, map_add, map_mul, map_pow, map_one, map_X] using h
  have hT : T^2 * (PowerSeries.C (-1/4 : ℚ) * X) + 1 = T := by
    have h := congrArg (rescale (-1/4 : ℚ)) hC
    simpa [T, rescale_X] using h
  have hhalf : (2 : ℚ⟦X⟧) * PowerSeries.C (1/2 : ℚ) = 1 := by
    have h : (2 : ℚ) * (1/2 : ℚ) = 1 := by norm_num
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (PowerSeries.C : ℚ →+* ℚ⟦X⟧) h
  have hquarter : (PowerSeries.C (1/2 : ℚ))^2 =
      -(PowerSeries.C (-1/4 : ℚ)) := by
    rw [← map_pow, ← map_neg]
    congr 1
    norm_num
  have hS : S^2 = 1 + X := by
    dsimp [S]
    linear_combination -X * hT + X*T * hhalf + X^2*T^2 * hquarter
  have hB : B^2 = 1 + X := by
    calc
      B^2 = binomialSeries ℚ ((1/2 : ℚ) + (1/2 : ℚ)) := by
        simpa only [B, pow_two] using
          (binomialSeries_add (A := ℚ) (1/2 : ℚ) (1/2 : ℚ)).symm
      _ = binomialSeries ℚ (1 : ℚ) := by norm_num
      _ = (1 + X)^1 := binomialSeries_nat 1
      _ = 1 + X := pow_one _
  have hunit : IsUnit (S + B) := isUnit_iff_constantCoeff.mpr (by
    norm_num [S, B])
  have hdiff : S - B = 0 := by
    apply hunit.mul_right_cancel
    calc
      (S - B) * (S + B) = S^2 - B^2 := by ring
      _ = 0 := by rw [hS, hB]; ring
      _ = 0 * (S + B) := by ring
  have hSB : S = B := sub_eq_zero.mp hdiff
  have hc := congrArg (coeff (n + 1)) hSB.symm
  have hbase : Ring.choose (1/2 : ℚ) (n + 1) =
      (1/2 : ℚ) * (-1/4 : ℚ)^n * (catalan n : ℚ) := by
    simpa [S, B, T, C, coeff_succ_X_mul, coeff_C_mul, mul_assoc] using hc
  have hformula : Ring.choose (1/2 : ℚ) (n + 1) =
      (-1 : ℚ)^n * (catalan n : ℚ) / (2 : ℚ)^(2*n + 1) := by
    calc
      Ring.choose (1/2 : ℚ) (n + 1) =
          (1/2 : ℚ) * (-1/4 : ℚ)^n * (catalan n : ℚ) := hbase
      _ = (-1 : ℚ)^n * (catalan n : ℚ) / (2 : ℚ)^(2*n + 1) := by
        rw [div_pow]
        have hfour : (4 : ℚ)^n = (2 : ℚ)^(2*n) := by
          norm_num [pow_mul]
        rw [hfour, pow_add]
        field_simp
  refine ⟨hformula, ?_⟩
  refine ⟨(-1 : ℤ)^n * (catalan n : ℤ), ?_⟩
  rw [hformula]
  field_simp
  norm_cast

#print axioms half_binomial_catalan

end D5.S3.Arith.Primes.FibonacciHalfBinomialCatalan
