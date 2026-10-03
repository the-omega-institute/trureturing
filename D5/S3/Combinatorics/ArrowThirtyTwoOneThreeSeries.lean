/- GID: D5/S3/Combinatorics/ArrowThirtyTwoOneThreeSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowThirtyTwoOneThreeSeries
   mirror-E: none(waiver:formal-series-branch-uniqueness-for-the-arrow-cubic)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.NoZeroDivisors]
   utility: none
   digest: The cubic has at most one integer power-series solution with constant and linear coefficients one. -/

import D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDefs
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowThirtyTwoOneThreeSeries

open D5.S3.Combinatorics.ArrowThirtyTwoOneThreeDefs

noncomputable section

local notation "X" => (PowerSeries.X : PowerSeries ℤ)

/-- The branch selected by the first two coefficients is unique. -/
theorem cubic_solution_unique (G S : PowerSeries ℤ)
    (hG0 : PowerSeries.constantCoeff G = 1)
    (hS0 : PowerSeries.constantCoeff S = 1)
    (hG1 : PowerSeries.coeff 1 G = 1)
    (hS1 : PowerSeries.coeff 1 S = 1)
    (hG : 1 + (3 * X - 2) * G + (1 - X) * (1 - 2 * X) * G ^ 2 +
      X ^ 3 * G ^ 3 = 0)
    (hS : 1 + (3 * X - 2) * S + (1 - X) * (1 - 2 * X) * S ^ 2 +
      X ^ 3 * S ^ 3 = 0) : G = S := by
  let factor : PowerSeries ℤ :=
    (3 * X - 2) + (1 - X) * (1 - 2 * X) * (G + S) +
      X ^ 3 * (G ^ 2 + G * S + S ^ 2)
  have hfactor :
      (1 + (3 * X - 2) * G + (1 - X) * (1 - 2 * X) * G ^ 2 + X ^ 3 * G ^ 3) -
        (1 + (3 * X - 2) * S + (1 - X) * (1 - 2 * X) * S ^ 2 + X ^ 3 * S ^ 3) =
          (G - S) * factor := by
    dsimp [factor]
    ring
  have hprod : (G - S) * factor = 0 := by
    rw [← hfactor, hG, hS, sub_self]
  rcases (mul_eq_zero.mp hprod) with h | h
  · exact sub_eq_zero.mp h
  · have hc : PowerSeries.coeff 1 ((3 * X - 2) +
        (1 - X) * (1 - 2 * X) * (G + S) +
          X ^ 3 * (G ^ 2 + G * S + S ^ 2)) = -1 := by
      have hcoeff0 (f g : PowerSeries ℤ) :
          PowerSeries.coeff 0 (f * g) =
            PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
        rw [PowerSeries.coeff_mul]
        simp
      have hcoeff1 (f g : PowerSeries ℤ) :
          PowerSeries.coeff 1 (f * g) =
            PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
              PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
        rw [PowerSeries.coeff_mul]
        simp [Finset.antidiagonal]
      have hG0' : PowerSeries.coeff 0 G = 1 := by
        simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hG0
      have hS0' : PowerSeries.coeff 0 S = 1 := by
        simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hS0
      have hconst1 (a : ℤ) : PowerSeries.coeff 1 (a : PowerSeries ℤ) = 0 := by
        have hcast : (a : PowerSeries ℤ) = PowerSeries.C a :=
          (map_intCast (PowerSeries.C : ℤ →+* PowerSeries ℤ) a).symm
        rw [hcast, PowerSeries.coeff_C]
        simp
      have htwo1 : PowerSeries.coeff 1 (2 : PowerSeries ℤ) = 0 := by
        have hcast : (2 : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) :=
          (map_intCast (PowerSeries.C : ℤ →+* PowerSeries ℤ) 2).symm
        rw [hcast, PowerSeries.coeff_C]
        norm_num
      have htwoC : PowerSeries.constantCoeff (2 : PowerSeries ℤ) = 2 := by
        have hcast : (2 : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) :=
          (map_intCast (PowerSeries.C : ℤ →+* PowerSeries ℤ) 2).symm
        rw [hcast, PowerSeries.constantCoeff_C]
      have hthree0 : PowerSeries.coeff 0 (3 : PowerSeries ℤ) = 3 := by
        have hcast : (3 : PowerSeries ℤ) = PowerSeries.C (3 : ℤ) :=
          (map_intCast (PowerSeries.C : ℤ →+* PowerSeries ℤ) 3).symm
        rw [hcast, PowerSeries.coeff_C]
        norm_num
      have hthree1 : PowerSeries.coeff 1 (3 : PowerSeries ℤ) = 0 := by
        have hcast : (3 : PowerSeries ℤ) = PowerSeries.C (3 : ℤ) :=
          (map_intCast (PowerSeries.C : ℤ →+* PowerSeries ℤ) 3).symm
        rw [hcast, PowerSeries.coeff_C]
        norm_num
      have hA1 : PowerSeries.coeff 1 (3 * X - 2) = 3 := by
        rw [map_sub, hcoeff1]
        simp [PowerSeries.coeff_X, hconst1, htwo1, hthree0, hthree1]
      have he0 : PowerSeries.coeff 0 ((1 - X) * (1 - 2 * X)) = 1 := by
        rw [hcoeff0]
        simp
      have he1 : PowerSeries.coeff 1 ((1 - X) * (1 - 2 * X)) = -3 := by
        rw [hcoeff1]
        simp [htwo1, htwoC]
      have hE1 : PowerSeries.coeff 1
          (((1 - X) * (1 - 2 * X)) * (G + S)) = -4 := by
        rw [hcoeff1, map_add]
        rw [map_add, hG0', hS0', he0, he1, hG1, hS1]
        norm_num
      have hC1 : PowerSeries.coeff 1 (X ^ 3 * (G ^ 2 + G * S + S ^ 2)) = 0 := by
        rw [PowerSeries.coeff_X_pow_mul']
        simp
      rw [map_add, map_add, hA1, hE1, hC1]
      norm_num
    change PowerSeries.coeff 1 factor = -1 at hc
    rw [h] at hc
    simp at hc

end
end D5.S3.Combinatorics.ArrowThirtyTwoOneThreeSeries
