/- GID: D5/S3/Arith/ArtinSchreierQuadraticRootUniqueness
   generality: I
   mirror-B: D5/B/S3/Arith/ArtinSchreierQuadraticRootUniqueness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A characteristic-two quadratic equation has at most one root with a fixed constant coefficient. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

open PowerSeries

namespace D5.S3.Arith.ArtinSchreierQuadraticRootUniqueness

/-- Two roots of the same Artin--Schreier equation over a characteristic-two
power-series ring are equal when their constant coefficients agree. -/
theorem eq_of_square_add_eq_square_add
    {R : Type*} [CommRing R] [CharP R 2]
    (F G f : PowerSeries R)
    (hF : F ^ 2 + F = f) (hG : G ^ 2 + G = f)
    (h0 : constantCoeff F = constantCoeff G) :
    F = G := by
  let D := F + G
  have series_two_eq_zero : (2 : PowerSeries R) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := R)) (CharTwo.two_eq_zero (R := R))
  have series_add_self_eq_zero (H : PowerSeries R) : H + H = 0 := by
    ext n
    simpa only [map_add, map_zero] using CharTwo.add_self_eq_zero (coeff n H)
  have hD : D ^ 2 + D = 0 := by
    calc
      D ^ 2 + D = (F ^ 2 + F) + (G ^ 2 + G) + (2 : PowerSeries R) * F * G := by
        simp only [D]
        ring
      _ = (F ^ 2 + F) + (G ^ 2 + G) := by
        rw [series_two_eq_zero, zero_mul, zero_mul, add_zero]
      _ = f + f := by rw [hF, hG]
      _ = 0 := series_add_self_eq_zero f
  have hu : IsUnit (D + 1) := by
    rw [isUnit_iff_constantCoeff]
    convert isUnit_one
    simp [D, h0, CharTwo.add_self_eq_zero]
  have hprod : D * (D + 1) = 0 := by
    calc
      D * (D + 1) = D ^ 2 + D := by ring
      _ = 0 := hD
  have hDz : D = 0 := by
    apply hu.mul_right_cancel
    simpa using hprod
  change F + G = 0 at hDz
  calc
    F = (F + G) + G := by rw [add_assoc, series_add_self_eq_zero, add_zero]
    _ = G := by rw [hDz, zero_add]

#print axioms eq_of_square_add_eq_square_add

end D5.S3.Arith.ArtinSchreierQuadraticRootUniqueness
