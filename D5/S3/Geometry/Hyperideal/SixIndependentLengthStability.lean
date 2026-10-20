/- GID: D5/S3/Geometry/Hyperideal/SixIndependentLengthStability
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/SixIndependentLengthStability
   mirror-E: none(waiver:quantitative-six-length-stability)
   anchors: []
   utility: none
   digest: Quantitative Cauchy stability for the six-independent-length determinant remainder. -/

import D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Hyperideal.SixIndependentLengthStability

open D5.S3.Geometry.Hyperideal.SixIndependentLengthRemainder

def asymmetrySize (xi zeta : Real) : Real := xi ^ 2 + zeta ^ 2

def stabilityCoefficient (r o A B : Real) : Real :=
  r * o - 1 + Real.sqrt ((A ^ 2 - B ^ 2) ^ 2 + (r - o) ^ 2)

def stabilityRadius (r o A B : Real) : Real :=
  Real.sqrt (stabilityCoefficient r o A B ^ 2 +
    L r o A B * M r o A B) - stabilityCoefficient r o A B

theorem asymmetry_remainder_le_envelope (r o A B xi zeta : Real) :
    Xi r o A B xi zeta ≤
      asymmetrySize xi zeta ^ 2 +
        2 * stabilityCoefficient r o A B * asymmetrySize xi zeta := by
  let t : Real := xi ^ 2 + zeta ^ 2
  let u : Real := A ^ 2 - B ^ 2
  let v : Real := r - o
  let x : Real := zeta ^ 2 - xi ^ 2
  let y : Real := 2 * xi * zeta
  let q : Real := u ^ 2 + v ^ 2
  let s : Real := Real.sqrt q
  let d : Real := u * x + v * y
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hxy : x ^ 2 + y ^ 2 = t ^ 2 := by
    dsimp [x, y, t]
    ring
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hs : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = q := by
    dsimp [s]
    exact Real.sq_sqrt hq
  have hdet_identity : q * t ^ 2 - d ^ 2 = (u * y - v * x) ^ 2 := by
    rw [← hxy]
    dsimp [q, d]
    ring
  have hdot_sq : d ^ 2 ≤ q * t ^ 2 := by
    nlinarith [sq_nonneg (u * y - v * x)]
  have hst : 0 ≤ s * t := mul_nonneg hs ht
  have hdot_le : d ≤ s * t := by
    by_contra hnot
    have hgt : s * t < d := lt_of_not_ge hnot
    have hsum : 0 < d + s * t := by linarith
    have hprod : 0 < (d - s * t) * (d + s * t) :=
      mul_pos (sub_pos.mpr hgt) hsum
    nlinarith [hs_sq, hdot_sq, hprod]
  have hx : x ^ 2 ≤ t ^ 2 := by
    nlinarith [sq_nonneg y, hxy]
  have hquad :
      2 * (r * o - 1) * t + 2 * d ≤
        2 * (r * o - 1 + s) * t := by
    dsimp [d]
    nlinarith [hdot_le]
  dsimp [Xi, asymmetrySize, stabilityCoefficient]
  dsimp [t, u, v, x, y, q, s] at hquad hx hs_sq
  nlinarith [hquad, hx, hxy]

theorem determinant_negative_of_stability_bound
    (r o A B xi zeta : Real)
    (hbound :
      asymmetrySize xi zeta ^ 2 +
          2 * stabilityCoefficient r o A B * asymmetrySize xi zeta <
        L r o A B * M r o A B) :
    (gram r o A B xi zeta).det < 0 := by
  rw [determinant_remainder_identity]
  have hXi := asymmetry_remainder_le_envelope r o A B xi zeta
  nlinarith

theorem stability_bound_iff_radius
    (r o A B xi zeta : Real)
    (hL : 0 < L r o A B)
    (hM : 0 < M r o A B)
    (hC : 0 < stabilityCoefficient r o A B) :
    asymmetrySize xi zeta < stabilityRadius r o A B ↔
      asymmetrySize xi zeta ^ 2 +
          2 * stabilityCoefficient r o A B * asymmetrySize xi zeta <
        L r o A B * M r o A B := by
  let t : Real := asymmetrySize xi zeta
  let C : Real := stabilityCoefficient r o A B
  let P : Real := L r o A B * M r o A B
  let s : Real := Real.sqrt (C ^ 2 + P)
  have ht : 0 ≤ t := by
    dsimp [t, asymmetrySize]
    positivity
  have hP : 0 < P := mul_pos hL hM
  have hs : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = C ^ 2 + P := by
    dsimp [s]
    exact Real.sq_sqrt (by nlinarith [sq_nonneg C, le_of_lt hP])
  have hC' : 0 < C := hC
  change t < s - C ↔ t ^ 2 + 2 * C * t < P
  constructor
  · intro h
    have hsum : t + C < s := by linarith
    have hsum_nonneg : 0 ≤ t + C := by linarith
    have hprod : 0 < (s - (t + C)) * (s + (t + C)) := by
      apply mul_pos
      · linarith
      · nlinarith
    nlinarith [hs_sq, hprod]
  · intro h
    have hsq : (t + C) ^ 2 < s ^ 2 := by
      nlinarith [hs_sq]
    have hsum : t + C < s := by
      by_contra hnot
      have hdiff : 0 ≤ t + C - s := by linarith
      have hsum_nonneg : 0 ≤ t + C + s := by linarith
      have hprod : 0 ≤ (t + C - s) * (t + C + s) :=
        mul_nonneg hdiff hsum_nonneg
      nlinarith
    linarith

#print axioms asymmetry_remainder_le_envelope
#print axioms determinant_negative_of_stability_bound
#print axioms stability_bound_iff_radius

end D5.S3.Geometry.Hyperideal.SixIndependentLengthStability
