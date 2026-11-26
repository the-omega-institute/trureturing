/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/GeometricTail
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The four-copy kernel with one distinguished node has a geometric tail expansion across lower spectral collisions. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
import Mathlib.Algebra.Field.GeomSum

namespace RefinedBMV

open Finset

private theorem geom_sum_eq_resolvent_sub_tail (x : ℝ) (hx : x ≠ 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) = (1 - x)⁻¹ - x ^ n * (1 - x)⁻¹ := by
  rw [geom_sum_eq hx]
  have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr hx.symm
  have hsub' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  <;> ring

open private FourCopyGap.sum_gaps_nested FourCopyGap.monomial FourCopyGap.balanced
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap in
/-- Completing the three lower geometric sums leaves three finite tail
terms. Their denominators remain regular when lower labels coincide. -/
theorem gapDefect_one_top_geometric_tail (p : ℕ) (x y z : ℝ)
    (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) :
    let rx := (1 - x)⁻¹
    let ry := (1 - y)⁻¹
    let rz := (1 - z)⁻¹
    FourCopyGap.gapDefect p x y z 1 =
      rx * ry * rz - x ^ (p + 1) * rx * ry * rz -
        (∑ i ∈ range (p + 1), x ^ i * y ^ (p - i + 1) * ry * rz) -
        (∑ i ∈ range (p + 1), ∑ j ∈ range (p - i + 1),
          x ^ i * y ^ j * (z ^ (p - i - j + 1) * rz)) -
        (FourCopyGap.gaps p).card * FourCopyGap.balanced p x y z 1 := by
  dsimp only
  have hsum (i : ℕ) :
      (∑ j ∈ range (p - i + 1), x ^ i * y ^ j * (1 - z)⁻¹) =
        (x ^ i * (1 - z)⁻¹) * ((1 - y)⁻¹ - y ^ (p - i + 1) * (1 - y)⁻¹) := by
    rw [← geom_sum_eq_resolvent_sub_tail y hy, mul_sum]
    exact sum_congr rfl fun j _ ↦ by ring
  have hxsum :
      (∑ i ∈ range (p + 1), x ^ i * (1 - z)⁻¹ * (1 - y)⁻¹) =
        ((1 - x)⁻¹ - x ^ (p + 1) * (1 - x)⁻¹) * (1 - z)⁻¹ * (1 - y)⁻¹ := by
    rw [← sum_mul, ← sum_mul, geom_sum_eq_resolvent_sub_tail x hx]
  rw [FourCopyGap.gapDefect, FourCopyGap.sum_gaps_nested]
  simp only [FourCopyGap.monomial, one_pow, mul_one, ← mul_sum]
  simp_rw [geom_sum_eq_resolvent_sub_tail z hz, mul_sub, sum_sub_distrib, hsum]
  simp_rw [mul_sub, sum_sub_distrib, hxsum]
  have hytail :
      (∑ i ∈ range (p + 1), x ^ i * (1 - z)⁻¹ * (y ^ (p - i + 1) * (1 - y)⁻¹)) =
        ∑ i ∈ range (p + 1), x ^ i * y ^ (p - i + 1) * (1 - y)⁻¹ * (1 - z)⁻¹ :=
    sum_congr rfl fun i _ ↦ by ring
  rw [hytail]
  ring

end RefinedBMV
