/- GID: D5/S3/Arith/ModularForms/CubicThetaIdentities
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaIdentities
   mirror-E: none(waiver:formal-cubic-theta-identities)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: The actual Euler quotients satisfy both classical cubic theta identities. -/

import D5.S3.Arith.ModularForms.CubicThetaWeightedProduct
import D5.S3.Combinatorics.Partitions.OrdinaryEulerProduct
import D5.S3.Combinatorics.PowerSeries.ExpandingRecurrence

/-! The two classical cubic theta identities follow from genuine Euler products, complete lattices, and expanding coefficient induction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaIdentities

open CubicThetaLattice CubicThetaCoreProduct CubicThetaWeightedProduct
open D5.S3.Combinatorics.PowerSeries.ExpandingRecurrence
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable abbrev E : PowerSeries ℚ := PowerSeries.pentagonalSeries ℚ
noncomputable abbrev P : PowerSeries ℚ := PowerSeries.invOfUnit E 1
noncomputable abbrev expand3 : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := PowerSeries.expand 3 (by decide)
noncomputable def B : PowerSeries ℚ := E ^ 3 * expand3 P

theorem euler_mul_inverse : E * P = 1 :=
  PowerSeries.mul_invOfUnit _ 1 CubicThetaCoreProduct.euler_constant_one

theorem core_eq_product : coreTheta = expand3 E ^ 3 * P := core_product_eq_theta.symm

/-- This first cubic identity identifies an actual Euler quotient with the lattice dissection. -/
theorem B_dissection : B = expand3 normTheta - 3 * PowerSeries.X * expand3 coreTheta := by
  have hunit : expand3 E * expand3 P = 1 := by rw [← map_mul, euler_mul_inverse, map_one]
  have h := congrArg (fun v : PowerSeries ℚ => v * expand3 P) norm_dissection_mul_euler
  rw [mul_assoc, hunit, mul_one] at h
  simpa only [B, expand3, map_ofNat, mul_assoc] using h.symm

/-- The quotient multiplication law is proved using only the two actual unit inverses. -/
theorem quotient_multiplication : B * coreTheta ^ 3 = expand3 coreTheta * expand3 B ^ 3 := by
  have hunit : expand3 E * expand3 P = 1 := by rw [← map_mul, euler_mul_inverse, map_one]
  have hunit9 : expand3 (expand3 E) * expand3 (expand3 P) = 1 := by
    rw [← map_mul, ← map_mul, euler_mul_inverse, map_one, map_one]
  rw [B, core_eq_product]
  simp only [map_mul, map_pow]
  calc
    _ = expand3 E ^ 9 * expand3 P * (E * P) ^ 3 := by ring
    _ = expand3 E ^ 8 := by
      rw [euler_mul_inverse, one_pow, mul_one]
      calc
        _ = expand3 E ^ 8 * (expand3 E * expand3 P) := by ring
        _ = _ := by rw [hunit, mul_one]
    _ = expand3 E ^ 9 * expand3 P *
        (expand3 (expand3 E) * expand3 (expand3 P)) ^ 3 := by
      rw [hunit9, one_pow, mul_one]
      calc
        _ = expand3 E ^ 8 * (expand3 E * expand3 P) := by rw [hunit, mul_one]
        _ = _ := by ring
    _ = _ := by ring

/-- The cubic defect satisfies a positive-degree expanding homogeneous recurrence. -/
theorem cubic_defect_recurrence :
    let D := normTheta ^ 3 - B ^ 3 - 27 * PowerSeries.X * coreTheta ^ 3
    B * D = PowerSeries.X * (27 * expand3 coreTheta) * expand3 D := by
  dsimp only
  simp only [map_sub, map_pow, map_mul, map_ofNat, expand3, PowerSeries.expand_X]
  have hA := norm_theta_dissection
  have hB := B_dissection
  have hQ := quotient_multiplication
  change normTheta = expand3 normTheta + PowerSeries.C 6 *
    (PowerSeries.X * expand3 coreTheta) at hA
  simp only [map_ofNat] at hA
  change B = expand3 normTheta - 3 * PowerSeries.X * expand3 coreTheta at hB
  change B * coreTheta ^ 3 = expand3 coreTheta * expand3 B ^ 3 at hQ
  change B * (normTheta ^ 3 - B ^ 3 - 27 * PowerSeries.X * coreTheta ^ 3) =
    PowerSeries.X * (27 * expand3 coreTheta) *
      (expand3 normTheta ^ 3 - expand3 B ^ 3 -
        27 * PowerSeries.X ^ 3 * expand3 coreTheta ^ 3)
  linear_combination
    (B * (normTheta ^ 2 + normTheta * (expand3 normTheta + 6 * PowerSeries.X * expand3 coreTheta) +
      (expand3 normTheta + 6 * PowerSeries.X * expand3 coreTheta) ^ 2)) * hA -
    ((B ^ 3 + B ^ 2 * (expand3 normTheta - 3 * PowerSeries.X * expand3 coreTheta) +
      B * (expand3 normTheta - 3 * PowerSeries.X * expand3 coreTheta) ^ 2 +
      (expand3 normTheta - 3 * PowerSeries.X * expand3 coreTheta) ^ 3) -
      (expand3 normTheta + 6 * PowerSeries.X * expand3 coreTheta) ^ 3) * hB -
    27 * PowerSeries.X * hQ

/-- Both sides are the actual classical series; coefficient induction closes every degree. -/
theorem cubic_identity : normTheta ^ 3 = B ^ 3 + 27 * PowerSeries.X * coreTheta ^ 3 := by
  have hB : PowerSeries.constantCoeff B = 1 := by
    rw [B, map_mul, map_pow, CubicThetaCoreProduct.euler_constant_one]
    simp only [expand3, PowerSeries.constantCoeff_expand, PowerSeries.constantCoeff_invOfUnit]
    norm_num
  have h := eq_zero_of_mul_eq_X_expand B
    (normTheta ^ 3 - B ^ 3 - 27 * PowerSeries.X * coreTheta ^ 3)
    (27 * expand3 coreTheta) 3 (by decide) hB cubic_defect_recurrence
  exact sub_eq_zero.mp (show normTheta ^ 3 - (B ^ 3 + 27 * PowerSeries.X * coreTheta ^ 3) = 0 by
    simpa only [sub_sub] using h)

end D5.S3.Arith.ModularForms.CubicThetaIdentities
