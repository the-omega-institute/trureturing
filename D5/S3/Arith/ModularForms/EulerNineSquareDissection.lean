/- GID: D5/S3/Arith/ModularForms/EulerNineSquareDissection
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/EulerNineSquareDissection
   mirror-E: none(waiver:actual-squared-euler-sign-dissection)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.Glaisher]
   utility: none
   digest: Cubic residue extraction and positive decompositions control the squared Euler sections. -/

import D5.S3.Arith.ModularForms.EulerNineDissection
import D5.S3.Arith.ModularForms.EtaSignK6

/-! The restricted-product cubic relation is derived from the actual cubic theta
supplier.  Its difficult squared section has a positive partition decomposition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.EulerNineSquareDissection

open CubicThetaIdentities CubicThetaLattice EulerNineDissection
open D5.S3.Combinatorics.Partitions.EulerNineComparison
open D5.S3.Combinatorics.Partitions.RestrictedEulerCancellation
open D5.S3.Combinatorics.Partitions.OrdinaryEulerProduct
open D5.S3.Combinatorics.PowerSeries.Trisection

private theorem R_cube_theta : R ^ 3 = B * expand3 (P ^ 2) := by
  simp only [R, B, map_pow]
  ring

/-- The relation B9²=A9 C9+X C9 D is extracted from the genuine theta
dissection and cancellation of the constant-one unit A9. -/
theorem restricted_cubic_relation :
    Q 2 ^ 2 = Q 4 * Q 1 + PowerSeries.X * Q 1 * D := by
  have ht : R ^ 3 = expand3 (normTheta * P ^ 2) +
      PowerSeries.X * expand3 (PowerSeries.C (-3) * (coreTheta * P ^ 2)) +
      PowerSeries.X ^ 2 * expand3 0 := by
    rw [R_cube_theta, B_dissection]
    simp only [map_mul, map_zero, mul_zero, add_zero, expand3, PowerSeries.expand_C,
      map_neg, map_ofNat]
    ring
  have hp : R ^ 3 =
      expand3 (Q 4 ^ 3 + 6 * PowerSeries.X * Q 4 * Q 2 * Q 1 -
        PowerSeries.X * Q 2 ^ 3 - PowerSeries.X ^ 2 * Q 1 ^ 3) +
      PowerSeries.X * expand3 (PowerSeries.C (-3) *
        (Q 4 ^ 2 * Q 2 - PowerSeries.X * Q 4 * Q 1 ^ 2 +
          PowerSeries.X * Q 2 ^ 2 * Q 1)) +
      PowerSeries.X ^ 2 * expand3 (PowerSeries.C 3 *
        (Q 4 * Q 2 ^ 2 - Q 4 ^ 2 * Q 1 - PowerSeries.X * Q 2 * Q 1 ^ 2)) := by
    rw [R_dissection]
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
      expand3, PowerSeries.expand_X, PowerSeries.expand_C]
    ring
  have hz : Q 4 * Q 2 ^ 2 - Q 4 ^ 2 * Q 1 - PowerSeries.X * Q 2 * Q 1 ^ 2 = 0 := by
    ext m
    have h := (coeff_three_components _ _ _ _ hp m).2.2
    have hzero := (coeff_three_components _ _ _ _ ht m).2.2
    rw [map_zero] at hzero
    rw [hzero, PowerSeries.coeff_C_mul] at h
    simp only [map_zero]
    nlinarith
  have hb : Q 4 * Q 2 ^ 2 = Q 4 ^ 2 * Q 1 + PowerSeries.X * Q 2 * Q 1 ^ 2 := by
    linear_combination hz
  have hn : Q 4 ≠ 0 := by
    intro he
    have hc : PowerSeries.constantCoeff (Q 4) = 1 := restricted_constant_one _
    rw [he, map_zero] at hc
    exact zero_ne_one hc
  apply mul_left_cancel₀ hn
  rw [hb]
  linear_combination -(PowerSeries.X * Q 1) * multiplicity_relation

noncomputable def U : PowerSeries ℚ := Q 4 ^ 2 + 2 * PowerSeries.X * Q 2 * Q 1
noncomputable def V : PowerSeries ℚ := 2 * Q 4 * Q 2 - PowerSeries.X * Q 1 ^ 2
noncomputable def W : PowerSeries ℚ := 2 * Q 4 * Q 1 - Q 2 ^ 2

private theorem Q_nonnegative (r n : ℕ) : 0 ≤ PowerSeries.coeff n (Q r) :=
  coeff_restricted_nonnegative _ n

private theorem coeff_A_ge_one (n : ℕ) : 1 ≤ PowerSeries.coeff n (Q 4) := by
  apply coeff_restricted_ge_one_of_parts _ n (Multiset.replicate n 1)
  · intro m hm
    have h := (Multiset.mem_replicate.mp hm).2
    omega
  · simp
  · intro m hm
    rw [(Multiset.mem_replicate.mp hm).2]
    norm_num

private theorem coeff_AB_ge_one (n : ℕ) : 1 ≤ PowerSeries.coeff n (Q 4 * Q 2) := by
  rw [mul_comm]
  exact (coeff_A_ge_one n).trans
    (coeff_mul_ge_right (Q_nonnegative 2) (Q_nonnegative 4) (restricted_constant_one _) n)

private theorem coeff_shift_nonnegative (H : PowerSeries ℚ)
    (hH : ∀ n, 0 ≤ PowerSeries.coeff n H) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (PowerSeries.X * H) := by
  rw [← pow_one (PowerSeries.X : PowerSeries ℚ), PowerSeries.coeff_X_pow_mul']
  split_ifs
  · exact hH _
  · exact le_rfl

theorem coeff_U_ge_one (n : ℕ) : 1 ≤ PowerSeries.coeff n U := by
  have hA : 1 ≤ PowerSeries.coeff n (Q 4 ^ 2) := by
    rw [pow_two]
    exact (coeff_A_ge_one n).trans
      (coeff_mul_ge_right (Q_nonnegative 4) (Q_nonnegative 4) (restricted_constant_one _) n)
  have hBC := coeff_shift_nonnegative (Q 2 * Q 1)
    (coeff_mul_nonnegative (Q_nonnegative 2) (Q_nonnegative 1)) n
  have he : U = Q 4 ^ 2 + PowerSeries.C 2 * (PowerSeries.X * (Q 2 * Q 1)) := by
    simp only [U, map_ofNat]
    ring
  rw [he, map_add, PowerSeries.coeff_C_mul]
  linarith

private theorem coeff_AB_sub_CC (n : ℕ) :
    0 ≤ PowerSeries.coeff n (Q 4 * Q 2 - Q 1 ^ 2) := by
  have he : Q 4 * Q 2 - Q 1 ^ 2 = (Q 4 - Q 1) * Q 2 + Q 1 * (Q 2 - Q 1) := by ring
  rw [he, map_add]
  apply add_nonneg
  · apply coeff_mul_nonnegative _ (Q_nonnegative 2) n
    intro m
    rw [map_sub, sub_nonneg]
    exact (coefficient_order m).1.trans (coefficient_order m).2
  · apply coeff_mul_nonnegative (Q_nonnegative 1) _ n
    intro m
    rw [map_sub, sub_nonneg]
    exact (coefficient_order m).1

private theorem coeff_cancelled_AB (n : ℕ) :
    0 ≤ PowerSeries.coeff n ((1 - PowerSeries.X) * (Q 4 * Q 2)) := by
  have hc := restricted_mul_one_sub
    (fun m => m % 9 ≠ 0 ∧ m % 9 ≠ 4 ∧ m % 9 ≠ 9 - 4) 1
    (by omega) (by norm_num)
  change Q 4 * (1 - PowerSeries.X ^ 1) = _ at hc
  rw [pow_one] at hc
  rw [show (1 - PowerSeries.X) * (Q 4 * Q 2) =
      Q 2 * (Q 4 * (1 - PowerSeries.X)) by ring, hc]
  exact coeff_mul_nonnegative (Q_nonnegative 2) (coeff_restricted_nonnegative _) n

theorem coeff_V_ge_one (n : ℕ) : 1 ≤ PowerSeries.coeff n V := by
  have he : V = Q 4 * Q 2 + (1 - PowerSeries.X) * (Q 4 * Q 2) +
      PowerSeries.X * (Q 4 * Q 2 - Q 1 ^ 2) := by dsimp only [V]; ring
  rw [he, map_add, map_add]
  have h1 := coeff_AB_ge_one n
  have h2 := coeff_cancelled_AB n
  have h3 := coeff_shift_nonnegative _ coeff_AB_sub_CC n
  linarith

/-- The difficult section is an exact sum of nonnegative actual products. -/
theorem W_positive_decomposition :
    W = lowerProduct + PowerSeries.X * (Q 4 * Q 1 - Q 1 * D) := by
  rw [W, restricted_cubic_relation, lowerProduct]
  ring

theorem W_initial : PowerSeries.constantCoeff W = 1 ∧ PowerSeries.coeff 1 W = 0 := by
  have hd : PowerSeries.constantCoeff (Q 4 * Q 1 - Q 1 * D) = 0 := by
    simp only [map_sub, map_mul, D, map_pow, Q, restricted_constant_one]
    norm_num
  rw [W_positive_decomposition]
  constructor
  · simp only [map_add, map_mul, PowerSeries.constantCoeff_X, zero_mul, add_zero]
    exact lowerProduct_initial.1
  · rw [map_add, PowerSeries.coeff_succ_X_mul, lowerProduct_initial.2,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hd, add_zero]

theorem coeff_W_ge_one (n : ℕ) (hn : n = 0 ∨ 2 ≤ n) : 1 ≤ PowerSeries.coeff n W := by
  rw [W_positive_decomposition, map_add]
  have h1 := coeff_lowerProduct_ge_one n hn
  have h2 := coeff_shift_nonnegative _ coeff_delta_nonnegative n
  linarith

theorem coeff_W_nonnegative (n : ℕ) : 0 ≤ PowerSeries.coeff n W := by
  by_cases hn : n = 1
  · rw [W_positive_decomposition, map_add]
    exact add_nonneg (coeff_lowerProduct_nonnegative n)
      (coeff_shift_nonnegative _ coeff_delta_nonnegative n)
  · exact (by norm_num : (0 : ℚ) ≤ 1).trans (coeff_W_ge_one n (by omega))

/-- The genuine squared Euler quotient has the U,-V,-W dissection. -/
theorem R_square_dissection : R ^ 2 =
    expand3 U - PowerSeries.X * expand3 V - PowerSeries.X ^ 2 * expand3 W := by
  rw [R_dissection]
  simp only [U, V, W, map_add, map_sub, map_mul, map_pow, map_ofNat,
    expand3, PowerSeries.expand_X]
  ring

end D5.S3.Arith.ModularForms.EulerNineSquareDissection
