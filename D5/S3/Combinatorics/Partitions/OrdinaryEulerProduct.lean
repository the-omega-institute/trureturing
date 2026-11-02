/- GID: D5/S3/Combinatorics/Partitions/OrdinaryEulerProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/OrdinaryEulerProduct
   mirror-E: none(waiver:ordinary-partition-euler-positivity)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.Glaisher, mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Ordinary partition Euler products and strict positive convolutions. -/

import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Positivity

/-! Ordinary partitions, without odd-part restrictions or a finite coefficient cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.Partitions.OrdinaryEulerProduct

open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def partitionSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((Nat.Partition.restricted n (fun _ => True)).card : ℚ)

theorem coeff_partitionSeries_ge_one (n : ℕ) : 1 ≤ PowerSeries.coeff n partitionSeries := by
  rw [partitionSeries, PowerSeries.coeff_mk]
  have h : 0 < (Nat.Partition.restricted n (fun _ => True)).card :=
    Finset.card_pos.mpr ⟨Nat.Partition.indiscrete n, by simp [Nat.Partition.restricted]⟩
  exact_mod_cast (show 1 ≤ (Nat.Partition.restricted n (fun _ => True)).card by omega)

theorem partitionSeries_mul_euler :
    partitionSeries * PowerSeries.pentagonalSeries ℚ = 1 := by
  letI : TopologicalSpace ℚ := ⊥
  letI : DiscreteTopology ℚ := ⟨rfl⟩
  have hp := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℚ (fun _ => True)
  simp only [ite_true] at hp
  have he := PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℚ
  have h := hp.mul he
  have hfactor (i : ℕ) :
      (∑' j : ℕ, (PowerSeries.X : PowerSeries ℚ) ^ ((i + 1) * j)) *
        (1 - PowerSeries.X ^ (i + 1)) = 1 := by
    simp_rw [pow_mul]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  simp_rw [hfactor] at h
  exact h.unique hasProd_one

theorem euler_constant_one : PowerSeries.constantCoeff (PowerSeries.pentagonalSeries ℚ) = 1 := by
  calc
    _ = PowerSeries.coeff 0 (PowerSeries.pentagonalSeries ℚ) :=
      (PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm
    _ = 1 := by
      have h := PowerSeries.coeff_pentagonalSeries_pentagonal ℚ 0
      rw [show _root_.pentagonal (0 : ℤ) = 0 by decide] at h
      simpa only [Int.coe_negOnePow, Int.natAbs_zero, pow_zero] using h

/-- Mathlib's ordinary partition product is the unit reciprocal of the actual Euler product. -/
theorem partitionSeries_eq_euler_inverse :
    partitionSeries = PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 := by
  have h := PowerSeries.mul_invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 euler_constant_one
  calc
    partitionSeries = partitionSeries *
        (PowerSeries.pentagonalSeries ℚ * PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1) :=
      by rw [h, mul_one]
    _ = (partitionSeries * PowerSeries.pentagonalSeries ℚ) *
        PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 := by ring
    _ = _ := by rw [partitionSeries_mul_euler, one_mul]

/-- Nonnegative coefficient series are closed under finite convolution. -/
theorem coeff_mul_nonnegative {H G : PowerSeries ℚ}
    (hH : ∀ n, 0 ≤ PowerSeries.coeff n H) (hG : ∀ n, 0 ≤ PowerSeries.coeff n G)
    (n : ℕ) : 0 ≤ PowerSeries.coeff n (H * G) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hH p.1) (hG p.2)

theorem coeff_pow_nonnegative {H : PowerSeries ℚ}
    (hH : ∀ n, 0 ≤ PowerSeries.coeff n H) (s n : ℕ) :
    0 ≤ PowerSeries.coeff n (H ^ s) := by
  induction s generalizing n with
  | zero => simp only [pow_zero, PowerSeries.coeff_one]; split_ifs <;> norm_num
  | succ s ih =>
    rw [pow_succ]
    exact coeff_mul_nonnegative (fun n => by simpa using ih n) hH n

/-- The distinguished constant term bounds the complete convolution at every degree. -/
theorem coeff_mul_ge_right {H G : PowerSeries ℚ}
    (hH : ∀ n, 0 ≤ PowerSeries.coeff n H) (hG : ∀ n, 0 ≤ PowerSeries.coeff n G)
    (hzero : PowerSeries.constantCoeff H = 1) (n : ℕ) :
    PowerSeries.coeff n G ≤ PowerSeries.coeff n (H * G) := by
  have ht : PowerSeries.coeff 0 H * PowerSeries.coeff n G ≤
      PowerSeries.coeff n (H * G) := by
    rw [PowerSeries.coeff_mul]
    exact Finset.single_le_sum (fun p _ => mul_nonneg (hH p.1) (hG p.2))
      (show (0, n) ∈ Finset.antidiagonal n by simp)
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hzero, one_mul] using ht

/-- Every positive finite power of the actual reciprocal Euler series has coefficients at least one. -/
theorem coeff_euler_inverse_pow_ge_one (s n : ℕ) (hs : 1 ≤ s) :
    1 ≤ PowerSeries.coeff n (PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 ^ s) := by
  rw [← partitionSeries_eq_euler_inverse]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  have hp : ∀ n, 0 ≤ PowerSeries.coeff n partitionSeries :=
    fun n => le_trans (by norm_num) (coeff_partitionSeries_ge_one n)
  have hz : PowerSeries.constantCoeff partitionSeries = 1 := by
    rw [partitionSeries_eq_euler_inverse, PowerSeries.constantCoeff_invOfUnit]
    rfl
  have hzero : PowerSeries.constantCoeff (partitionSeries ^ t) = 1 := by rw [map_pow, hz, one_pow]
  have h := coeff_mul_ge_right (fun n => coeff_pow_nonnegative hp t n) hp hzero n
  rw [show 1 + t = t + 1 by omega, pow_succ]
  exact (coeff_partitionSeries_ge_one n).trans h

end D5.S3.Combinatorics.Partitions.OrdinaryEulerProduct
