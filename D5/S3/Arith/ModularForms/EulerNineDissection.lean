/- GID: D5/S3/Arith/ModularForms/EulerNineDissection
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/EulerNineDissection
   mirror-E: none(waiver:actual-euler-quotient-dissection)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.Glaisher]
   utility: none
   digest: The actual Euler quotient has three restricted partition sections. -/

import D5.S3.Arith.ModularForms.EulerPentagonalTrisection
import D5.S3.Combinatorics.Partitions.EulerNineComparison
import D5.S3.Arith.ModularForms.CubicThetaIdentities

/-! Cancelling the actual partition geometric factors identifies the weighted
Jacobi sections with E times Q, rather than assuming an R dissection. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.EulerNineDissection

open WeightedJacobiSpecialization EulerPentagonalTrisection CubicThetaIdentities
open D5.S3.Combinatorics.Partitions.EulerNineComparison
open D5.S3.Combinatorics.Partitions.RestrictedEulerCancellation
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

private local instance : UniformSpace ℚ := ⊥
private local instance : DiscreteUniformity ℚ := ⟨rfl⟩

private noncomputable def filteredFactor (r i : ℕ) : PowerSeries ℚ := by
  classical
  exact if (i + 1) % 9 ≠ 0 ∧ (i + 1) % 9 ≠ r ∧ (i + 1) % 9 ≠ 9 - r
    then 1 else 1 - PowerSeries.X ^ (i + 1)

private theorem hasProd_filtered (r : ℕ) : HasProd (filteredFactor r) (E * Q r) := by
  classical
  let p : ℕ → Prop := fun m => m % 9 ≠ 0 ∧ m % 9 ≠ r ∧ m % 9 ≠ 9 - r
  have hp : HasProd (fun i => if p (i + 1) then
      ∑' j : ℕ, (PowerSeries.X : PowerSeries ℚ) ^ ((i + 1) * j) else 1) (Q r) := by
    simpa only [Q, restrictedSeries, Nat.Partition.restricted, Finset.filter_congr_decidable]
      using Nat.Partition.hasProd_powerSeriesMk_card_restricted ℚ p
  have he := PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℚ
  apply (he.mul hp).congr_fun
  intro i
  by_cases hi : p (i + 1)
  · simp only [if_pos hi]
    rw [mul_comm]
    simp_rw [pow_mul]
    have hg := PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
      (f := (PowerSeries.X : PowerSeries ℚ) ^ (i + 1))
      (by simp only [map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega : i + 1 ≠ 0)])
    simpa only [filteredFactor, p, if_pos hi] using hg.symm
  · simp only [if_neg hi, mul_one]
    simp only [filteredFactor, p, if_neg hi]

private theorem finite_filtered (r N : ℕ) (hr : r = 1 ∨ r = 2 ∨ r = 4) :
    (∏ i ∈ Finset.range (9 * N), filteredFactor r i) = finiteProduct (8 - r) r N := by
  induction N with
  | zero => simp [finiteProduct]
  | succ N ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih]
    simp only [finiteProduct, Finset.prod_range_succ]
    rcases hr with rfl | rfl | rfl
    all_goals
      norm_num [filteredFactor, Finset.prod_range_succ, Nat.add_mod, Nat.mul_mod,
        Nat.mul_add, Nat.add_assoc]
      ring

/-- All filtered Euler factors and all reciprocal factors occur with their
actual multiplicities.  Finite blocks converge to the same product. -/
theorem J_eq_euler_mul_Q (r : ℕ) (hr : r = 1 ∨ r = 2 ∨ r = 4) :
    J (8 - r) r = E * Q r := by
  have hg : Filter.Tendsto (fun N : ℕ => 9 * N) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact Filter.eventually_atTop.2 ⟨b, by intro n hn; omega⟩
  have hp := (hasProd_filtered r).tendsto_prod_nat.comp hg
  have hp' : Filter.Tendsto (finiteProduct (8 - r) r) Filter.atTop (nhds (E * Q r)) := by
    simpa only [Function.comp_def, finite_filtered r _ hr] using hp
  exact tendsto_nhds_unique (tendsto_finiteProduct (8 - r) r) hp'

theorem J_mul_inverse (r : ℕ) (hr : r = 1 ∨ r = 2 ∨ r = 4) :
    J (8 - r) r * P = Q r := by
  rw [J_eq_euler_mul_Q r hr]
  calc
    E * Q r * P = (E * P) * Q r := by ring
    _ = Q r := by rw [euler_mul_inverse, one_mul]

noncomputable def R : PowerSeries ℚ := E * expand3 P

/-- Exact all-degree dissection of E(q)/E(q^3), with the original signs. -/
theorem R_dissection : R =
    expand3 (Q 4) - PowerSeries.X * expand3 (Q 2) -
      PowerSeries.X ^ 2 * expand3 (Q 1) := by
  have h4 : J 4 4 * P = Q 4 := by simpa using J_mul_inverse 4 (by omega)
  have h2 : J 6 2 * P = Q 2 := by simpa using J_mul_inverse 2 (by omega)
  have h1 : J 7 1 * P = Q 1 := by simpa using J_mul_inverse 1 (by omega)
  calc
    R = (expand3 (J 4 4) - PowerSeries.X * expand3 (J 6 2) -
        PowerSeries.X ^ 2 * expand3 (J 7 1)) * expand3 P := by
      rw [R, ← euler_three_sections]
    _ = expand3 (J 4 4 * P) - PowerSeries.X * expand3 (J 6 2 * P) -
        PowerSeries.X ^ 2 * expand3 (J 7 1 * P) := by simp only [map_mul]; ring
    _ = _ := by rw [h4, h2, h1]

end D5.S3.Arith.ModularForms.EulerNineDissection
