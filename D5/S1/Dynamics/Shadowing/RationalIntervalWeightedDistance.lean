/- GID: D5/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/RationalIntervalWeightedDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal all-integer geometric weighted distance and its one-sided tail bound. -/

import D5.S1.Dynamics.Shadowing.RationalIntervalAction
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! No replacement metric or additional metric-space instance is used. -/

open Set Filter
open scoped Topology BigOperators

namespace D5.S1.Dynamics.Shadowing.RationalInterval

/-- The original geometric weight at every integer coordinate. -/
noncomputable def geometricWeight (j : ℤ) : ℝ := (2 : ℝ) ^ (-(j.natAbs : ℤ))

private theorem geometricWeight_eq (j : ℤ) :
    geometricWeight j = (1 / 2 : ℝ) ^ j.natAbs := by
  rw [geometricWeight, zpow_neg, zpow_natCast, ← inv_pow]
  rw [one_div]

/-- The actual infinite sum in the self-tuning antecedent, for all integer coordinates. -/
noncomputable def weightedDistance (x y : ℤ → I) : ℝ :=
  ∑' j : ℤ, geometricWeight j * dist (x j) (y j)

private theorem geometricWeight_nonneg (j : ℤ) : 0 ≤ geometricWeight j := by
  unfold geometricWeight
  positivity

/-- The full integer weight series has sum three. -/
theorem geometricWeight_hasSum : HasSum geometricWeight 3 := by
  have hp : HasSum (fun n : ℕ => geometricWeight (n : ℤ)) 2 := by
    simpa only [geometricWeight_eq, Int.natAbs_natCast] using hasSum_geometric_two
  have hn : HasSum (fun n : ℕ => geometricWeight (-((n + 1 : ℕ) : ℤ))) 1 := by
    convert hasSum_geometric_two.mul_left (1 / 2 : ℝ) using 1
    · funext n
      rw [geometricWeight_eq]
      simp only [Int.natAbs_neg, Int.natAbs_natCast, pow_succ]
      ring
    · norm_num
  convert hp.of_nat_of_neg_add_one hn using 1
  norm_num

private theorem interval_dist_le_one (u v : I) : dist u v ≤ 1 := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_le]
  constructor <;> linarith [u.property.1, u.property.2, v.property.1, v.property.2]

/-- Every interval-valued sequence pair gives an actually summable distance series. -/
theorem weightedDistance_summable (x y : ℤ → I) :
    Summable (fun j : ℤ => geometricWeight j * dist (x j) (y j)) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (geometricWeight_nonneg j) dist_nonneg)
    (fun j => ?_) geometricWeight_hasSum.summable
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (interval_dist_le_one (x j) (y j))
    (geometricWeight_nonneg j)

/-- Product-topology continuity of the literal sum, with its summable uniform majorant. -/
theorem continuous_weightedDistance :
    Continuous (fun p : (ℤ → I) × (ℤ → I) => weightedDistance p.1 p.2) := by
  apply continuous_tsum
  · intro j
    exact continuous_const.mul (((continuous_apply j).comp continuous_fst).dist
      ((continuous_apply j).comp continuous_snd))
  · exact geometricWeight_hasSum.summable
  · intro j p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (geometricWeight_nonneg j) dist_nonneg)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (interval_dist_le_one (p.1 j) (p.2 j))
      (geometricWeight_nonneg j)

/-- The exact sum of weights strictly before the negative integer `-n`. -/
theorem geometricWeight_negative_tail (n : ℕ) :
    (∑' j : ℤ, if j < -(n : ℤ) then geometricWeight j else 0) = (1 / 2 : ℝ) ^ n := by
  let b : ℤ → ℝ := fun j => if j < -(n : ℤ) then geometricWeight j else 0
  have hb : Summable b := by
    apply Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      geometricWeight_hasSum.summable
    · dsimp only [b]
      split_ifs <;> first | exact le_refl 0 | exact geometricWeight_nonneg j
    · dsimp only [b]
      split_ifs <;> first | exact le_refl _ | exact geometricWeight_nonneg j
  rw [tsum_of_nat_of_neg_add_one (hb.comp_injective Nat.cast_injective)
    (hb.comp_injective (show Function.Injective (fun k : ℕ => -(k + 1 : ℤ)) from by
      intro a b h
      change -((a : ℤ) + 1) = -((b : ℤ) + 1) at h
      omega))]
  have hz : (∑' k : ℕ, b (k : ℤ)) = 0 := by
    have hzero : (fun k : ℕ => b (k : ℤ)) = fun _ => 0 := by
      funext k
      exact ite_eq_right (by omega)
    rw [hzero, tsum_zero]
  rw [hz, zero_add]
  have heq (k : ℕ) : b (-(k + 1 : ℤ)) =
      (1 / 2 : ℝ) * (if n ≤ k then (2 : ℝ)⁻¹ ^ k else 0) := by
    have habs : (-(k + 1 : ℤ)).natAbs = k + 1 := by omega
    simp only [b, geometricWeight_eq, habs]
    by_cases h : n ≤ k
    · rw [ite_eq_left (by omega), ite_eq_left h, pow_succ]
      simp only [one_div]
      ring
    · rw [ite_eq_right (by omega), ite_eq_right h, mul_zero]
  simp_rw [heq]
  rw [tsum_mul_left, tsum_geometric_inv_two_ge]
  simp only [one_div]
  ring

/-- Agreement on the entire half-line leaves at most the original geometric tail.
This controls the exact sum, including all infinitely many earlier discrepancies. -/
theorem weightedDistance_le_negative_tail (n : ℕ) (x y : ℤ → I)
    (hxy : ∀ j : ℤ, -(n : ℤ) ≤ j → x j = y j) :
    weightedDistance x y ≤ (1 / 2 : ℝ) ^ n := by
  rw [← geometricWeight_negative_tail]
  apply (weightedDistance_summable x y).tsum_le_tsum
  · intro j
    by_cases h : j < -(n : ℤ)
    · rw [ite_eq_left h]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (interval_dist_le_one (x j) (y j))
        (geometricWeight_nonneg j)
    · rw [ite_eq_right h, hxy j (le_of_not_gt h), dist_self, mul_zero]
  · apply Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
      geometricWeight_hasSum.summable
    · split_ifs <;> first | exact le_refl 0 | exact geometricWeight_nonneg j
    · split_ifs <;> first | exact le_refl _ | exact geometricWeight_nonneg j

#print axioms weightedDistance_summable
#print axioms continuous_weightedDistance
#print axioms weightedDistance_le_negative_tail

end D5.S1.Dynamics.Shadowing.RationalInterval
