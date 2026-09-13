/- GID: D5/S3/ArithSums/SimicWeightedPowerSumFloorIdentity
   generality: G
   mirror-B: D5/B/S3/ArithSums/SimicWeightedPowerSumFloorIdentity
   mirror-E: none(waiver:unbounded-symbolic-floor-identity)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Floor.Ring, mathlib/module/Mathlib.Data.Finset.Max, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Simic H-655(ii) weighted power-sum floor identity for at least two indices. -/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S3.ArithSums.SimicWeightedPowerSumFloorIdentity

/-- Simic's Fibonacci Quarterly Problem H-655(ii), with the necessary exclusion of
the singleton case. -/
theorem simic_h655_ii (s : Finset ℕ) (hs : 2 ≤ s.card)
    (h1 : ∀ i ∈ s, 1 ≤ i) (q : ℕ) (hq : 2 ≤ q) :
    ⌊((q : ℚ) - 1) * (∑ i ∈ s, (i : ℚ) * (q : ℚ) ^ i) /
        (∑ i ∈ s, (q : ℚ) ^ i)⌋ =
      (s.max' (Finset.card_pos.mp (by omega)) : ℤ) * ((q : ℤ) - 1) - 1 := by
  classical
  have tail_sum_identity (c : ℕ) :
      (∑ i ∈ Finset.range c,
          (((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i) =
        (q : ℚ) ^ c - (c + 1 : ℕ) := by
    induction c with
    | zero => simp
    | succ c ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range c,
              (((q : ℚ) - 1) * ((c + 1 - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i) +
            (((q : ℚ) - 1) * ((c + 1 - c : ℕ) : ℚ) - 1) * (q : ℚ) ^ c =
            (∑ i ∈ Finset.range c,
              ((((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i +
                ((q : ℚ) - 1) * (q : ℚ) ^ i)) +
              ((q : ℚ) - 2) * (q : ℚ) ^ c := by
                congr 1
                · apply Finset.sum_congr rfl
                  intro i hi
                  have hic : i < c := Finset.mem_range.mp hi
                  have hsub : c + 1 - i = (c - i) + 1 := by omega
                  rw [hsub]
                  push_cast
                  ring
                · have hsub : c + 1 - c = 1 := by omega
                  rw [hsub]
                  push_cast
                  ring
        _ = (∑ i ∈ Finset.range c,
              (((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i) +
              ((q : ℚ) - 1) * (∑ i ∈ Finset.range c, (q : ℚ) ^ i) +
              ((q : ℚ) - 2) * (q : ℚ) ^ c := by
                rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = (q : ℚ) ^ (c + 1) - ((c + 1) + 1 : ℕ) := by
              rw [ih, mul_geom_sum]
              push_cast
              rw [pow_succ]
              ring
  sorry

#print axioms simic_h655_ii

end D5.S3.ArithSums.SimicWeightedPowerSumFloorIdentity
