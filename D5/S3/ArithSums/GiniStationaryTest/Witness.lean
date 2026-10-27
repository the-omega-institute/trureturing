/- GID: D5/S3/ArithSums/GiniStationaryTest/Witness
   generality: I
   mirror-B: D5/B/S3/ArithSums/GiniStationaryTest/Witness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A one-small-coordinate family reverses the proposed Gini comparison. -/

import D5.S3.ArithSums.GiniStationaryTest.Defs

/-! A strict comparison family at a tuple with one small coordinate. -/

noncomputable section
open scoped BigOperators
open D5.S3.ArithSums.GiniMeanEndpointComparison (highTuple)
open D5.S3.ArithSums.GiniStationaryTest.Defs

namespace D5.S3.ArithSums.GiniStationaryTest.Witness

/-- The exact numerator of the cubed comparison. -/
theorem witness_identity (t k : ℝ) :
    (t + k) ^ 3 * (1 + k * t) - (k + 1) ^ 3 * t * (t ^ 2 + k) =
      k * (t - 1) ^ 3 * (t - k ^ 2) := by
  ring

lemma sum_highTuple_rpow (m : ℕ) (t p : ℝ) :
    (∑ i : Fin (m + 1), highTuple (m + 1) t 1 i ^ p) = t ^ p + m := by
  simp [highTuple, Fin.sum_univ_succ]

/-- Every positive small coordinate below one gives a strict reversal. -/
theorem witness_comparison (n : ℕ) (hn : 3 ≤ n) (t : ℝ)
    (ht : 0 < t) (ht1 : t < 1) :
    giniMean 2 (-1) (highTuple n t 1) < giniMean 1 0 (highTuple n t 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hm0 : (0 : ℝ) < m := by linarith
  have hsum1 := sum_highTuple_rpow m t 1
  have hsum0 := sum_highTuple_rpow m t 0
  have hsum2 := sum_highTuple_rpow m t 2
  have hsumNeg := sum_highTuple_rpow m t (-1)
  simp only [Real.rpow_one] at hsum1
  simp only [Real.rpow_zero] at hsum0
  simp only [Real.rpow_two] at hsum2
  simp only [Real.rpow_neg_one] at hsumNeg
  have hmean : giniMean 1 0 (highTuple (m + 1) t 1) = (t + m) / (m + 1) := by
    simp [giniMean, GiniMeanEndpointComparison.giniMean, hsum1, hsum0, add_comm]
  have hother : giniMean 2 (-1) (highTuple (m + 1) t 1) =
      ((t ^ 2 + m) / (t⁻¹ + m)) ^ (1 / (3 : ℝ)) := by
    simp only [giniMean, if_neg (by norm_num : (2 : ℝ) ≠ -1),
      GiniMeanEndpointComparison.giniMean, Real.rpow_two, Real.rpow_neg_one, hsum2, hsumNeg]
    norm_num
  rw [hmean, hother]
  have hden : 0 < t⁻¹ + (m : ℝ) := by positivity
  have hbase : 0 < (t ^ 2 + m) / (t⁻¹ + m) := by positivity
  have hfactor : 0 < (m : ℝ) * (t - 1) ^ 3 * (t - (m : ℝ) ^ 2) := by
    have hneg : t - (m : ℝ) ^ 2 < 0 := by nlinarith
    have hcneg : (t - 1) ^ 3 < 0 := (by decide : Odd 3).pow_neg (by linarith)
    exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hm0 hcneg) hneg
  have hid := witness_identity t m
  have hrat : (t ^ 2 + m) / (t⁻¹ + m) < ((t + m) / (m + 1)) ^ (3 : ℕ) := by
    rw [div_pow, div_lt_div_iff₀ hden (by positivity)]
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hid' : 0 < (t + m) ^ 3 * (1 + (m : ℝ) * t) -
        ((m : ℝ) + 1) ^ 3 * t * (t ^ 2 + m) := by rw [hid]; exact hfactor
    have he : t * ((t + m) ^ 3 * (t⁻¹ + m) -
        (t ^ 2 + m) * ((m : ℝ) + 1) ^ 3) =
        (t + m) ^ 3 * (1 + (m : ℝ) * t) -
        ((m : ℝ) + 1) ^ 3 * t * (t ^ 2 + m) := by
      field_simp
      <;> ring
    exact sub_pos.mp ((mul_pos_iff_of_pos_left ht).mp (he.symm ▸ hid'))
  simpa only [one_div, Real.rpow_natCast] using
    (Real.rpow_inv_lt_iff_of_pos hbase.le
      (by positivity : 0 ≤ (t + (m : ℝ)) / (m + 1))
      (by norm_num : (0 : ℝ) < 3)).2 (by
        change _ < _ ^ ((3 : ℕ) : ℝ)
        rw [Real.rpow_natCast]
        exact hrat)

/-- The comparison fails on the positive half-line for every dimension at least three. -/
theorem not_mem_Gamma (n : ℕ) (hn : 3 ≤ n) :
    (((1, 0), (2, -1)) : (ℝ × ℝ) × (ℝ × ℝ)) ∉ Gamma n (Set.Ioi 0) := by
  intro h
  have hx : ∀ i, highTuple n (1 / 2 : ℝ) 1 i ∈ Set.Ioi 0 := by
    intro i
    simp only [highTuple]
    split_ifs <;> norm_num
  exact (not_le_of_gt (witness_comparison n hn (1 / 2) (by norm_num) (by norm_num)))
    (h _ hx)

end D5.S3.ArithSums.GiniStationaryTest.Witness
