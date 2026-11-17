/- GID: D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/HalvingPartitionDeficit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Stern deficit on binary 10...01, its even dilates and real logarithmic asymptotic. -/

import D5.S1.Recurrence.Partitions.HalvingPartitionDilation
import D5.S1.Recurrence.Partitions.HalvingPartitionGrowth
import D5.S3.PrimeForms.SternBrocot.AdamsonSternFareyInverse

/-! This specializes the deficit direction of Alekseyev (2026), Section 6.
It does not give a general digit formula or an exact fixed-bit maximum. -/

namespace D5.S3.Combinatorics.Partitions.HalvingPartitionDeficit

open D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
open D5.S3.PrimeForms.SternBrocot.AdamsonSternFareyInverse

/-- The actual Stern sequence minus the actual halving-list count. -/
noncomputable def deficit (n : ℕ) : ℕ := stern n - count n

private theorem stern_power_two (m : ℕ) : stern (2 ^ m) = 1 := by
  induction m with
  | zero => simpa using stern_one
  | succ m ih => rw [pow_succ, Nat.mul_comm, stern_even, ih]

/-- The dyadic successor value of the already published Stern recursion. -/
theorem stern_dyadic_successor (m : ℕ) : stern (2 ^ m + 1) = m + 1 := by
  induction m with
  | zero => simpa only [pow_zero, Nat.reduceAdd, stern_one] using stern_even 1
  | succ m ih =>
    rw [pow_succ, Nat.mul_comm, stern_odd, stern_power_two, ih]
    omega

/-- Exact natural subtraction, including m=2. -/
theorem deficit_dyadic (m : ℕ) (hm : 2 ≤ m) :
    deficit (2 ^ m + 1) = m - 2 - thresholdCount m := by
  unfold deficit
  rw [stern_dyadic_successor, dyadic_source_count m hm]
  change m + 1 - (3 + thresholdCount m) = m - 2 - thresholdCount m
  omega

/-- All even dilates of the same binary family have the identical deficit. -/
theorem deficit_dyadic_dilation (m v : ℕ) (hm : 2 ≤ m) :
    deficit (2 ^ v * (2 ^ m + 1)) = m - 2 - thresholdCount m := by
  have hs (n v : ℕ) : stern (2 ^ v * n) = stern n := by
    induction v with
    | zero => simp
    | succ v ih =>
      rw [pow_succ, show 2 ^ v * 2 * n = 2 * (2 ^ v * n) by ring, stern_even, ih]
  unfold deficit
  rw [hs, count_even_dilation]
  exact deficit_dyadic m hm

/-- The manuscript's two sharp floor-log deficit bounds. -/
theorem deficit_log_bounds (m : ℕ) (hm : 4 ≤ m) :
    m - Nat.log2 m - 2 ≤ deficit (2 ^ m + 1) ∧
      deficit (2 ^ m + 1) ≤ m - Nat.log2 m - 1 := by
  rw [deficit_dyadic m (by omega)]
  have hr := thresholdCount_log_bounds m hm
  omega

private theorem thresholdCount_add_two_le (m : ℕ) (hm : 2 ≤ m) :
    thresholdCount m + 2 ≤ m := by
  by_cases hz : thresholdCount m = 0
  · omega
  · have ht := (threshold_iff_le_count m (thresholdCount m)).mpr ⟨by omega, le_rfl⟩
    have hp : 0 < (2 : ℕ) ^ thresholdCount m := by positivity
    omega

/-- A bounded error against the ordinary real logarithm, with exact source counts. -/
theorem deficit_real_log_bound (m : ℕ) (hm : 4 ≤ m) :
    |(deficit (2 ^ m + 1) : ℝ) - ((m : ℝ) - Real.logb 2 m)| ≤ 4 := by
  have hc : count (2 ^ m + 1) ≤ m + 1 := by
    rw [dyadic_source_count m (by omega)]
    have hr := thresholdCount_add_two_le m (by omega)
    change 3 + thresholdCount m ≤ m + 1
    omega
  have hd : (deficit (2 ^ m + 1) : ℝ) = (m : ℝ) + 1 - count (2 ^ m + 1) := by
    unfold deficit
    rw [stern_dyadic_successor, Nat.cast_sub hc, Nat.cast_add, Nat.cast_one]
  rw [hd]
  have hb := (abs_le.mp (dyadic_count_real_log_bound m hm))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- d(2^m+1)=m-log_2(m)+O(1), in the standard atTop sense. -/
theorem deficit_log_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun m : ℕ => (deficit (2 ^ m + 1) : ℝ) - ((m : ℝ) - Real.logb 2 m))
      (fun _ : ℕ => (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (4 : ℝ)
  apply Filter.eventually_atTop.mpr
  refine ⟨4, fun m hm => ?_⟩
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using deficit_real_log_bound m hm

end D5.S3.Combinatorics.Partitions.HalvingPartitionDeficit
