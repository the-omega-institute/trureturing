/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionGrowth
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp floor-log dyadic count bounds and the ordinary real-log bounded-error asymptotic. -/

import D5.S1.Recurrence.Partitions.HalvingPartitionProfile
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Asymptotics.Defs

/-! Exact floor logarithms and a genuine real logarithm bridge. -/

namespace D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

/-- The threshold count is either floor(log2 m)-1 or floor(log2 m). -/
theorem thresholdCount_log_bounds (m : ℕ) (hm : 4 ≤ m) :
    Nat.log2 m - 1 ≤ thresholdCount m ∧ thresholdCount m ≤ Nat.log2 m := by
  rw [Nat.log2_eq_log_two]
  let h := Nat.log 2 m
  have hh : 2 ≤ h := Nat.le_log_of_pow_le (by decide) (by simpa using hm)
  have hp : 2 ^ h ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hsmall : h ≤ 2 ^ (h - 1) := by
    have := Nat.lt_two_pow_self (n := h - 1)
    omega
  have hp2 : 2 ^ h = 2 ^ (h - 1) * 2 := by
    have he : h = (h - 1) + 1 := by omega
    calc
      _ = 2 ^ ((h - 1) + 1) := congrArg (fun x => (2 : ℕ) ^ x) he
      _ = _ := pow_succ _ _
  constructor
  · have ht : 1 ≤ h - 1 ∧ 2 ^ (h - 1) + (h - 1) + 1 ≤ m := by omega
    exact ((threshold_iff_le_count m (h - 1)).mp ht).2
  · by_cases hz : thresholdCount m = 0
    · omega
    · have ht := ((threshold_iff_le_count m (thresholdCount m)).mpr ⟨by omega, le_rfl⟩).2
      exact Nat.le_log_of_pow_le (by decide) (by omega)

/-- Sharp floor-log bounds, at every m at least four. -/
theorem dyadic_count_log_bounds (m : ℕ) (hm : 4 ≤ m) :
    Nat.log2 m + 2 ≤ count (2 ^ m + 1) ∧
      count (2 ^ m + 1) ≤ Nat.log2 m + 3 := by
  have ht := thresholdCount_log_bounds m hm
  rw [dyadic_source_count m (by omega)]
  change Nat.log2 m + 2 ≤ 3 + thresholdCount m ∧
    3 + thresholdCount m ≤ Nat.log2 m + 3
  omega

/-- Ordinary real log base two differs from the count by at most three. -/
theorem dyadic_count_real_log_bound (m : ℕ) (hm : 4 ≤ m) :
    |(count (2 ^ m + 1) : ℝ) - Real.logb 2 m| ≤ 3 := by
  have hb := dyadic_count_log_bounds m hm
  have hlo := Real.log2_le_logb m
  have hhi : Real.logb 2 m < (Nat.log2 m : ℝ) + 1 := by
    have he := Nat.lt_floor_add_one (Real.logb 2 (m : ℝ))
    have hf : ⌊Real.logb 2 (m : ℝ)⌋₊ = Nat.log2 m := by
      simpa only [Nat.cast_ofNat, Nat.log2_eq_log_two] using Real.natFloor_logb_natCast 2 m
    rwa [hf] at he
  have hb0 : (Nat.log2 m : ℝ) + 2 ≤ count (2 ^ m + 1) := by exact_mod_cast hb.1
  have hb1 : (count (2 ^ m + 1) : ℝ) ≤ (Nat.log2 m : ℝ) + 3 := by exact_mod_cast hb.2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- b_m=log_2(m)+O(1), with real logarithm and the usual atTop filter. -/
theorem dyadic_count_log_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun m : ℕ => (count (2 ^ m + 1) : ℝ) - Real.logb 2 m)
      (fun _ : ℕ => (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (3 : ℝ)
  apply Filter.eventually_atTop.mpr
  refine ⟨4, fun m hm => ?_⟩
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using dyadic_count_real_log_bound m hm

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
