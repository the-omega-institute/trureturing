/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual weighted halving counts have paired impulses and admit no finite decimation family over any nonzero commutative ring at any power-of-two representation base. -/

import D5.S1.Recurrence.Partitions.HalvingPartitionWeights
import D5.S1.Recurrence.PowerBaseDecimation

/-! Forward monic recurrence obstruction, with arbitrary weights including zero. -/

namespace D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

variable {R : Type*} [CommRing R]

/-- The r-th dyadic tail contribution is present at its threshold, with the
first two exponents equal to zero. Natural subtraction is intentional. -/
def weightedTail (t : R) (m r : ℕ) : R :=
  if 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m then t ^ (m - r - 2 ^ r - 2) else 0

private theorem weighted_tail_sum (t : R) (m L : ℕ) (hL : m < L) :
    ∑ r : Threshold m, t ^ (m - r.val.val - 2 ^ r.val.val - 2) =
      ∑ r ∈ Finset.range L, weightedTail t m r := by
  classical
  unfold weightedTail
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun r _ => r.val.val)
  · intro r _
    have hr := r.prop
    have hp : 0 < (2 : ℕ) ^ r.val.val := by positivity
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hr⟩
  · intro r _ s _ h
    exact Subtype.ext (Fin.ext h)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    have hp : 0 < (2 : ℕ) ^ r := by positivity
    exact ⟨⟨⟨r, by omega⟩, hr.2⟩, Finset.mem_univ _, rfl⟩
  · intro r _
    rfl

/-- A common finite summation domain for any two consecutive dyadic values. -/
theorem weightedCount_bounded (t : R) (m L : ℕ) (hm : 2 ≤ m) (hL : m < L) :
    weightedCount t (2 ^ m + 1) =
      t ^ (m - 3) + t ^ (m - 2) + t ^ (m - 1) +
        ∑ r ∈ Finset.range L, weightedTail t m r := by
  rw [weightedCount_dyadic t m hm, weighted_tail_sum t m L hL]

private theorem weightedTail_difference (t : R) (m r : ℕ) :
    weightedTail t (m + 1) r - t * weightedTail t m r =
      if 1 ≤ r ∧ 2 ^ r + r = m then 1
      else if 1 ≤ r ∧ 2 ^ r + r + 1 = m then 1 - t else 0 := by
  by_cases hr : 1 ≤ r
  · by_cases h0 : 2 ^ r + r + 1 ≤ m
    · by_cases h2 : 2 ^ r + r + 2 ≤ m
      · have h1 : 2 ^ r + r + 1 ≤ m + 1 := by omega
        have he : m + 1 - r - 2 ^ r - 2 = (m - r - 2 ^ r - 2) + 1 := by omega
        simp only [weightedTail, hr, h0, h1, and_self, ↓reduceIte, he, pow_succ]
        simp only [show ¬(True ∧ 2 ^ r + r = m) from by omega,
          show ¬(True ∧ 2 ^ r + r + 1 = m) from by omega, ↓reduceIte]
        ring
      · have hm : m = 2 ^ r + r + 1 := by omega
        subst m
        simp [weightedTail, hr,
          show 2 ^ r + r + 1 + 1 - r - 2 ^ r - 2 = 0 by omega]
    · by_cases h1 : 2 ^ r + r + 1 ≤ m + 1
      · have hm : m = 2 ^ r + r := by omega
        subst m
        simp [weightedTail, hr]
      · simp [weightedTail, hr, h0, h1, show 2 ^ r + r ≠ m by omega,
          show 2 ^ r + r + 1 ≠ m by omega]
  · simp [weightedTail, hr]

/-- The exact weighted forward difference. Its two impulses are 1 and 1-t. -/
noncomputable def weightedDifference (t : R) (m : ℕ) : R :=
  weightedCount t (2 ^ (m + 1) + 1) - t * weightedCount t (2 ^ m + 1)

open Classical in
/-- All indices and both paired endpoints are retained in this finite sum. -/
theorem weightedDifference_impulses (t : R) (m : ℕ) (hm : 3 ≤ m) :
    weightedDifference t m =
      ∑ r ∈ Finset.range (m + 2),
        if 1 ≤ r ∧ 2 ^ r + r = m then 1
        else if 1 ≤ r ∧ 2 ^ r + r + 1 = m then 1 - t else 0 := by
  classical
  unfold weightedDifference
  rw [weightedCount_bounded t (m + 1) (m + 2) (by omega) (by omega),
    weightedCount_bounded t m (m + 2) (by omega) (by omega)]
  have hb : t ^ (m + 1 - 3) + t ^ (m + 1 - 2) + t ^ (m + 1 - 1) =
      t * (t ^ (m - 3) + t ^ (m - 2) + t ^ (m - 1)) := by
    rw [show m + 1 - 3 = (m - 3) + 1 by omega,
      show m + 1 - 2 = (m - 2) + 1 by omega,
      show m + 1 - 1 = (m - 1) + 1 by omega]
    simp only [pow_succ]
    ring
  rw [hb]
  calc
    _ = ∑ r ∈ Finset.range (m + 2),
        (weightedTail t (m + 1) r - t * weightedTail t m r) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    _ = _ := Finset.sum_congr rfl (fun r _ => weightedTail_difference t m r)

private theorem thresholds_separated {q r : ℕ} (h : q < r) :
    2 ^ q + q + 1 + 2 ≤ 2 ^ r + r + 1 := by
  have hp : (2 : ℕ) ^ q < 2 ^ r := pow_lt_pow_right₀ (by decide) h
  omega

/-- At every first impulse the value is exactly 1, for every ring parameter. -/
theorem weightedDifference_jump (t : R) (r : ℕ) (hr : 1 ≤ r) :
    weightedDifference t (2 ^ r + r) = 1 := by
  classical
  have hp : 2 ≤ (2 : ℕ) ^ r := by
    simpa using (pow_le_pow_right₀ (show 1 ≤ (2 : ℕ) by decide) hr)
  rw [weightedDifference_impulses t _ (by omega), Finset.sum_eq_single r]
  · simp [hr]
  · intro q hq hne
    rcases lt_or_gt_of_ne hne with hqr | hrq
    · have hs := thresholds_separated hqr
      simp only [show ¬(1 ≤ q ∧ 2 ^ q + q = 2 ^ r + r) from by omega,
        show ¬(1 ≤ q ∧ 2 ^ q + q + 1 = 2 ^ r + r) from by omega, ↓reduceIte]
    · have hs := thresholds_separated hrq
      simp only [show ¬(1 ≤ q ∧ 2 ^ q + q = 2 ^ r + r) from by omega,
        show ¬(1 ≤ q ∧ 2 ^ q + q + 1 = 2 ^ r + r) from by omega, ↓reduceIte]
  · intro h
    simp only [Finset.mem_range] at h
    omega

/-- The second impulse, including the case t=1 where it vanishes. -/
theorem weightedDifference_after_jump (t : R) (r : ℕ) (hr : 1 ≤ r) :
    weightedDifference t (2 ^ r + r + 1) = 1 - t := by
  classical
  have hp : 0 < (2 : ℕ) ^ r := by positivity
  rw [weightedDifference_impulses t _ (by omega), Finset.sum_eq_single r]
  · simp [hr]
  · intro q hq hne
    rcases lt_or_gt_of_ne hne with hqr | hrq
    · have hs := thresholds_separated hqr
      simp only [show ¬(1 ≤ q ∧ 2 ^ q + q = 2 ^ r + r + 1) from by omega,
        show ¬(1 ≤ q ∧ 2 ^ q + q + 1 = 2 ^ r + r + 1) from by omega, ↓reduceIte]
    · have hs := thresholds_separated hrq
      simp only [show ¬(1 ≤ q ∧ 2 ^ q + q = 2 ^ r + r + 1) from by omega,
        show ¬(1 ≤ q ∧ 2 ^ q + q + 1 = 2 ^ r + r + 1) from by omega, ↓reduceIte]
  · intro h
    simp only [Finset.mem_range] at h
    omega

/-- Precisely the open interval after a paired impulse and before the next
first impulse consists of zeros. Its length is 2^r-1. -/
theorem weightedDifference_gap (t : R) (m r : ℕ) (hr : 1 ≤ r)
    (hlo : 2 ^ r + r + 1 < m) (hhi : m < 2 ^ (r + 1) + (r + 1)) :
    weightedDifference t m = 0 := by
  classical
  have hp : 0 < (2 : ℕ) ^ r := by positivity
  rw [weightedDifference_impulses t m (by omega)]
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hqr : q ≤ r
  · have hs := threshold_mono hqr
    simp only [show ¬(1 ≤ q ∧ 2 ^ q + q = m) from by omega,
      show ¬(1 ≤ q ∧ 2 ^ q + q + 1 = m) from by omega, ↓reduceIte]
  · have hs := threshold_mono (r := r + 1) (s := q) (by omega)
    simp only [show ¬(1 ≤ q ∧ 2 ^ q + q = m) from by omega,
      show ¬(1 ≤ q ∧ 2 ^ q + q + 1 = m) from by omega, ↓reduceIte]

open Classical in
/-- The actual unweighted count has a single unit impulse at J_r=2^r+r.
The formula includes m=2 over every commutative ring. -/
theorem count_difference (m : ℕ) (hm : 2 ≤ m) :
    (count (2 ^ (m + 1) + 1) : R) - (count (2 ^ m + 1) : R) =
      if ∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r = m then 1 else 0 := by
  classical
  have hs : weightedDifference (1 : R) m =
      ∑ r ∈ Finset.range (m + 2),
        if 1 ≤ r ∧ 2 ^ r + r = m then (1 : R) else 0 := by
    unfold weightedDifference
    rw [weightedCount_bounded (1 : R) (m + 1) (m + 2) (by omega) (by omega),
      weightedCount_bounded (1 : R) m (m + 2) hm (by omega)]
    calc
      _ = ∑ r ∈ Finset.range (m + 2),
          (weightedTail (1 : R) (m + 1) r - 1 * weightedTail (1 : R) m r) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [one_pow, one_mul]
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        rw [weightedTail_difference]
        simp
  have he : (count (2 ^ (m + 1) + 1) : R) - (count (2 ^ m + 1) : R) =
      weightedDifference (1 : R) m := by
    simp only [weightedDifference, weightedCount_one, one_mul]
  rw [he, hs]
  split_ifs with h
  · obtain ⟨r, hr, hm⟩ := h
    rw [Finset.sum_eq_single r]
    · simp [hr, hm]
    · intro q _ hqr
      have hneq : ¬ (1 ≤ q ∧ 2 ^ q + q = m) := by
        intro hq
        rcases lt_or_gt_of_ne hqr with hlt | hgt
        · have := thresholds_separated hlt
          omega
        · have := thresholds_separated hgt
          omega
      simp only [if_neg hneq]
    · intro hnot
      simp only [Finset.mem_range] at hnot
      have hp : 0 < (2 : ℕ) ^ r := by positivity
      omega
  · apply Finset.sum_eq_zero
    intro r _
    exact if_neg (fun hr => h ⟨r, hr⟩)

/-- There are exactly 2^r intervening zero positions after J_r and before
J_(r+1); i=0 and i=2^r-1 are included. -/
theorem count_difference_zero_block (r i : ℕ) (hr : 1 ≤ r) (hi : i < 2 ^ r) :
    (count (2 ^ (2 ^ r + r + 1 + i + 1) + 1) : R) -
      (count (2 ^ (2 ^ r + r + 1 + i) + 1) : R) = 0 := by
  classical
  have hp : 0 < (2 : ℕ) ^ r := by positivity
  rw [count_difference _ (by omega)]
  apply if_neg
  rintro ⟨q, hq, he⟩
  by_cases hqr : q ≤ r
  · have hs := threshold_mono hqr
    omega
  · have hs := threshold_mono (r := r + 1) (s := q) (by omega)
    rw [pow_succ] at hs
    omega

/-- No weight over any nonzero commutative ring admits fixed binary matrices.
The recurrence is monic, and the proof never divides by t or by a coefficient. -/
theorem weighted_nonregularity [Nontrivial R] (t : R) :
    ¬ BinaryDecimation.MatrixFamily (weightedCount t) := by
  intro ha
  obtain ⟨E, hd, hE⟩ := BinaryDecimation.dyadic_matrix_recurrence (weightedCount t) ha
  let u (n : ℕ) := weightedCount t (2 ^ (n + 3) + 1)
  have hu : E.IsSolution u := by
    intro n
    simpa only [u, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hE (n + 1)
  have hc := BinaryDecimation.shifted_sub_solution E u hu t
  let r := E.order + 3
  let start := 2 ^ r + r - 1
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hp : E.order < 2 ^ r := by have := Nat.lt_two_pow_self (n := r); dsimp [r] at *; omega
  have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; omega
  have hzero (i : ℕ) (hi : i < E.order) :
      u (start + i + 1) - t * u (start + i) = 0 := by
    change weightedDifference t (start + i + 3) = 0
    exact weightedDifference_gap t _ r hr (by dsimp [start]; omega)
      (by dsimp [start]; omega)
  have hshift : E.IsSolution (fun n => u (start + n + 1) - t * u (start + n)) := by
    intro n
    simpa only [Nat.add_assoc] using hc (start + n)
  have hident : (fun n => u (start + n + 1) - t * u (start + n)) = fun _ => (0 : R) := by
    apply (E.eq_iff_eqOn_range_order _ _ hshift (by intro n; simp)).mpr
    intro i hi
    exact hzero i (Finset.mem_range.mp hi)
  let jump := 2 ^ (r + 1) + (r + 1) - 3
  have hj : start ≤ jump := by dsimp [start, jump]; omega
  have hz := congrFun hident (jump - start)
  rw [show start + (jump - start) = jump by omega] at hz
  change weightedDifference t (jump + 3) = 0 at hz
  have he : jump + 3 = 2 ^ (r + 1) + (r + 1) := by dsimp [jump]; omega
  rw [he, weightedDifference_jump t (r + 1) (by omega)] at hz
  exact one_ne_zero hz

/-- All representation bases 2^h, h>=1, for every weight and nonzero ring. -/
theorem weighted_powerBase_nonregularity [Nontrivial R] (t : R) (h : ℕ) (hh : 1 ≤ h) :
    ¬ BinaryDecimation.BaseFamily (2 ^ h) (weightedCount t) := by
  intro ha
  exact weighted_nonregularity t ((BinaryDecimation.arbitrary_matrix_iff _).mp
    (BinaryDecimation.powerBase_binary h hh _ ha))

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
