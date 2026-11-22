/- GID: D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityMixedRankBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Combine row and column parity mismatches on selected rank cuts. -/

import D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds

open Finset
open D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
open D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds

def lowEven {n : ℕ} (r : ℕ) : Finset (EvenSubset n) :=
  univ.filter fun p => p.val.card < r

def highOdd {n : ℕ} (r : ℕ) : Finset (OddSubset n) :=
  univ.filter fun q => n - r < q.val.card

abbrev RankCutTable (n : ℕ) :=
  EvenSubset n × (EvenSubset n → OddSubset n → ℕ) × (Finset ℕ × Finset ℕ)

private def mismatch {Y : Type*} [Fintype Y] (mass : Y → ℕ) (free : Finset Y) : Prop :=
  (∑ y, mass y) % 2 ≠ (∑ y ∈ free, mass y) % 2

private theorem mismatch_charge {Y : Type*} [Fintype Y] [DecidableEq Y]
    (mass : Y → ℕ) (free : Finset Y) (h : mismatch mass free) :
    1 ≤ ∑ y, if y ∈ free then 0 else mass y % 2 := by
  by_contra! failure
  have zero : (∑ y, if y ∈ free then 0 else mass y % 2) = 0 := by omega
  apply h
  have same (y : Y) :
      mass y ≡ (if y ∈ free then mass y else 0) [MOD 2] := by
    by_cases hy : y ∈ free
    · simp [hy, Nat.ModEq]
    · have le := single_le_sum (f := fun z => if z ∈ free then 0 else mass z % 2)
        (fun _ _ => Nat.zero_le _) (mem_univ y)
      rw [zero] at le
      simpa [hy, Nat.ModEq] using le
  have congruence := Nat.ModEq.sum (s := univ) (fun y _ => same y)
  change (∑ y, mass y) % 2 = (∑ y, if y ∈ free then mass y else 0) % 2 at congruence
  rw [← sum_filter] at congruence
  simpa only [filter_mem_eq_inter, univ_inter] using congruence

private def highRows {n : ℕ} (full : EvenSubset n) (r : ℕ) : Finset (EvenSubset n) :=
  (univ.erase full).filter fun p => r ≤ p.val.card

/-- Targets for which the free columns leave an odd balance. -/
def rowTargets {n : ℕ} (table : RankCutTable n) (r : ℕ) : Finset (EvenSubset n) :=
  if r ∈ table.2.2.1 then
    (highRows table.1 r).filter fun p =>
      (∑ q, table.2.1 p q) % 2 ≠ (∑ q ∈ lowOddRanks r, table.2.1 p q) % 2
  else ∅

/-- Targets for which the low rows and the distinguished row leave an odd balance. -/
def columnTargets {n : ℕ} (table : RankCutTable n) (r : ℕ) : Finset (OddSubset n) :=
  if r ∈ table.2.2.2 then
    (highOdd r).filter fun q =>
      (∑ p, table.2.1 p q) % 2 ≠
        (∑ p ∈ insert table.1 (lowEven r), table.2.1 p q) % 2
  else ∅

private theorem row_targets {n : ℕ} (table : RankCutTable n) (r : ℕ)
    {p : EvenSubset n} (hp : p ∈ rowTargets table r) :
    p ∈ highRows table.1 r ∧ mismatch (table.2.1 p) (lowOddRanks r) := by
  unfold rowTargets at hp
  split at hp
  · exact mem_filter.mp hp
  · exact (notMem_empty p hp).elim

private theorem column_targets {n : ℕ} (table : RankCutTable n) (r : ℕ)
    {q : OddSubset n} (hq : q ∈ columnTargets table r) :
    q ∈ highOdd r ∧ mismatch (fun p => table.2.1 p q) (insert table.1 (lowEven r)) := by
  unfold columnTargets at hq
  split at hq
  · exact mem_filter.mp hq
  · exact (notMem_empty q hq).elim

/-- Use the larger target family at a shared threshold, with ties assigned to rows. -/
def charges {n : ℕ} (table : RankCutTable n) (r : ℕ)
    (p : EvenSubset n) (q : OddSubset n) : Prop :=
  if (columnTargets table r).card ≤ (rowTargets table r).card then
    p ∈ rowTargets table r ∧ q ∉ lowOddRanks r
  else q ∈ columnTargets table r ∧ p ∉ insert table.1 (lowEven r)

instance {n : ℕ} (table : RankCutTable n) (r : ℕ) (p : EvenSubset n) (q : OddSubset n) :
    Decidable (charges table r p q) := by unfold charges; infer_instance

/-- Sum the larger selected target count at each threshold. -/
def cutDeficitSum {n : ℕ} (table : RankCutTable n) : ℕ :=
  ∑ r ∈ table.2.2.1 ∪ table.2.2.2,
    max (rowTargets table r).card (columnTargets table r).card

/-- Count the selected thresholds that can charge an ordinary cell. -/
def chargeCount {n : ℕ} (table : RankCutTable n) (p : EvenSubset n) (q : OddSubset n) : ℕ :=
  ((table.2.2.1 ∪ table.2.2.2).filter fun r => charges table r p q).card

private theorem sum_indicator {X : Type*} [Fintype X] [DecidableEq X]
    (s : Finset X) (f : X → ℕ) :
    (∑ x ∈ s, f x) = ∑ x, if x ∈ s then f x else 0 := by
  rw [← sum_filter]
  simp only [filter_mem_eq_inter, univ_inter]

private theorem row_count {n : ℕ} (table : RankCutTable n) (r : ℕ) :
    (rowTargets table r).card ≤ ∑ p : EvenSubset n, ∑ q : OddSubset n,
      if p ∈ rowTargets table r ∧ q ∉ lowOddRanks r then table.2.1 p q % 2 else 0 := by
  calc
    _ = ∑ _p ∈ rowTargets table r, (1 : ℕ) := card_eq_sum_ones _
    _ ≤ ∑ p ∈ rowTargets table r, ∑ q,
          if q ∈ lowOddRanks r then 0 else table.2.1 p q % 2 :=
      sum_le_sum fun p hp => mismatch_charge _ _ (row_targets table r hp).2
    _ = _ := by
      rw [sum_indicator]
      apply sum_congr rfl
      intro p _
      by_cases hp : p ∈ rowTargets table r
      · simp [hp, ite_not]
      · simp [hp]

private theorem column_count {n : ℕ} (table : RankCutTable n) (r : ℕ) :
    (columnTargets table r).card ≤ ∑ p : EvenSubset n, ∑ q : OddSubset n,
      if q ∈ columnTargets table r ∧ p ∉ insert table.1 (lowEven r) then
        table.2.1 p q % 2 else 0 := by
  rw [sum_comm]
  calc
    _ = ∑ _q ∈ columnTargets table r, (1 : ℕ) := card_eq_sum_ones _
    _ ≤ ∑ q ∈ columnTargets table r, ∑ p,
          if p ∈ insert table.1 (lowEven r) then 0 else table.2.1 p q % 2 :=
      sum_le_sum fun q hq => mismatch_charge _ _ (column_targets table r hq).2
    _ = _ := by
      rw [sum_indicator]
      apply sum_congr rfl
      intro q _
      by_cases hq : q ∈ columnTargets table r
      · simp only [hq, ite_true, true_and, ite_not]
      · simp only [hq, ite_false, false_and, sum_const_zero]

private theorem bound_at_threshold {n : ℕ} (table : RankCutTable n) (r : ℕ) :
    max (rowTargets table r).card (columnTargets table r).card ≤
      ∑ p : EvenSubset n, ∑ q : OddSubset n,
        if charges table r p q then table.2.1 p q % 2 else 0 := by
  by_cases h : (columnTargets table r).card ≤ (rowTargets table r).card
  · simpa only [max_eq_left h, charges, ite_eq_left h] using row_count table r
  · simpa only [max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h)), charges, ite_eq_right h] using
      column_count table r

private theorem charges_region {n : ℕ} (table : RankCutTable n) (r : ℕ)
    (p : EvenSubset n) (q : OddSubset n) (h : charges table r p q) :
    p ≠ table.1 ∧ r ∈ Ioc (n - q.val.card) p.val.card := by
  have size : q.val.card ≤ n := by simpa using card_le_univ q.val
  have inside (notFull : p ≠ table.1) (hi : r ≤ p.val.card) (lo : n - r < q.val.card) :
      p ≠ table.1 ∧ r ∈ Ioc (n - q.val.card) p.val.card :=
    ⟨notFull, mem_Ioc.mpr ⟨by omega, hi⟩⟩
  unfold charges at h
  split at h
  · have hp := (row_targets table r h.1).1
    have rank : p ≠ table.1 ∧ r ≤ p.val.card := by simpa [highRows] using hp
    have lo : n - r < q.val.card := by simpa [lowOddRanks, Nat.not_le] using h.2
    exact inside rank.1 rank.2 lo
  · have hq := (column_targets table r h.1).1
    have rank : p ≠ table.1 ∧ r ≤ p.val.card := by simpa [lowEven, Nat.not_lt] using h.2
    have lo : n - r < q.val.card := by simpa [highOdd] using hq
    exact inside rank.1 rank.2 lo

private theorem chargeCount_le_intersection {n : ℕ} (table : RankCutTable n)
    (p : EvenSubset n) (q : OddSubset n) :
    chargeCount table p q ≤ if p = table.1 then 0 else (p.val ∩ q.val).card := by
  by_cases hp : p = table.1
  · have empty : ((table.2.2.1 ∪ table.2.2.2).filter fun r => charges table r p q) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact (charges_region table r p q (mem_filter.mp hr).2).1 hp
    rw [ite_eq_left hp, chargeCount, empty, card_empty]
  · rw [ite_eq_right hp]
    have subset : ((table.2.2.1 ∪ table.2.2.2).filter fun r => charges table r p q) ⊆
        Ioc (n - q.val.card) p.val.card :=
      fun r hr => (charges_region table r p q (mem_filter.mp hr).2).2
    have bound := card_le_card subset
    rw [Nat.card_Ioc] at bound
    have union : (p.val ∪ q.val).card ≤ n := by simpa using card_le_univ (p.val ∪ q.val)
    have both := card_union_add_card_inter p.val q.val
    unfold chargeCount
    omega

/-- Each mismatch is paid by a charged odd cell, within the cell's intersection size. -/
theorem mixed_rank_lower (n : ℕ) (table : RankCutTable n) :
    (cutDeficitSum table ≤ ∑ p : EvenSubset n, ∑ q : OddSubset n,
      (table.2.1 p q % 2) * chargeCount table p q) ∧
    (∀ p q, chargeCount table p q ≤ if p = table.1 then 0 else (p.val ∩ q.val).card) := by
  refine ⟨?_, chargeCount_le_intersection table⟩
  refine (sum_le_sum fun r _ => bound_at_threshold table r).trans_eq ?_
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [chargeCount, ← sum_filter, sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]

end D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
