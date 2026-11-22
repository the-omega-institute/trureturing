/- GID: D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityMixedRankBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Combine exact row and column rank deficits for parity tables with odd margins. -/

import D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds

open Finset
open D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
open D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds

private theorem lift_sum {X : Type*} [Fintype X] [DecidableEq X]
    (s : Finset X) (f : X → ℕ) :
    (∑ x ∈ s, f x) = ∑ x, if x ∈ s then f x else 0 := by
  rw [← sum_filter]
  simp only [filter_mem_eq_inter, univ_inter]

private theorem cut_count_le {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (mass : X → Y → ℕ) (target : Finset X) (free : Finset Y)
    (odd : ∀ x, (∑ y, mass x y) % 2 = 1) :
    target.card - (∑ x ∈ target, ∑ y ∈ free, mass x y) ≤
      ∑ x ∈ target, ∑ y, if y ∈ free then 0 else mass x y % 2 := by
  classical
  have one (x : X) :
      1 ≤ (∑ y ∈ free, mass x y) + ∑ y, if y ∈ free then 0 else mass x y % 2 := by
    have h := parity_deficit (mass x) free (odd x)
    rw [lift_sum free (mass x), ← sum_add_distrib]
    exact h.trans_eq (sum_congr rfl (fun y _ => by split <;> simp_all))
  have summed := sum_le_sum (s := target) (fun x _ => one x)
  rw [sum_add_distrib] at summed
  have bound : target.card ≤
      (∑ x ∈ target, ∑ y ∈ free, mass x y) +
      (∑ x ∈ target, ∑ y, if y ∈ free then 0 else mass x y % 2) := by simpa using summed
  exact Nat.sub_le_iff_le_add.mpr (bound.trans_eq (Nat.add_comm _ _))

def lowEven {n : ℕ} (r : ℕ) : Finset (EvenSubset n) :=
  univ.filter fun p => p.val.card < r

def highOdd {n : ℕ} (r : ℕ) : Finset (OddSubset n) :=
  univ.filter fun q => n-r < q.val.card

private def active {n : ℕ} (p : EvenSubset n) (q : OddSubset n) (r : ℕ) : Prop :=
  r ≤ p.val.card ∧ n-r < q.val.card

noncomputable section
local instance {n : ℕ} (p : EvenSubset n) (q : OddSubset n) (r : ℕ) :
    Decidable (active p q r) := Classical.propDecidable _

private theorem active_iff_mem_interval {n : ℕ} (p : EvenSubset n) (q : OddSubset n)
    (r : ℕ) : active p q r ↔ r ∈ Ioc (n - q.val.card) p.val.card := by
  have pcard : p.val.card ≤ n := by simpa using card_le_univ p.val
  have qcard : q.val.card ≤ n := by simpa using card_le_univ q.val
  simp only [active, mem_Ioc]
  omega

private theorem row_cut {n : ℕ}
    (full : EvenSubset n) (full_size : full.val.card = n)
    (mass : EvenSubset n → OddSubset n → ℕ)
    (rows : ∀ p, (∑ q, mass p q) % 2 = 1) (r : ℕ) :
    (highOrdinaryEvenRanks (n := n) r).card -
      (∑ p ∈ highOrdinaryEvenRanks r, ∑ q ∈ lowOddRanks r, mass p q) ≤
    ∑ p : EvenSubset n, ∑ q : OddSubset n,
      if p = full then 0 else if active p q r then mass p q % 2 else 0 := by
  classical
  have cut := cut_count_le mass (highOrdinaryEvenRanks r) (lowOddRanks r) rows
  apply cut.trans
  apply le_of_eq
  rw [lift_sum (highOrdinaryEvenRanks r)]
  apply sum_congr rfl
  intro p _
  by_cases hp : p = full
  · simp [hp, highOrdinaryEvenRanks, full_size]
  · have proper : p.val.card ≠ n := by
      intro h
      apply hp
      apply Subtype.ext
      apply eq_of_subset_of_card_le
      · have hfull : full.val = univ :=
          eq_of_subset_of_card_le (subset_univ _) (by simp [full_size])
        rw [hfull]
        exact subset_univ _
      · rw [h, full_size]
    by_cases h : r ≤ p.val.card
    · simp [hp, proper, h, highOrdinaryEvenRanks, lowOddRanks, active]
      apply sum_congr rfl
      intro q _
      by_cases hq : n - r < q.val.card
      · simp [hq, not_le.mpr hq]
      · simp [hq, not_lt.mp hq]
    · simp [hp, h, highOrdinaryEvenRanks, active]

private theorem col_cut {n : ℕ}
    (full : EvenSubset n) (mass : EvenSubset n → OddSubset n → ℕ)
    (cols : ∀ q, (∑ p, mass p q) % 2 = 1) (r : ℕ) :
    (highOdd (n := n) r).card -
      (∑ q ∈ highOdd r, ∑ p ∈ insert full (lowEven r), mass p q) ≤
    ∑ p : EvenSubset n, ∑ q : OddSubset n,
      if p = full then 0 else if active p q r then mass p q % 2 else 0 := by
  classical
  have cut := cut_count_le (Function.swap mass) (highOdd r) (insert full (lowEven r)) cols
  apply cut.trans
  apply le_of_eq
  rw [lift_sum (highOdd r)]
  have rearrange :
      (∑ q : OddSubset n, if q ∈ highOdd r then
          (∑ p : EvenSubset n, if p ∈ insert full (lowEven r) then 0 else mass p q % 2)
          else 0) =
        ∑ p : EvenSubset n, ∑ q : OddSubset n, if q ∈ highOdd r then
          (if p ∈ insert full (lowEven r) then 0 else mass p q % 2) else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    by_cases hq : q ∈ highOdd r <;> simp [hq]
  change (∑ q : OddSubset n, if q ∈ highOdd r then
          (∑ p : EvenSubset n, if p ∈ insert full (lowEven r) then 0 else mass p q % 2)
          else 0) = _
  rw [rearrange]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  by_cases hp : p = full
  · simp [hp]
  · by_cases hq : n-r < q.val.card
    · by_cases h : r ≤ p.val.card
      · simp [hp, hq, h, not_lt.mpr h, lowEven, highOdd, active]
      · simp [hp, hq, h, not_le.mp h, lowEven, highOdd, active]
    · simp [hp, hq, highOdd, active]


/-- The high ordinary rows that cannot all receive a unit from the low columns. -/
def rowDeficit {n : ℕ} (mass : EvenSubset n → OddSubset n → ℕ) (r : ℕ) : ℕ :=
  (highOrdinaryEvenRanks (n := n) r).card -
    ∑ p ∈ highOrdinaryEvenRanks r, ∑ q ∈ lowOddRanks r, mass p q

/-- The high columns that cannot all receive a unit from low rows and the full row. -/
def columnDeficit {n : ℕ} (full : EvenSubset n)
    (mass : EvenSubset n → OddSubset n → ℕ) (r : ℕ) : ℕ :=
  (highOdd (n := n) r).card -
    ∑ q ∈ highOdd r, ∑ p ∈ insert full (lowEven r), mass p q

/-- The larger of the selected row and column deficits at a threshold. -/
def mixedDeficit {n : ℕ} (full : EvenSubset n)
    (mass : EvenSubset n → OddSubset n → ℕ) (cuts : Finset ℕ × Finset ℕ) (r : ℕ) : ℕ :=
  let row := if r ∈ cuts.1 then rowDeficit mass r else 0
  let col := if r ∈ cuts.2 then columnDeficit full mass r else 0
  row + (col - row)

private theorem sum_weighted_cuts {n : ℕ}
    (full : EvenSubset n) (mass : EvenSubset n → OddSubset n → ℕ)
    (thresholds : Finset ℕ) (deficit : ℕ → ℕ)
    (cut : ∀ r ∈ thresholds, deficit r ≤ ∑ p : EvenSubset n, ∑ q : OddSubset n,
      if p = full then 0 else if active p q r then mass p q % 2 else 0) :
    (∑ r ∈ thresholds, deficit r) ≤
      ∑ p : EvenSubset n, ∑ q : OddSubset n,
        if p = full then 0 else (mass p q % 2) *
          (∑ r ∈ thresholds ∩ Ioc (n - q.val.card) p.val.card,
            (deficit r - (deficit r - 1))) := by
  classical
  have atCut (r : ℕ) (hr : r ∈ thresholds) :
      deficit r ≤ ∑ p : EvenSubset n, ∑ q : OddSubset n,
        (if p = full then 0 else if active p q r then mass p q % 2 else 0) *
          (deficit r - (deficit r - 1)) := by
    by_cases h : deficit r = 0
    · rw [h]
      exact Nat.zero_le _
    · have cap : deficit r - (deficit r - 1) = 1 := by omega
      simpa only [cap, mul_one] using cut r hr
  apply (sum_le_sum atCut).trans
  apply le_of_eq
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  by_cases hp : p = full
  · simp [hp]
  · simp only [hp, ite_false]
    rw [mul_sum]
    simp_rw [ite_mul, zero_mul]
    rw [← sum_filter]
    congr 1
    ext r
    simp [active_iff_mem_interval, mem_inter, and_comm]

abbrev RankCutTable (n : ℕ) :=
  EvenSubset n × (EvenSubset n → OddSubset n → ℕ) × (Finset ℕ × Finset ℕ)

/-- Sum the larger selected deficit at each threshold. -/
def cutDeficitSum {n : ℕ} (table : RankCutTable n) : ℕ :=
  ∑ r ∈ table.2.2.1 ∪ table.2.2.2, mixedDeficit table.1 table.2.1 table.2.2 r

/-- The exact mixed deficits charge only positions of the same parity table. -/
theorem mixed_rank_lower (n : ℕ) (table : RankCutTable n) (hfull : table.1.val.card = n)
    (rows : ∀ p, (∑ q, table.2.1 p q) % 2 = 1)
    (cols : ∀ q, (∑ p, table.2.1 p q) % 2 = 1) :
    cutDeficitSum table ≤
    ∑ p : EvenSubset n, ∑ q : OddSubset n,
      if p = table.1 then 0
      else (table.2.1 p q % 2) *
        (∑ r ∈ (table.2.2.1 ∪ table.2.2.2) ∩ Ioc (n - q.val.card) p.val.card,
          let d := mixedDeficit table.1 table.2.1 table.2.2 r
          d - (d - 1)) := by
  classical
  obtain ⟨full, mass, cuts⟩ := table
  refine sum_weighted_cuts full mass _ (mixedDeficit full mass cuts) ?_
  intro r _
  let ordinary : ℕ := ∑ p : EvenSubset n, ∑ q : OddSubset n,
    if p = full then 0 else if active p q r then mass p q % 2 else 0
  have hrow : (if r ∈ cuts.1 then rowDeficit mass r else 0) ≤ ordinary := by
    split
    · exact row_cut full hfull mass rows r
    · exact Nat.zero_le _
  have hcol : (if r ∈ cuts.2 then columnDeficit full mass r else 0) ≤ ordinary := by
    split
    · exact col_cut full mass cols r
    · exact Nat.zero_le _
  change mixedDeficit full mass cuts r ≤ ordinary
  change (if r ∈ cuts.1 then rowDeficit mass r else 0) +
    ((if r ∈ cuts.2 then columnDeficit full mass r else 0) -
      (if r ∈ cuts.1 then rowDeficit mass r else 0)) ≤ ordinary
  omega
end
end D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
