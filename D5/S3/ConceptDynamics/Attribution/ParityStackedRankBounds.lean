/- GID: D5/S3/ConceptDynamics/Attribution/ParityStackedRankBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityStackedRankBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Add compatible high-rank cuts for odd uniform parity tables. -/

import D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds

open Finset ParityOddRankBounds

private theorem stacked_cuts
    {P Q R : Type*} [Fintype P] [Fintype Q] [Fintype R] [DecidableEq P] [DecidableEq Q]
    (mass weight : P → Q → ℕ) (specialFlags : Q → ℕ)
    (zeroRow special : P) (different : zeroRow ≠ special)
    (top : Finset Q) (low : R → Finset Q) (high : R → Finset P) (k : ℕ)
    (odd : k % 2 = 1)
    (rows : ∀ p, ∑ q, mass p q = k) (cols : ∀ q, ∑ p, mass p q = k)
    (ordinaryHigh : ∀ r, special ∉ high r)
    (budget : ∀ p q, p ≠ special →
      (if q ∈ top ∧ p ≠ zeroRow then 1 else 0) +
        (∑ r, if p ∈ high r ∧ q ∉ low r then 1 else 0) ≤ weight p q) :
    (∑ q, specialFlags q * weight special q) +
      (top.card - (∑ q ∈ top, (mass zeroRow q + mass special q))) +
      (∑ r, ((high r).card - (∑ p ∈ high r, ∑ q ∈ low r, mass p q))) ≤
      ∑ p, ∑ q, (if p = special then specialFlags q else mass p q % 2) * weight p q := by
  let oddPart (p : P) (q : Q) : ℕ := if p = special then 0 else mass p q % 2
  let rowGate (r : R) (p : P) (q : Q) : ℕ := if p ∈ high r ∧ q ∉ low r then 1 else 0
  let columnGate (p : P) (q : Q) : ℕ := if q ∈ top ∧ p ≠ zeroRow then 1 else 0
  have col :
      (top.card - ∑ q ∈ top, (mass zeroRow q + mass special q)) ≤
        ∑ p, ∑ q, oddPart p q * columnGate p q := by
    simpa [oddPart, columnGate] using
      (rank_cuts mass columnGate (fun _ => 0) zeroRow special different top ∅ ∅ k odd rows cols
        (by simp) (by intros; simp [columnGate]))
  have row (r : R) :
      ((high r).card - ∑ p ∈ high r, ∑ q ∈ low r, mass p q) ≤
        ∑ p, ∑ q, oddPart p q * rowGate r p q := by
    simpa [oddPart, rowGate] using
      (rank_cuts mass (rowGate r) (fun _ => 0) zeroRow special different ∅ (low r) (high r) k odd
        rows cols (fun p hp eq => ordinaryHigh r (eq ▸ hp)) (by intros; simp [rowGate]))
  have specialSum :
      (∑ q, specialFlags q * weight special q) =
        ∑ p, ∑ q, if p = special then specialFlags q * weight p q else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    simp
  calc
    _ ≤ (∑ q, specialFlags q * weight special q) +
        (∑ p, ∑ q, oddPart p q * columnGate p q) +
        (∑ r, ∑ p, ∑ q, oddPart p q * rowGate r p q) :=
      Nat.add_le_add (Nat.add_le_add_left col _) (sum_le_sum (fun r _ => row r))
    _ = ∑ p, ∑ q, ((if p = special then specialFlags q * weight p q else 0) +
        oddPart p q * (columnGate p q + ∑ r, rowGate r p q)) := by
      have swap : (∑ r, ∑ p, ∑ q, oddPart p q * rowGate r p q) =
          ∑ p, ∑ q, ∑ r, oddPart p q * rowGate r p q := by
        rw [sum_comm]
        apply sum_congr rfl
        intro p _
        rw [sum_comm]
      rw [specialSum, swap, Nat.add_assoc]
      simp only [Nat.mul_add, mul_sum, sum_add_distrib]
    _ ≤ _ := by
      apply sum_le_sum
      intro p _
      apply sum_le_sum
      intro q _
      by_cases h : p = special
      · simp [h, oddPart]
      · simpa [h, oddPart, columnGate, rowGate] using Nat.mul_le_mul_left (mass p q % 2) (budget p q h)

private theorem stack_intersection_budget {n : ℕ} (p q : Finset (Fin n))
    (even : p.card % 2 = 0) (thresholds : Finset ℕ)
    (lower : ∀ r ∈ thresholds, 4 ≤ r) :
    (if q.card = n-1 ∧ p ≠ ∅ then 1 else 0) +
      (∑ r ∈ thresholds, if r ≤ p.card ∧ n-r < q.card then 1 else 0) ≤
      (p ∩ q).card := by
  let used : Finset ℕ := thresholds.filter (fun r => r ≤ p.card ∧ n-r < q.card)
  let budget : Finset ℕ := Ioc (n-q.card) p.card
  have sum_used : (∑ r ∈ thresholds, if r ≤ p.card ∧ n-r < q.card then 1 else 0) =
      used.card := by
    rw [← sum_filter]
    exact (card_eq_sum_ones used).symm
  have fit : used ⊆ budget := by
    intro r hr
    obtain ⟨_, up, low⟩ := mem_filter.mp hr
    have rlimit : r ≤ n := up.trans (by simpa using (card_le_univ p))
    have qlimit : q.card ≤ n := by simpa using (card_le_univ q)
    apply mem_Ioc.mpr
    refine ⟨?_, up⟩
    omega
  have room : budget.card ≤ (p ∩ q).card := by
    have h := card_union_add_card_inter p q
    have union : (p ∪ q).card ≤ n := by simpa using (card_le_univ (p ∪ q))
    rw [Nat.card_Ioc]
    omega
  rw [sum_used]
  split
  next top =>
    have twoNotUsed : 2 ∉ used := by
      intro h
      have tooHigh := lower 2 (mem_filter.mp h).1
      omega
    have twoFits : 2 ∈ budget := by
      have pos : 0 < p.card := card_pos.mpr (nonempty_iff_ne_empty.mpr top.2)
      have qpos : 0 < q.card := by
        have pn : p.card ≤ n := by simpa using (card_le_univ p)
        omega
      apply mem_Ioc.mpr
      omega
    have bound : (insert 2 used).card ≤ budget.card :=
      card_le_card (insert_subset_iff.mpr ⟨twoFits, fit⟩)
    rw [card_insert_of_notMem twoNotUsed] at bound
    omega
  next =>
    simpa using (card_le_card fit).trans room


def topOddRank {n : ℕ} : Finset (OddSubset n) :=
  univ.filter (fun q => q.val.card = n - 1)

def lowOddRanks {n : ℕ} (r : ℕ) : Finset (OddSubset n) :=
  univ.filter (fun q => q.val.card ≤ n - r)

def highOrdinaryEvenRanks {n : ℕ} (r : ℕ) : Finset (EvenSubset n) :=
  univ.filter (fun p => p.val.card ≠ n ∧ r ≤ p.val.card)

private theorem stacked_rank_deficits (n : ℕ) (large : 6 ≤ n) (even : n % 2 = 0)
    (thresholds : Finset ℕ) (lower : ∀ r ∈ thresholds, 4 ≤ r) (k : ℕ) (odd : k % 2 = 1)
    (mass : EvenSubset n → OddSubset n → ℕ) (flags : OddSubset n → ℕ)
    (rows : ∀ p, ∑ q, mass p q = k) (cols : ∀ q, ∑ p, mass p q = k) :
    let zeroRow : EvenSubset n := ⟨∅, by simp⟩
    let special : EvenSubset n := ⟨univ, by simpa using even⟩
    (∑ q, flags q * q.val.card)
      + ((topOddRank (n := n)).card - (∑ q ∈ topOddRank, (mass zeroRow q + mass special q)))
      + (∑ r ∈ thresholds, ((highOrdinaryEvenRanks (n := n) r).card
        - ∑ p ∈ highOrdinaryEvenRanks r, ∑ q ∈ lowOddRanks r, mass p q)) ≤
    ∑ p : EvenSubset n, ∑ q : OddSubset n,
      (if p = special then flags q else mass p q % 2) * (p.val ∩ q.val).card := by
  classical
  dsimp only
  let zeroRow : EvenSubset n := ⟨∅, by simp⟩
  let special : EvenSubset n := ⟨univ, by simpa using even⟩
  have different : zeroRow ≠ special := by
    intro eq
    have h := congrArg (fun p : EvenSubset n => p.val.card) eq
    simp [zeroRow, special] at h
    omega
  have ordinaryHigh (r : thresholds) : special ∉ highOrdinaryEvenRanks r.val := by
    simp [highOrdinaryEvenRanks, special]
  have charge (p : EvenSubset n) (q : OddSubset n) (hp : p ≠ special) :
      (if q ∈ topOddRank ∧ p ≠ zeroRow then 1 else 0) +
        (∑ r : thresholds, if p ∈ highOrdinaryEvenRanks r.val ∧ q ∉ lowOddRanks r.val then 1 else 0)
        ≤ (p.val ∩ q.val).card := by
    have psize : p.val.card ≠ n := by
      intro full
      apply hp
      apply Subtype.ext
      apply eq_of_subset_of_card_le (subset_univ _)
      simp [special, full]
    have pzero : p ≠ zeroRow ↔ p.val ≠ ∅ :=
      not_congr ⟨congrArg Subtype.val, fun eq => Subtype.ext eq⟩
    let hit (r : ℕ) : ℕ := if r ≤ p.val.card ∧ n-r < q.val.card then 1 else 0
    have conversion :
        (∑ r : thresholds, if p ∈ highOrdinaryEvenRanks r.val ∧ q ∉ lowOddRanks r.val then 1 else 0) =
          ∑ r ∈ thresholds, hit r := by
      calc
        _ = ∑ r : thresholds, hit r.val := by
          apply sum_congr rfl
          intro r _
          simp [hit, highOrdinaryEvenRanks, lowOddRanks, psize]
        _ = _ := sum_coe_sort thresholds hit
    rw [conversion]
    simpa only [topOddRank, mem_filter, mem_univ, true_and, pzero, hit] using
      stack_intersection_budget p.val q.val p.property thresholds lower
  have h := stacked_cuts mass (fun p q => (p.val ∩ q.val).card) flags zeroRow special different
    topOddRank (fun r : thresholds => lowOddRanks r.val) (fun r => highOrdinaryEvenRanks r.val)
    k odd rows cols ordinaryHigh charge
  let deficit (r : ℕ) : ℕ := (highOrdinaryEvenRanks (n := n) r).card -
    ∑ p ∈ highOrdinaryEvenRanks r, ∑ q ∈ lowOddRanks r, mass p q
  have thresholdSum : (∑ r : thresholds, deficit r.val) = ∑ r ∈ thresholds, deficit r :=
    sum_coe_sort thresholds deficit
  have core :
      (∑ q, flags q * (special.val ∩ q.val).card) +
        (topOddRank.card - ∑ q ∈ topOddRank, (mass zeroRow q + mass special q)) +
        (∑ r : thresholds, deficit r.val) ≤
      ∑ p : EvenSubset n, ∑ q : OddSubset n,
        (if p = special then flags q else mass p q % 2) * (p.val ∩ q.val).card := h
  rw [thresholdSum] at core
  simpa only [special, zeroRow, univ_inter, deficit] using core

private theorem reserved_top_mass {n k : ℕ}
    (mass : EvenSubset n → OddSubset n → ℕ)
    (zeroRow special : EvenSubset n) (row : ∀ p, ∑ q, mass p q = k)
    (q : OddSubset n) (hasMass : 1 ≤ mass special q) :
    (topOddRank (n := n)).card + 1 - 2 * k ≤
      (topOddRank (n := n)).card - (∑ c ∈ topOddRank, (mass zeroRow c + mass special c)) +
      (if q ∈ topOddRank then 1 else 0) := by
  classical
  have charged := top_charged_mass mass zeroRow special
    (topOddRank (n := n)) k row
  by_cases h : q ∈ topOddRank
  · simp [h]
    omega
  · have unit := single_le_sum (f := mass special) (fun _ _ => Nat.zero_le _)
      (mem_sdiff.mpr ⟨mem_univ q, h⟩)
    simp [h]
    omega

private theorem reserved_low_mass {n k r : ℕ}
    (mass : EvenSubset n → OddSubset n → ℕ)
    (special : EvenSubset n) (full : special.val.card = n)
    (col : ∀ q, ∑ p, mass p q = k)
    (q : OddSubset n) (hasMass : 1 ≤ mass special q) :
    (highOrdinaryEvenRanks (n := n) r).card + 1 - k * (lowOddRanks (n := n) r).card ≤
      ((highOrdinaryEvenRanks (n := n) r).card - ∑ p ∈ highOrdinaryEvenRanks r, ∑ c ∈ lowOddRanks r, mass p c) +
      (if q ∈ lowOddRanks r then 0 else 1) := by
  classical
  have notHigh : special ∉ highOrdinaryEvenRanks r := by simp [highOrdinaryEvenRanks, full]
  have exactSum := high_charged_mass mass special (highOrdinaryEvenRanks r) (lowOddRanks r)
    k notHigh col
  rw [Nat.mul_comm] at exactSum
  by_cases h : q ∈ lowOddRanks r
  · have unit := single_le_sum (f := mass special) (fun _ _ => Nat.zero_le _) h
    simp [h]; omega
  · simp [h]; omega

private theorem maximum_lost_thresholds (n : ℕ) (large : 6 ≤ n)
    (q : OddSubset n) (thresholds : Finset ℕ)
    (bounded : ∀ r ∈ thresholds, r ≤ n - 2) :
    (if q ∈ topOddRank then 1 else 0) +
      (∑ r ∈ thresholds, if q ∈ lowOddRanks r then 0 else 1) + 1 ≤ q.val.card := by
  let missed := thresholds.filter (fun r => q ∉ lowOddRanks r)
  have missedSum :
      (∑ r ∈ thresholds, if q ∈ lowOddRanks r then 0 else 1) = missed.card := by
    calc
      _ = ∑ r ∈ thresholds, if q ∉ lowOddRanks r then 1 else 0 := by
        apply sum_congr rfl
        intro r _
        split <;> simp_all
      _ = _ := by rw [← sum_filter]; exact (card_eq_sum_ones missed).symm
  have fit : missed ⊆ Ioc (n-q.val.card) (n-2) := by
    intro r hr
    have upper := bounded r (mem_filter.mp hr).1
    have away : n - r < q.val.card := by
      exact Nat.lt_of_not_ge (fun le => (mem_filter.mp hr).2 (by simp [lowOddRanks, le]))
    have fit : r ≤ n := upper.trans (Nat.sub_le _ _)
    have qlimit : q.val.card ≤ n := by simpa using (card_le_univ q.val)
    have eq : n - r + r = n := Nat.sub_add_cancel fit
    exact mem_Ioc.mpr ⟨by omega, upper⟩
  have bound := card_le_card fit
  rw [Nat.card_Ioc] at bound
  have width : q.val.card ≤ n := by simpa using (card_le_univ q.val)
  have cardOdd := q.property
  rw [missedSum]
  by_cases top : q ∈ topOddRank
  · have h : q.val.card = n - 1 := by simpa [topOddRank] using top
    simp [top]; omega
  · simp [top]; omega

/-- Charge any collection of high even ranks against one common odd-margin table.
A positive full-row flag reserves one unit and pays for the rank cuts that do
not see its column. -/
theorem stacked_fixed_from_odd_margins (n k : ℕ) (large : 6 ≤ n) (even : n % 2 = 0)
    (odd : k % 2 = 1) (thresholds : Finset ℕ)
    (lower : ∀ r ∈ thresholds, 4 ≤ r) (upper : ∀ r ∈ thresholds, r ≤ n - 2)
    (mass : EvenSubset n → OddSubset n → ℕ) (flags : OddSubset n → ℕ)
    (rows : ∀ p, ∑ q, mass p q = k) (cols : ∀ q, ∑ p, mass p q = k)
    (positive : ∃ q, 1 ≤ flags q ∧ flags q ≤ mass ⟨univ, by simpa using even⟩ q) :
    1 + ((topOddRank (n := n)).card + 1 - 2 * k) +
      (∑ r ∈ thresholds, ((highOrdinaryEvenRanks (n := n) r).card + 1 - k * (lowOddRanks (n := n) r).card)) ≤
    ∑ p : EvenSubset n, ∑ q : OddSubset n,
      (if p = ⟨univ, by simpa using even⟩ then flags q else mass p q % 2) * (p.val ∩ q.val).card := by
  let zeroRow : EvenSubset n := ⟨∅, by simp⟩
  let special : EvenSubset n := ⟨univ, by simpa using even⟩
  obtain ⟨q, flag, dom⟩ := positive
  have massAt : 1 ≤ mass special q := flag.trans dom
  have specialScore : q.val.card ≤ ∑ c, flags c * c.val.card := by
    have one := Nat.mul_le_mul_right q.val.card flag
    rw [Nat.one_mul] at one
    exact one.trans (single_le_sum (f := fun c => flags c * c.val.card) (fun _ _ => Nat.zero_le _) (mem_univ q))
  have first := reserved_top_mass mass zeroRow special rows q massAt
  have each : ∀ r ∈ thresholds,
      (highOrdinaryEvenRanks (n := n) r).card + 1 - k * (lowOddRanks (n := n) r).card ≤
      ((highOrdinaryEvenRanks (n := n) r).card - ∑ p ∈ highOrdinaryEvenRanks r, ∑ c ∈ lowOddRanks r, mass p c) +
      (if q ∈ lowOddRanks r then 0 else 1) :=
    fun _ _ => reserved_low_mass mass special (by simp [special]) cols q massAt
  have total := sum_le_sum each
  rw [sum_add_distrib] at total
  have losses := maximum_lost_thresholds n large q thresholds upper
  have exactCuts := stacked_rank_deficits n large even thresholds lower k odd mass flags rows cols
  change (∑ q, flags q * q.val.card) + ((topOddRank (n := n)).card -
    ∑ q ∈ topOddRank, (mass zeroRow q + mass special q)) +
    (∑ r ∈ thresholds, ((highOrdinaryEvenRanks (n := n) r).card -
      ∑ p ∈ highOrdinaryEvenRanks r, ∑ q ∈ lowOddRanks r, mass p q)) ≤ _ at exactCuts
  omega

end D5.S3.ConceptDynamics.Attribution.ParityStackedRankBounds
