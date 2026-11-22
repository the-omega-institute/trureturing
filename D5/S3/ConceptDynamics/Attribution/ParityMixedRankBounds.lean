/- GID: D5/S3/ConceptDynamics/Attribution/ParityMixedRankBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityMixedRankBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Add compatible row and column rank cuts for odd uniform parity tables. -/

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

private theorem active_fits {n : ℕ} {p : EvenSubset n} {q : OddSubset n} {r : ℕ}
    (h : active p q r) : r ∈ Ioc (n-q.val.card) p.val.card := by
  have pcard : p.val.card ≤ n := by simpa using card_le_univ p.val
  have qcard : q.val.card ≤ n := by simpa using card_le_univ q.val
  obtain ⟨hp, hq⟩ := h
  exact mem_Ioc.mpr ⟨by omega, hp⟩

private theorem active_budget {n : ℕ} (p : EvenSubset n) (q : OddSubset n)
    (R C : Finset ℕ) (separate : Disjoint R C) :
    (∑ r ∈ R, (if active p q r then 1 else 0 : ℕ)) +
      (∑ r ∈ C, (if active p q r then 1 else 0 : ℕ)) ≤ (p.val ∩ q.val).card := by
  classical
  rw [← sum_union separate, ← sum_filter, ← card_eq_sum_ones]
  have fit : ((R ∪ C).filter (active p q)) ⊆ Ioc (n-q.val.card) p.val.card := by
    intro r hr
    exact active_fits (mem_filter.mp hr).2
  exact (card_le_card fit).trans (rank_interval_card_le_intersection p.val q.val)

private theorem flag_budget {n : ℕ} (q : OddSubset n) (R C : Finset ℕ)
    (separate : Disjoint R C) (upper : ∀ r ∈ R ∪ C, r ≤ n - 2) :
    1 + (∑ r ∈ R, (if q ∈ highOdd r then 1 else 0 : ℕ)) +
      (∑ r ∈ C, (if q ∈ highOdd r then 1 else 0 : ℕ)) ≤ q.val.card := by
  classical
  rw [add_assoc, ← sum_union separate, ← sum_filter, ← card_eq_sum_ones]
  have fit : ((R ∪ C).filter (fun r => q ∈ highOdd r)) ⊆ Ioc (n-q.val.card) (n-2) := by
    intro r hr
    obtain ⟨mem, hq⟩ := mem_filter.mp hr
    have hr := upper r mem
    have out : n-r < q.val.card := by simpa [highOdd] using hq
    have qcard : q.val.card ≤ n := by simpa using card_le_univ q.val
    exact mem_Ioc.mpr ⟨by omega, hr⟩
  have room := card_le_card fit
  rw [Nat.card_Ioc] at room
  have odd := q.property
  omega

private theorem row_cut {n k : ℕ}
    (full : EvenSubset n) (full_size : full.val.card = n)
    (mass : EvenSubset n → OddSubset n → ℕ)
    (rows : ∀ p, ∑ q, mass p q = k) (odd : k % 2 = 1) (r : ℕ) :
    (highOrdinaryEvenRanks (n := n) r).card -
      (∑ p ∈ highOrdinaryEvenRanks r, ∑ q ∈ lowOddRanks r, mass p q) ≤
    ∑ p : EvenSubset n, ∑ q : OddSubset n,
      if p = full then 0 else if active p q r then mass p q % 2 else 0 := by
  classical
  have cut := cut_count_le mass (highOrdinaryEvenRanks r) (lowOddRanks r)
    (fun p => by rw [rows]; exact odd)
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

private theorem col_cut {n k : ℕ}
    (full : EvenSubset n) (mass : EvenSubset n → OddSubset n → ℕ)
    (cols : ∀ q, ∑ p, mass p q = k) (odd : k % 2 = 1) (r : ℕ) :
    (highOdd (n := n) r).card -
      (∑ q ∈ highOdd r, ∑ p ∈ insert full (lowEven r), mass p q) ≤
    ∑ p : EvenSubset n, ∑ q : OddSubset n,
      if p = full then 0 else if active p q r then mass p q % 2 else 0 := by
  classical
  have cut := cut_count_le (Function.swap mass) (highOdd r) (insert full (lowEven r))
    (fun q => by change (∑ p, mass p q) % 2 = 1; rw [cols]; exact odd)
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



private theorem reserved_col_mass {n k : ℕ} (full : EvenSubset n)
    (mass : EvenSubset n → OddSubset n → ℕ)
    (rows : ∀ p, ∑ q, mass p q = k) (q : OddSubset n) (present : 1 ≤ mass full q)
    (r : ℕ) :
    (highOdd (n := n) r).card + 1 - k * ((lowEven (n := n) r).card + 1) ≤
      ((highOdd (n := n) r).card - ∑ c ∈ highOdd r, ∑ p ∈ insert full (lowEven r), mass p c) +
      (if q ∈ highOdd r then 1 else 0) := by
  classical
  let H := highOdd (n := n) r
  let L := lowEven (n := n) r
  have part (p : EvenSubset n) : (∑ c ∈ H, mass p c) ≤ k := by
    rw [← rows p]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
  have small : (∑ p ∈ L, ∑ c ∈ H, mass p c) ≤ k * L.card := by
    simpa [Nat.mul_comm] using sum_le_sum (s := L) (fun p _ => part p)
  have total : (∑ p ∈ insert full L, ∑ c ∈ H, mass p c) ≤
      (∑ c ∈ H, mass full c) + (∑ p ∈ L, ∑ c ∈ H, mass p c) := by
    by_cases h : full ∈ L
    · rw [insert_eq_of_mem h]; exact Nat.le_add_left _ _
    · rw [sum_insert h]
  rw [sum_comm]
  change H.card + 1 - k * (L.card + 1) ≤
    H.card - (∑ p ∈ insert full L, ∑ c ∈ H, mass p c) + (if q ∈ H then 1 else 0)
  rw [Nat.mul_succ]
  by_cases hq : q ∈ H
  · have hpart := part full
    simp [hq]
    omega
  · have outside : (∑ c ∈ H, mass full c) + mass full q ≤ k := by
      rw [Nat.add_comm, ← sum_insert hq, ← rows full]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
    simp [hq]
    omega

private def cellFlags {n : ℕ} (full p : EvenSubset n) (q : OddSubset n)
    (mass : EvenSubset n → OddSubset n → ℕ) (r : ℕ) : ℕ :=
  if p = full then 0 else if active p q r then mass p q % 2 else 0

/-- Add row and column deficits on disjoint threshold sets in one odd-margin table. -/
theorem mixed_rank_lower (n k : ℕ) (even : n % 2 = 0) (odd : k % 2 = 1)
    (cuts : Finset ℕ × Finset ℕ) (separate : Disjoint cuts.1 cuts.2)
    (upper : ∀ r ∈ cuts.1 ∪ cuts.2, r ≤ n - 2)
    (mass : EvenSubset n → OddSubset n → ℕ) (flags : OddSubset n → ℕ)
    (rows : ∀ p, ∑ q, mass p q = k) (cols : ∀ q, ∑ p, mass p q = k)
    (positive : ∃ q, 1 ≤ flags q ∧ flags q ≤ mass ⟨univ, by simpa using even⟩ q) :
    1 + (∑ r ∈ cuts.1, ((highOrdinaryEvenRanks (n := n) r).card + 1 - k * (lowOddRanks (n := n) r).card)) +
      (∑ r ∈ cuts.2, ((highOdd (n := n) r).card + 1 - k * ((lowEven (n := n) r).card + 1))) ≤
    ∑ p : EvenSubset n, ∑ q : OddSubset n,
      (if p = ⟨univ, by simpa using even⟩ then flags q else mass p q % 2) * (p.val ∩ q.val).card := by
  classical
  let R := cuts.1
  let C := cuts.2
  let full : EvenSubset n := ⟨univ, by simpa using even⟩
  have full_size : full.val.card = n := by simp [full]
  obtain ⟨q, flag, dom⟩ := positive
  have present : 1 ≤ mass full q := flag.trans dom
  have used : ∀ r ∈ R, (highOrdinaryEvenRanks (n := n) r).card + 1 - k * (lowOddRanks (n := n) r).card ≤
      (∑ p, ∑ c, cellFlags full p c mass r) + (if q ∈ highOdd r then 1 else 0) := by
    intro r _
    have h := reserved_low_mass mass full full_size cols q present (r := r)
    have eq : (if q ∈ lowOddRanks r then (0:ℕ) else 1) = if q ∈ highOdd r then 1 else 0 := by
      by_cases h : n - r < q.val.card
      · simp [lowOddRanks, highOdd, h, not_le.mpr h]
      · simp [lowOddRanks, highOdd, h, not_lt.mp h]
    rw [eq] at h
    exact h.trans (Nat.add_le_add_right (row_cut full full_size mass rows odd r) _)
  have usedCol : ∀ r ∈ C, (highOdd (n := n) r).card + 1 - k * ((lowEven (n := n) r).card + 1) ≤
      (∑ p, ∑ c, cellFlags full p c mass r) + (if q ∈ highOdd r then 1 else 0) := by
    intro r _
    exact (reserved_col_mass full mass rows q present r).trans
      (Nat.add_le_add_right (col_cut full mass cols odd r) _)
  have rowSum := sum_le_sum used
  have colSum := sum_le_sum usedCol
  rw [sum_add_distrib] at rowSum colSum
  have chosen := flag_budget q R C separate upper
  have spot : q.val.card ≤ (∑ c, flags c * c.val.card) := by
    have one := Nat.mul_le_mul_right q.val.card flag
    rw [Nat.one_mul] at one
    exact one.trans (single_le_sum (f := fun c => flags c * c.val.card)
      (fun _ _ => Nat.zero_le _) (mem_univ q))
  have base :
      1 + (∑ r ∈ R, ((highOrdinaryEvenRanks (n := n) r).card + 1 - k * (lowOddRanks (n := n) r).card)) +
        (∑ r ∈ C, ((highOdd (n := n) r).card + 1 - k * ((lowEven (n := n) r).card + 1))) ≤
      (∑ c, flags c * c.val.card) + (∑ r ∈ R, ∑ p, ∑ c, cellFlags full p c mass r) +
        (∑ r ∈ C, ∑ p, ∑ c, cellFlags full p c mass r) := by omega
  apply base.trans
  have regroup (S : Finset ℕ) :
      (∑ r ∈ S, ∑ p, ∑ c, cellFlags full p c mass r) =
      ∑ p, ∑ c, ∑ r ∈ S, cellFlags full p c mass r := by
    rw [sum_comm]
    exact sum_congr rfl (fun p _ => sum_comm)
  have fullSum : (∑ c, flags c * c.val.card) =
      ∑ p : EvenSubset n, ∑ c, if p = full then flags c * c.val.card else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro c _
    simp
  rw [regroup, regroup, fullSum]
  simp only [← sum_add_distrib]
  apply sum_le_sum
  intro p _
  apply sum_le_sum
  intro c _
  by_cases hp : p = full
  · subst p
    simp [cellFlags, full]
  · have atCut (S : Finset ℕ) :
        (∑ r ∈ S, cellFlags full p c mass r) =
        (mass p c % 2) * (∑ r ∈ S, (if active p c r then 1 else 0 : ℕ)) := by
      rw [mul_sum]
      exact sum_congr rfl (fun r _ => by by_cases h : active p c r <;> simp [cellFlags, hp, h])
    rw [ite_eq_right hp, ite_eq_right hp, zero_add, atCut, atCut, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (active_budget p c R C separate)
end
end D5.S3.ConceptDynamics.Attribution.ParityMixedRankBounds
