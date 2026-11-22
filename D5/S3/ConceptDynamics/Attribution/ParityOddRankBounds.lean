/- GID: D5/S3/ConceptDynamics/Attribution/ParityOddRankBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ParityOddRankBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: High rows and columns impose a joint lower bound under odd parity marginals. -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Rank constraints on odd uniform parity margins. -/

set_option autoImplicit false

open Finset

namespace D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds

private theorem parity_deficit {A : Type*} [Fintype A] [DecidableEq A]
    (mass : A → ℕ) (unrestricted : Finset A)
    (odd : (∑ a, mass a) % 2 = 1) :
    1 ≤ ∑ a, if a ∈ unrestricted then mass a else mass a % 2 := by
  by_contra! failure
  have zero : (∑ a, if a ∈ unrestricted then mass a else mass a % 2) = 0 :=
    by omega
  have pointwise (a : A) : mass a % 2 = 0 := by
    have bound := single_le_sum (f := fun b => if b ∈ unrestricted then mass b else mass b % 2)
      (fun _ _ => Nat.zero_le _) (mem_univ a)
    rw [zero] at bound
    by_cases h : a ∈ unrestricted
    · simp [h] at bound
      simp [bound]
    · simpa [h] using bound
  have zeroMod : (∑ a, mass a) % 2 = 0 := by
    have congruence : (∑ a, mass a) ≡ (∑ _a : A, (0 : ℕ)) [MOD 2] :=
      Nat.ModEq.sum fun a _ => by simpa [Nat.ModEq] using pointwise a
    simpa [Nat.ModEq] using congruence
  omega

private theorem rank_cuts
    {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (mass weight : P → Q → ℕ) (specialFlags : Q → ℕ)
    (zeroRow special : P) (different : zeroRow ≠ special)
    (top low : Finset Q) (high : Finset P) (k : ℕ)
    (odd : k % 2 = 1)
    (rows : ∀ p, ∑ q, mass p q = k) (cols : ∀ q, ∑ p, mass p q = k)
    (ordinaryHigh : ∀ p ∈ high, p ≠ special)
    (budget : ∀ p q, p ≠ special →
      (if q ∈ top ∧ p ≠ zeroRow then 1 else 0) +
        (if p ∈ high ∧ q ∉ low then 1 else 0) ≤ weight p q) :
    (∑ q, specialFlags q * weight special q) +
      (top.card - (∑ q ∈ top, (mass zeroRow q + mass special q))) +
      (high.card - (∑ p ∈ high, ∑ q ∈ low, mass p q)) ≤
      ∑ p, ∑ q, (if p = special then specialFlags q else mass p q % 2) * weight p q := by
  let columnCharge (p : P) (q : Q) : ℕ :=
    if q ∈ top ∧ p ≠ zeroRow ∧ p ≠ special then mass p q % 2 else 0
  let rowCharge (p : P) (q : Q) : ℕ :=
    if p ∈ high ∧ q ∉ low then mass p q % 2 else 0
  have columnOne (q : Q) (hq : q ∈ top) :
      1 ≤ (mass zeroRow q + mass special q) + ∑ p, columnCharge p q := by
    have lower := parity_deficit (fun p => mass p q) {zeroRow, special} (by rw [cols]; exact odd)
    calc
      1 ≤ ∑ p, if p ∈ ({zeroRow, special} : Finset P) then mass p q else mass p q % 2 := lower
      _ = ∑ p, ((if p = zeroRow then mass p q else 0) +
          (if p = special then mass p q else 0) + columnCharge p q) := by
        apply sum_congr rfl
        intro p _
        by_cases h₀ : p = zeroRow
        · subst p
          simp [columnCharge, different]
        · by_cases h₁ : p = special <;> simp [columnCharge, h₀, h₁, hq, different.symm]
      _ = _ := by simp [sum_add_distrib]
  have rowOne (p : P) (hp : p ∈ high) :
      1 ≤ (∑ q ∈ low, mass p q) + ∑ q, rowCharge p q := by
    have lower := parity_deficit (mass p) low (by rw [rows]; exact odd)
    calc
      1 ≤ ∑ q, if q ∈ low then mass p q else mass p q % 2 := lower
      _ = ∑ q, ((if q ∈ low then mass p q else 0) + rowCharge p q) := by
        apply sum_congr rfl
        intro q _
        by_cases hq : q ∈ low <;> simp [rowCharge, hp, hq]
      _ = _ := by simp [sum_add_distrib]
  have columnBound :
      top.card - (∑ q ∈ top, (mass zeroRow q + mass special q)) ≤ ∑ p, ∑ q, columnCharge p q := by
    have summed := sum_le_sum (fun q hq => columnOne q hq)
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_one, sum_add_distrib] at summed
    rw [sum_comm]
    have difference : top.card - (∑ q ∈ top, (mass zeroRow q + mass special q)) ≤
        ∑ q ∈ top, ∑ p, columnCharge p q := by
      rw [sum_add_distrib]
      omega
    exact difference.trans
      (sum_le_sum_of_subset_of_nonneg (subset_univ top) (fun _ _ _ => Nat.zero_le _))
  have rowBound :
      high.card - (∑ p ∈ high, ∑ q ∈ low, mass p q) ≤ ∑ p, ∑ q, rowCharge p q := by
    have summed := sum_le_sum (fun p hp => rowOne p hp)
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_one, sum_add_distrib] at summed
    have difference : high.card - (∑ p ∈ high, ∑ q ∈ low, mass p q) ≤
        ∑ p ∈ high, ∑ q, rowCharge p q := by omega
    exact difference.trans
      (sum_le_sum_of_subset_of_nonneg (subset_univ high) (fun _ _ _ => Nat.zero_le _))
  have together (p : P) (q : Q) :
      (if p = special then specialFlags q * weight p q else 0) +
        columnCharge p q + rowCharge p q ≤
          (if p = special then specialFlags q else mass p q % 2) * weight p q := by
    by_cases hp : p = special
    · subst p
      have notHigh : special ∉ high := fun h => ordinaryHigh special h rfl
      simp [columnCharge, rowCharge, notHigh]
    · have atCell := Nat.mul_le_mul_left (mass p q % 2) (budget p q hp)
      simpa [columnCharge, rowCharge, hp, Nat.mul_add, mul_ite] using atCell
  calc
    _ ≤ (∑ q, specialFlags q * weight special q) +
        (∑ p, ∑ q, columnCharge p q) + ∑ p, ∑ q, rowCharge p q :=
      Nat.add_le_add (Nat.add_le_add_left columnBound _) rowBound
    _ = ∑ p, ∑ q, ((if p = special then specialFlags q * weight p q else 0) +
          columnCharge p q + rowCharge p q) := by
      simp only [sum_add_distrib]
      congr 2
      rw [sum_comm]
      apply sum_congr rfl
      intro q _
      simp
    _ ≤ _ := sum_le_sum (fun p _ => sum_le_sum (fun q _ => together p q))

private theorem clean_odd_bound
    (n k low high total special outside singles : ℕ)
    (cuts : special + (n + outside - 2 * k) + (high + singles - low * k) ≤ total)
    (oddColumn : (1 ≤ special ∧ 1 ≤ outside ∧ 1 ≤ singles) ∨ 3 ≤ special) :
    1 + (n + 1 - 2 * k) + (high + 1 - low * k) ≤ total := by
  rcases oddColumn with ⟨hs, ho, hl⟩ | h
  · have cols : n + 1 - 2 * k ≤ n + outside - 2 * k := by omega
    have rows : high + 1 - low * k ≤ high + singles - low * k := by omega
    omega
  · have cols : n + 1 - 2 * k ≤ n + outside - 2 * k + 1 := by omega
    have rows : high + 1 - low * k ≤ high + singles - low * k + 1 := by omega
    omega

abbrev EvenSubset (n : ℕ) := {p : Finset (Fin n) // p.card % 2 = 0}
abbrev OddSubset (n : ℕ) := {q : Finset (Fin n) // q.card % 2 = 1}

private theorem intersection_charges (n : ℕ) (large : 6 ≤ n)
    (p : EvenSubset n) (q : OddSubset n) :
    (if q.val.card = n - 1 ∧ p.val ≠ ∅ then 1 else 0) +
      (if p.val.card = n - 2 ∧ q.val.card ≠ 1 then 1 else 0) ≤
        (p.val ∩ q.val).card := by
  have sumSizes := card_union_add_card_inter p.val q.val
  have unionCap : (p.val ∪ q.val).card ≤ n := by
    simpa using (card_le_card (subset_univ (p.val ∪ q.val)))
  have pEven := p.property
  have qOdd := q.property
  by_cases first : q.val.card = n - 1 ∧ p.val ≠ ∅
  · by_cases second : p.val.card = n - 2 ∧ q.val.card ≠ 1
    · rw [if_pos first, if_pos second]
      have := first.1
      have := second.1
      omega
    · rw [if_pos first, if_neg second]
      have nonzero : p.val.card ≠ 0 := by simpa using first.2
      have := first.1
      omega
  · by_cases second : p.val.card = n - 2 ∧ q.val.card ≠ 1
    · rw [if_neg first, if_pos second]
      have := second.1
      have := second.2
      omega
    · rw [if_neg first, if_neg second]
      exact Nat.zero_le _

private theorem rank_size (n r t : ℕ) (rh : r % 2 = t) :
    (univ.filter fun a : {x : Finset (Fin n) // x.card % 2 = t} => a.val.card = r).card =
      n.choose r := by
  classical
  let f : {x : Finset (Fin n) // x.card % 2 = t} ↪ Finset (Fin n) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have same :
      (univ.filter fun a : {x : Finset (Fin n) // x.card % 2 = t} => a.val.card = r).map f =
        (univ : Finset (Fin n)).powersetCard r := by
    ext a
    rw [mem_map, mem_powersetCard]
    constructor
    · rintro ⟨b, hb, eq⟩
      change b.val = a at eq
      exact ⟨subset_univ _, eq ▸ (mem_filter.mp hb).2⟩
    · rintro ⟨_, size⟩
      exact ⟨⟨a, size ▸ rh⟩, mem_filter.mpr ⟨mem_univ _, size⟩, rfl⟩
  rw [← card_map f, same, card_powersetCard, card_univ, Fintype.card_fin]

private theorem high_charged_mass {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q] (mass : P → Q → ℕ)
    (special : P) (high : Finset P) (low : Finset Q) (k : ℕ)
    (hs : special ∉ high) (cols : ∀ q, ∑ p, mass p q = k) :
    (∑ p ∈ high, ∑ q ∈ low, mass p q) + (∑ q ∈ low, mass special q) ≤ low.card * k := by
  rw [sum_comm (s := high) (t := low), ← sum_add_distrib]
  have colBound (q : Q) : (∑ p ∈ high, mass p q) + mass special q ≤ k := by
    rw [add_comm, ← sum_insert (f := fun p => mass p q) hs, ← cols q]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  calc
    _ ≤ ∑ _q ∈ low, k := sum_le_sum fun q _ => colBound q
    _ = _ := by simp [sum_const]

private theorem top_charged_mass {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq Q] (mass : P → Q → ℕ) (zeroRow special : P)
    (top : Finset Q) (k : ℕ) (rows : ∀ p, ∑ q, mass p q = k) :
    (∑ q ∈ top, (mass zeroRow q + mass special q)) +
      (∑ q ∈ univ \ top, mass special q) ≤ 2 * k := by
  rw [sum_add_distrib, add_assoc]
  have decompose : (∑ q ∈ top, mass special q) + (∑ q ∈ univ \ top, mass special q) = k := by
    rw [add_comm, sum_sdiff (subset_univ top), rows]
  rw [decompose]
  have h : (∑ q ∈ top, mass zeroRow q) ≤ k := by
    rw [← rows zeroRow]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  omega

/-- Odd uniform margins force a weighted intersection count controlled by the
mass of the full row outside the highest odd rank and on the singleton columns. -/
theorem weighted_rank_deficits_le_intersections (n k : ℕ) (large : 6 ≤ n) (even : n % 2 = 0)
    (odd : k % 2 = 1) (mass : EvenSubset n → OddSubset n → ℕ) (flags : OddSubset n → ℕ)
    (rows : ∀ p, ∑ q, mass p q = k) (cols : ∀ q, ∑ p, mass p q = k) :
    let full : EvenSubset n := ⟨univ, by simpa using even⟩
    (∑ q, flags q * q.val.card) +
      (n + (∑ q ∈ univ.filter (fun q : OddSubset n => q.val.card ≠ n - 1), mass full q)
        - 2 * k) +
      (n.choose 2 + (∑ q ∈ univ.filter (fun q : OddSubset n => q.val.card = 1), mass full q)
        - n * k) ≤
      ∑ p : EvenSubset n, ∑ q : OddSubset n,
        (if p.val = univ then flags q else mass p q % 2) * (p.val ∩ q.val).card := by
  let all : EvenSubset n := ⟨univ, by simpa using even⟩
  let zero : EvenSubset n := ⟨∅, by simp⟩
  let top : Finset (OddSubset n) := univ.filter fun q => q.val.card = n - 1
  let low : Finset (OddSubset n) := univ.filter fun q => q.val.card = 1
  let high : Finset (EvenSubset n) := univ.filter fun p => p.val.card = n - 2
  let weight (p : EvenSubset n) (q : OddSubset n) := (p.val ∩ q.val).card
  let outside := ∑ q ∈ univ \ top, mass all q
  let singles := ∑ q ∈ low, mass all q
  let special := ∑ q, flags q * weight all q
  let total := ∑ p, ∑ q, (if p = all then flags q else mass p q % 2) * weight p q
  have different : zero ≠ all := by
    intro same
    have eq := congrArg (fun p : EvenSubset n => p.val.card) same
    simp [zero, all] at eq
    omega
  have highOrdinary : ∀ p ∈ high, p ≠ all := by
    rintro p hp rfl
    simp [high, all] at hp
    omega
  have rule (p : EvenSubset n) (q : OddSubset n) (_ : p ≠ all) :
      (if q ∈ top ∧ p ≠ zero then 1 else 0) +
        (if p ∈ high ∧ q ∉ low then 1 else 0) ≤ weight p q := by
    have pzero : p = zero ↔ p.val = ∅ :=
      ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩
    simpa [pzero, top, high, low, weight] using intersection_charges n large p q
  have rankSum := rank_cuts mass weight flags zero all different top low high k odd rows cols
    highOrdinary rule
  have topSize : top.card = n := by
    unfold top
    rw [rank_size n (n - 1) 1 (by omega), Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right]
  have highSize : high.card = n.choose 2 := by
    unfold high
    rw [rank_size n (n - 2) 0 (by omega), Nat.choose_symm (by omega : 2 ≤ n)]
  have lowSize : low.card = n := by
    unfold low
    rw [rank_size n 1 1 rfl, Nat.choose_one_right]
  have hTop := top_charged_mass mass zero all top k rows
  have hHigh := high_charged_mass mass all high low k (fun h => highOrdinary all h rfl) cols
  rw [topSize, highSize] at rankSum
  rw [lowSize] at hHigh
  change (∑ q ∈ top, (mass zero q + mass all q)) + outside ≤ 2 * k at hTop
  change (∑ p ∈ high, ∑ q ∈ low, mass p q) + singles ≤ n * k at hHigh
  change special + (n - (∑ q ∈ top, (mass zero q + mass all q))) +
    (n.choose 2 - (∑ p ∈ high, ∑ q ∈ low, mass p q)) ≤ total at rankSum
  have estimates : special + (n + outside - 2 * k) + (n.choose 2 + singles - n * k) ≤ total := by
    omega
  have outsideFilter : univ \ top = univ.filter (fun q : OddSubset n => q.val.card ≠ n - 1) := by
    ext q
    simp [top]
  have sameFull (p : EvenSubset n) : p = all ↔ p.val = univ :=
    ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩
  simpa only [special, outside, singles, outsideFilter, low, weight, all, univ_inter, total,
    sameFull] using estimates

/-- A positive flag within the full row gives a dimension-only lower bound. -/
theorem fixed_from_odd_margins (n k : ℕ) (large : 6 ≤ n) (even : n % 2 = 0)
    (odd : k % 2 = 1) (mass : EvenSubset n → OddSubset n → ℕ) (flags : OddSubset n → ℕ)
    (rows : ∀ p, ∑ q, mass p q = k) (cols : ∀ q, ∑ p, mass p q = k)
    (flagFits : ∀ q, flags q ≤ mass ⟨univ, by simpa using even⟩ q)
    (someFlag : ∃ q, 0 < flags q) :
    1 + (n + 1 - 2 * k) + (n.choose 2 + 1 - n * k) ≤
      ∑ p : EvenSubset n, ∑ q : OddSubset n,
        (if p.val = univ then flags q else mass p q % 2) * (p.val ∩ q.val).card := by
  let all : EvenSubset n := ⟨univ, by simpa using even⟩
  let outsideColumns := univ.filter (fun q : OddSubset n => q.val.card ≠ n - 1)
  let singletonColumns := univ.filter (fun q : OddSubset n => q.val.card = 1)
  let outside := ∑ q ∈ outsideColumns, mass all q
  let singles := ∑ q ∈ singletonColumns, mass all q
  let special := ∑ q, flags q * q.val.card
  let total := ∑ p : EvenSubset n, ∑ q : OddSubset n,
    (if p.val = univ then flags q else mass p q % 2) * (p.val ∩ q.val).card
  have estimates : special + (n + outside - 2 * k) + (n.choose 2 + singles - n * k) ≤ total :=
    weighted_rank_deficits_le_intersections n k large even odd mass flags rows cols
  obtain ⟨q, hq⟩ := someFlag
  have specialLower : q.val.card ≤ special := by
    have h : flags q * q.val.card ≤ special :=
      single_le_sum (f := fun q => flags q * q.val.card)
        (fun _ _ => Nat.zero_le _) (mem_univ q)
    have lower := Nat.mul_le_mul_right q.val.card (show 1 ≤ flags q by omega)
    simpa using lower.trans h
  have flagAtMost : flags q ≤ mass all q := flagFits q
  have qOdd := q.property
  have oddColumn : (1 ≤ special ∧ 1 ≤ outside ∧ 1 ≤ singles) ∨ 3 ≤ special := by
    by_cases isOne : q.val.card = 1
    · have qLow : q ∈ singletonColumns := by simp [singletonColumns, isOne]
      have qOutside : q ∈ outsideColumns := by
        simp [outsideColumns, isOne]
        omega
      have lowerOutside : mass all q ≤ outside :=
        single_le_sum (fun _ _ => Nat.zero_le _) qOutside
      have lowerSingles : mass all q ≤ singles :=
        single_le_sum (fun _ _ => Nat.zero_le _) qLow
      left
      omega
    · right
      omega
  exact clean_odd_bound n k n (n.choose 2) total special outside singles estimates oddColumn

end D5.S3.ConceptDynamics.Attribution.ParityOddRankBounds
