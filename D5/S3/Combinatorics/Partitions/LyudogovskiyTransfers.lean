/- GID: D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/LyudogovskiyTransfers
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram]
   utility: none
   digest: Native partition transfers and their two-way Young-diagram bridge. -/

import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts

/-! Native integer-partition transfers are exactly one-cell Young-diagram exchanges. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Combinatorics.Partitions.LyudogovskiySimplex

/-- A zero row is omitted; a positive row contributes one occurrence. -/
def part (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

/-- The two displayed slots are distinct occurrences, even when their sizes agree.
The first slot donates one unit; the second may be the virtual zero recipient. -/
def UnitTransfer {n : ℕ} (p q : Nat.Partition n) : Prop :=
  p ≠ q ∧ ∃ (s : Multiset ℕ) (a b : ℕ),
    p.parts = {a + 1} + part b + s ∧
    q.parts = part a + {b + 1} + s

private theorem transfer_symm {n : ℕ} {p q : Nat.Partition n}
    (h : UnitTransfer p q) : UnitTransfer q p := by
  obtain ⟨hne, s, a, b, hp, hq⟩ := h
  refine ⟨hne.symm, s, b, a, ?_, ?_⟩
  · simpa [add_comm, add_left_comm, add_assoc] using hq
  · simpa [add_comm, add_left_comm, add_assoc] using hp

/-- The source simple graph on all integer partitions of n. -/
def graph (n : ℕ) : SimpleGraph (Nat.Partition n) where
  Adj := UnitTransfer
  symm := ⟨fun _ _ h => transfer_symm h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem column_count (d : YoungDiagram) (j : ℕ) :
    (d.rowLens : Multiset ℕ).countP (fun k => j < k) = d.colLen j := by
  have hf : (Finset.range (d.colLen 0)).filter (fun i => j < d.rowLen i) =
      Finset.range (d.colLen j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
    constructor
    · exact And.right
    · intro hi
      exact ⟨lt_of_lt_of_le hi (d.colLen_anti 0 j (Nat.zero_le j)), hi⟩
  change ((List.range (d.colLen 0)).map d.rowLen).countP (fun k => decide (j < k)) = _
  rw [List.countP_map, List.countP_eq_length_filter]
  have hc := congrArg Finset.card hf
  simpa only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.coe_card, List.length_range, Function.comp_def] using hc

private theorem partition_column_count {n : ℕ} (p : Nat.Partition n) (j : ℕ) :
    p.parts.countP (fun k => j < k) = (YoungDiagram.ofPartition p).colLen j := by
  have h := column_count (YoungDiagram.ofPartition p) j
  simpa using h

theorem part_sum (k : ℕ) : (part k).sum = k := by
  by_cases h : k = 0 <;> simp [part, h]

private theorem part_count (k j : ℕ) :
    (part k).countP (fun x => j < x) = if j < k then 1 else 0 := by
  by_cases h : k = 0 <;> by_cases hj : j < k <;>
    simp [part, h, Multiset.countP_eq_card_filter, Multiset.filter_singleton, hj]

private theorem singleton_count (k j : ℕ) :
    ({k} : Multiset ℕ).countP (fun x => j < x) = if j < k then 1 else 0 := by
  by_cases h : j < k <;> simp [Multiset.countP_eq_card_filter, Multiset.filter_singleton, h]

private theorem part_positive {k x : ℕ} (h : x ∈ part k) : 0 < x := by
  by_cases hk : k = 0
  · simp [part, hk] at h
  · simp [part, hk] at h
    omega

private theorem diagram_le_of_counts {m n : ℕ} (p : Nat.Partition m) (q : Nat.Partition n)
    (h : ∀ j : ℕ, p.parts.countP (fun x => j < x) ≤
      q.parts.countP (fun x => j < x)) :
    YoungDiagram.ofPartition p ≤ YoungDiagram.ofPartition q := by
  intro ⟨i,j⟩ hi
  rw [YoungDiagram.mem_iff_lt_colLen] at hi ⊢
  exact lt_of_lt_of_le hi (by simpa only [partition_column_count] using h j)

theorem diagram_injective {n : ℕ} :
    Function.Injective (YoungDiagram.ofPartition (n := n)) := by
  intro p q h
  have hh : YoungDiagram.equivPartition.symm p = YoungDiagram.equivPartition.symm q :=
    Subtype.ext h
  exact YoungDiagram.equivPartition.symm.injective hh

private theorem transfer_predecessor {n : ℕ} {p q : Nat.Partition n}
    (h : UnitTransfer p q) : ∃ m : Nat.Partition (n - 1),
      YoungDiagram.ofPartition m ≤ YoungDiagram.ofPartition p ∧
      YoungDiagram.ofPartition m ≤ YoungDiagram.ofPartition q := by
  obtain ⟨_, s, a, b, hp, hq⟩ := h
  have hpos : ∀ x ∈ s, 0 < x := by
    intro x hx
    apply p.parts_pos
    rw [hp]
    simp only [Multiset.mem_add]
    exact Or.inr hx
  have hs : (part a + part b + s).sum = n - 1 := by
    have hn := p.parts_sum
    rw [hp] at hn
    simp only [Multiset.sum_add, Multiset.sum_singleton] at hn ⊢
    rw [part_sum] at hn
    rw [part_sum, part_sum]
    omega
  let m : Nat.Partition (n - 1) := ⟨part a + part b + s, by
    intro x hx
    simp only [Multiset.mem_add] at hx
    rcases hx with (hx | hx) | hx
    · exact part_positive hx
    · exact part_positive hx
    · exact hpos x hx, hs⟩
  refine ⟨m, diagram_le_of_counts m p ?_, diagram_le_of_counts m q ?_⟩
  · intro j
    change (part a + part b + s).countP (fun x => j < x) ≤ _
    rw [hp]
    simp only [Multiset.countP_add, part_count, singleton_count]
    split_ifs <;> omega
  · intro j
    change (part a + part b + s).countP (fun x => j < x) ≤ _
    rw [hq]
    simp only [Multiset.countP_add, part_count, singleton_count]
    split_ifs <;> omega

private theorem diagram_eq_of_le {n : ℕ} {p q : Nat.Partition n}
    (h : YoungDiagram.ofPartition p ≤ YoungDiagram.ofPartition q) : p = q := by
  apply diagram_injective
  apply YoungDiagram.ext
  apply Finset.eq_of_subset_of_card_le h
  simp

private theorem transfer_intersection {n : ℕ} {p q : Nat.Partition n}
    (h : UnitTransfer p q) :
    ((YoungDiagram.ofPartition p) ⊓ (YoungDiagram.ofPartition q)).card = n - 1 := by
  obtain ⟨m, hmp, hmq⟩ := transfer_predecessor h
  have hlo := Finset.card_le_card (show (YoungDiagram.ofPartition m).cells ⊆
      ((YoungDiagram.ofPartition p) ⊓ (YoungDiagram.ofPartition q)).cells from
    le_inf hmp hmq)
  have hstrict : ((YoungDiagram.ofPartition p) ⊓ (YoungDiagram.ofPartition q)).cells ⊂
      (YoungDiagram.ofPartition p).cells := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨inf_le_left, ?_⟩
    intro he
    have hpq : YoungDiagram.ofPartition p ≤ YoungDiagram.ofPartition q := by
      intro c hc
      have : c ∈ (YoungDiagram.ofPartition p ⊓ YoungDiagram.ofPartition q).cells := he.symm ▸ hc
      exact (YoungDiagram.mem_inf.mp this).2
    exact h.1 (diagram_eq_of_le hpq)
  have hhi := Finset.card_lt_card hstrict
  change (YoungDiagram.ofPartition m).card ≤
    (YoungDiagram.ofPartition p ⊓ YoungDiagram.ofPartition q).card at hlo
  change (YoungDiagram.ofPartition p ⊓ YoungDiagram.ofPartition q).card <
    (YoungDiagram.ofPartition p).card at hhi
  simp only [YoungDiagram.card_ofPartition] at hlo hhi
  omega

theorem row_parts (d : YoungDiagram) (H : ℕ) (hH : d.colLen 0 ≤ H) :
    (∑ i ∈ Finset.range H, part (d.rowLen i)) = (d.rowLens : Multiset ℕ) := by
  calc
    _ = ∑ i ∈ Finset.range (d.colLen 0), part (d.rowLen i) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hH)
      intro i hi hn
      have hz := D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts.rowLen_zero d i
        (by simpa only [Finset.mem_range, not_lt] using hn)
      simp [hz, part]
    _ = ∑ i ∈ Finset.range (d.colLen 0), ({d.rowLen i} : Multiset ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hp : 0 < d.rowLen i := by
        apply YoungDiagram.mem_iff_lt_rowLen.mp
        apply YoungDiagram.mem_iff_lt_colLen.mpr
        exact Finset.mem_range.mp hi
      simp [part, Nat.ne_of_gt hp]
    _ = _ := by
      rw [Finset.sum_eq_multiset_sum]
      simpa only [Multiset.map_map, Function.comp_def, Finset.range_val,
        Multiset.range, Multiset.map_coe, List.map_map, Function.comp_def,
        YoungDiagram.rowLens] using
        Multiset.sum_map_singleton ((Finset.range (d.colLen 0)).val.map d.rowLen)

private theorem one_cell_row {A B : YoungDiagram} {c : ℕ × ℕ}
    (h : A.cells \ B.cells = {c}) : A.rowLen c.1 = c.2 + 1 := by
  have hc : c ∈ A ∧ c ∉ B := by
    have : c ∈ A.cells \ B.cells := by rw [h]; simp
    exact Finset.mem_sdiff.mp this
  have hp := YoungDiagram.mem_iff_lt_rowLen.mp hc.1
  have hn : ¬ (c.1, c.2 + 1) ∈ A := by
    intro hh
    have hB : (c.1, c.2 + 1) ∉ B := by
      intro hb
      exact hc.2 (B.up_left_mem le_rfl (by omega) hb)
    have : (c.1, c.2 + 1) ∈ A.cells \ B.cells := Finset.mem_sdiff.mpr ⟨hh,hB⟩
    rw [h] at this
    have he := congrArg Prod.snd (Finset.mem_singleton.mp this)
    omega
  rw [YoungDiagram.mem_iff_lt_rowLen] at hn
  omega

private theorem one_cell_other_rows {A B : YoungDiagram} {c d : ℕ × ℕ}
    (hAB : A.cells \ B.cells = {c}) (hBA : B.cells \ A.cells = {d})
    (i : ℕ) (hic : i ≠ c.1) (hid : i ≠ d.1) : A.rowLen i = B.rowLen i := by
  apply Nat.le_antisymm
  · by_contra! hh
    have ha : (i, B.rowLen i) ∈ A := YoungDiagram.mem_iff_lt_rowLen.mpr hh
    have hb : (i, B.rowLen i) ∉ B := by simp [YoungDiagram.mem_iff_lt_rowLen]
    have hm := Finset.mem_sdiff.mpr ⟨ha,hb⟩
    rw [hAB] at hm
    exact hic (congrArg Prod.fst (Finset.mem_singleton.mp hm))
  · by_contra! hh
    have hb : (i, A.rowLen i) ∈ B := YoungDiagram.mem_iff_lt_rowLen.mpr hh
    have ha : (i, A.rowLen i) ∉ A := by simp [YoungDiagram.mem_iff_lt_rowLen]
    have hm := Finset.mem_sdiff.mpr ⟨hb,ha⟩
    rw [hBA] at hm
    exact hid (congrArg Prod.fst (Finset.mem_singleton.mp hm))

private theorem one_cell_lower_row {A B : YoungDiagram} {c : ℕ × ℕ}
    (h : A.cells \ B.cells = {c}) : B.rowLen c.1 = c.2 := by
  have hc : c ∈ A ∧ c ∉ B := by
    have : c ∈ A.cells \ B.cells := by rw [h]; simp
    exact Finset.mem_sdiff.mp this
  have hp := one_cell_row h
  have hu : B.rowLen c.1 ≤ c.2 := by
    have hh := hc.2
    rw [YoungDiagram.mem_iff_lt_rowLen] at hh
    omega
  apply le_antisymm hu
  by_contra! hh
  have ha : (c.1, B.rowLen c.1) ∈ A := by
    apply YoungDiagram.mem_iff_lt_rowLen.mpr
    omega
  have hb : (c.1, B.rowLen c.1) ∉ B := by simp [YoungDiagram.mem_iff_lt_rowLen]
  have hm := Finset.mem_sdiff.mpr ⟨ha,hb⟩
  rw [h] at hm
  have he := congrArg Prod.snd (Finset.mem_singleton.mp hm)
  omega

private theorem row_parts_split (d : YoungDiagram) (H i j : ℕ)
    (hH : d.colLen 0 ≤ H) (hi : i ∈ Finset.range H) (hj : j ∈ Finset.range H)
    (hij : i ≠ j) :
    (d.rowLens : Multiset ℕ) = part (d.rowLen i) + part (d.rowLen j) +
      ∑ k ∈ ((Finset.range H).erase i).erase j, part (d.rowLen k) := by
  rw [← row_parts d H hH]
  have hj' : j ∈ (Finset.range H).erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  rw [← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hj']
  exact (add_assoc _ _ _).symm

private theorem intersection_transfer {n : ℕ} (hn : 0 < n) (p q : Nat.Partition n)
    (h : ((YoungDiagram.ofPartition p) ⊓ (YoungDiagram.ofPartition q)).card = n - 1) :
    UnitTransfer p q := by
  let A := YoungDiagram.ofPartition p
  let B := YoungDiagram.ofPartition q
  have hA : A.card = n := YoungDiagram.card_ofPartition p
  have hB : B.card = n := YoungDiagram.card_ofPartition q
  have hnq : p ≠ q := by
    intro he
    subst q
    simp only [inf_idem, YoungDiagram.card_ofPartition] at h
    omega
  have hcAB : (A.cells \ B.cells).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_comm]
    change A.card - (A ⊓ B).card = 1
    rw [hA, h]
    omega
  have hcBA : (B.cells \ A.cells).card = 1 := by
    rw [Finset.card_sdiff]
    change B.card - (A ⊓ B).card = 1
    rw [hB, h]
    omega
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hcAB
  obtain ⟨d,hd⟩ := Finset.card_eq_one.mp hcBA
  have hcm : c ∈ A ∧ c ∉ B := by
    apply Finset.mem_sdiff.mp
    rw [hc]
    simp
  have hdm : d ∈ B ∧ d ∉ A := by
    apply Finset.mem_sdiff.mp
    rw [hd]
    simp
  have hcd : c.1 ≠ d.1 := by
    intro he
    by_cases hle : c.2 ≤ d.2
    · exact hcm.2 (B.up_left_mem (by omega) hle hdm.1)
    · exact hdm.2 (A.up_left_mem (by omega) (by omega) hcm.1)
  let H := max (A.colLen 0) (B.colLen 0)
  have hAH : A.colLen 0 ≤ H := Nat.le_max_left _ _
  have hBH : B.colLen 0 ≤ H := Nat.le_max_right _ _
  have hci : c.1 ∈ Finset.range H := by
    apply Finset.mem_range.mpr
    have hh : c.1 < A.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp
      (A.up_left_mem le_rfl (Nat.zero_le _) hcm.1)
    omega
  have hdi : d.1 ∈ Finset.range H := by
    apply Finset.mem_range.mpr
    have hh : d.1 < B.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp
      (B.up_left_mem le_rfl (Nat.zero_le _) hdm.1)
    omega
  let s := ∑ k ∈ ((Finset.range H).erase c.1).erase d.1, part (A.rowLen k)
  have hs : s = ∑ k ∈ ((Finset.range H).erase c.1).erase d.1, part (B.rowLen k) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_erase] at hk
    rw [one_cell_other_rows hc hd k hk.2.1 hk.1]
  refine ⟨hnq, s, c.2, d.2, ?_, ?_⟩
  · have hh := row_parts_split A H c.1 d.1 hAH hci hdi hcd
    rw [one_cell_row hc, one_cell_lower_row hd] at hh
    simpa [A, part, s] using hh
  · have hh := row_parts_split B H c.1 d.1 hBH hci hdi hcd
    rw [one_cell_lower_row hc, one_cell_row hd, ← hs] at hh
    simpa [B, part, s] using hh

/-- Reordering and repeated row blocks preserve the literal unit-transfer graph. -/
theorem transfer_iff_intersection {n : ℕ} (hn : 0 < n) (p q : Nat.Partition n) :
    UnitTransfer p q ↔
      ((YoungDiagram.ofPartition p) ⊓ (YoungDiagram.ofPartition q)).card = n - 1 :=
  ⟨transfer_intersection, intersection_transfer hn p q⟩

end D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
