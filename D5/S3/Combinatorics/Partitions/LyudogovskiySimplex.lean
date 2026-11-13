/- GID: D5/S3/Combinatorics/Partitions/LyudogovskiySimplex
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/LyudogovskiySimplex
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram]
   utility: none
   digest: Integer-partition unit transfers and exact local clique layers. -/

import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import D5.S1.Words.Compositions.StrictFirstSumsGapfreeOddParts

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
  symm := fun _ _ h => transfer_symm h
  loopless := fun _ h => h.1 rfl

/-- All actual finite cliques, including singletons and the empty clique. -/
def cliques (n : ℕ) : Finset (Finset (Nat.Partition n)) := by
  classical
  exact Finset.univ.powerset.filter (fun s => (graph n).IsClique (s : Set (Nat.Partition n)))

/-- Maximum clique cardinality containing p, minus one. -/
def localDimension {n : ℕ} (p : Nat.Partition n) : ℕ :=
  ((cliques n).filter (p ∈ ·)).sup (fun s => s.card - 1)

/-- This is the exact local-dimension level, rather than a superlevel. -/
def layer (r n : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter (fun p => localDimension p = r)

def maxDimension (n : ℕ) : ℕ := Finset.univ.sup (fun p : Nat.Partition n => localDimension p)

/-- The infimum convention has value zero if the set is empty.
The threshold assertion includes existence and positive leastness. -/
def threshold (r : ℕ) : ℕ := sInf {n : ℕ | 0 < n ∧ (layer r n).Nonempty}

def triangular (r : ℕ) : ℕ := r * (r + 1) / 2

/-- The finite Young ideal of the staircase (r,r-1,...,1), including r=0. -/
def staircase (r : ℕ) : YoungDiagram where
  cells := ((Finset.range r).product (Finset.range r)).filter (fun c => c.1 + c.2 < r)
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at *
    exact ⟨⟨lt_of_le_of_lt hxy.1 hy.1.1, lt_of_le_of_lt hxy.2 hy.1.2⟩,
      lt_of_le_of_lt (Nat.add_le_add hxy.1 hxy.2) hy.2⟩

/-- A genuine one-cell Young extension of the staircase. -/
def firstFamily (r n : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter (fun p => (staircase r).cells ⊆ (YoungDiagram.ofPartition p).cells ∧
    ((YoungDiagram.ofPartition p).cells \ (staircase r).cells).card = 1)

/-- The complete threshold and global-maximum question, with existence explicit. -/
def ThresholdClaim : Prop :=
  (∀ r : ℕ, threshold r = triangular r + 1 ∧
    IsLeast {n : ℕ | 0 < n ∧ (layer r n).Nonempty} (triangular r + 1)) ∧
  (∀ n : ℕ, 0 < n → maxDimension n =
    ((Finset.range (n + 1)).filter (fun r => triangular r + 1 ≤ n)).sup id)

/-- Both inclusions at the literal threshold, and the exact distinct-family count. -/
def FirstOccurrenceClaim : Prop := ∀ r : ℕ, 2 ≤ r →
  layer r (threshold r) = firstFamily r (threshold r) ∧
  layer r (triangular r + 1) = firstFamily r (triangular r + 1) ∧
  (firstFamily r (threshold r)).card = r + 1

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
  have hc := congrArg Finset.card hf
  simpa [YoungDiagram.rowLens, Multiset.countP_map, Multiset.countP_eq_card_filter,
    Finset.filter_val, Finset.range_val] using hc

private theorem partition_column_count {n : ℕ} (p : Nat.Partition n) (j : ℕ) :
    p.parts.countP (fun k => j < k) = (YoungDiagram.ofPartition p).colLen j := by
  have h := column_count (YoungDiagram.ofPartition p) j
  simpa using h

private theorem part_sum (k : ℕ) : (part k).sum = k := by
  by_cases h : k = 0 <;> simp [part, h]

private theorem part_count (k j : ℕ) :
    (part k).countP (fun x => j < x) = if j < k then 1 else 0 := by
  by_cases h : k = 0 <;> simp [part, h]

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

private theorem diagram_injective {n : ℕ} :
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
    simp only [Multiset.countP_add, part_count, Multiset.countP_singleton]
    split_ifs <;> omega
  · intro j
    change (part a + part b + s).countP (fun x => j < x) ≤ _
    rw [hq]
    simp only [Multiset.countP_add, part_count, Multiset.countP_singleton]
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
  change (YoungDiagram.ofPartition m).card ≤ _ at hlo
  change _ < (YoungDiagram.ofPartition p).card at hhi
  simp only [YoungDiagram.card_ofPartition] at hlo hhi
  omega

private theorem row_parts (d : YoungDiagram) (H : ℕ) (hH : d.colLen 0 ≤ H) :
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
      change (((Finset.range (d.colLen 0)).val.map d.rowLen).map
        (fun k => ({k} : Multiset ℕ))).sum = _
      rw [Multiset.sum_map_singleton]
      rfl

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
    simp only [Finset.mem_singleton, Prod.mk.injEq] at this
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
    simpa [A, part] using hh
  · have hh := row_parts_split B H c.1 d.1 hBH hci hdi hcd
    rw [one_cell_lower_row hc, one_cell_row hd, ← hs] at hh
    simpa [B, part] using hh

/-- Reordering and repeated row blocks preserve the literal unit-transfer graph. -/
theorem transfer_iff_intersection {n : ℕ} (hn : 0 < n) (p q : Nat.Partition n) :
    UnitTransfer p q ↔
      ((YoungDiagram.ofPartition p) ⊓ (YoungDiagram.ofPartition q)).card = n - 1 :=
  ⟨transfer_intersection, intersection_transfer hn p q⟩

private theorem clique_difference {n : ℕ} (hn : 0 < n)
    {C : Finset (Nat.Partition n)} (hC : (graph n).IsClique (C : Set (Nat.Partition n)))
    {p q : Nat.Partition n} (hp : p ∈ C) (hq : q ∈ C) :
    ((YoungDiagram.ofPartition p).cells \ (YoungDiagram.ofPartition q).cells).card ≤ 1 := by
  by_cases he : p = q
  · subst q
    simp
  · have ht := (transfer_iff_intersection hn p q).mp (hC hp hq he)
    rw [Finset.card_sdiff, Finset.inter_comm]
    change (YoungDiagram.ofPartition p).card -
      (YoungDiagram.ofPartition p ⊓ YoungDiagram.ofPartition q).card ≤ 1
    rw [YoungDiagram.card_ofPartition, ht]
    omega

private theorem clique_star_or_top {n : ℕ} (hn : 0 < n)
    (C : Finset (Nat.Partition n))
    (hC : (graph n).IsClique (C : Set (Nat.Partition n))) (hcard : 2 ≤ C.card) :
    (∃ X : YoungDiagram, X.card = n - 1 ∧
      ∀ p ∈ C, X ≤ YoungDiagram.ofPartition p) ∨
    (∃ U : YoungDiagram, U.card = n + 1 ∧
      ∀ p ∈ C, YoungDiagram.ofPartition p ≤ U) := by
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < C.card)
  let A := YoungDiagram.ofPartition p
  let B := YoungDiagram.ofPartition q
  let X := A ⊓ B
  let U := A ⊔ B
  have hX : X.card = n - 1 := (transfer_iff_intersection hn p q).mp (hC hp hq hpq)
  have hU : U.card = n + 1 := by
    have hc := Finset.card_inter_add_card_union A.cells B.cells
    change X.card + U.card = A.card + B.card at hc
    simp only [A, B, YoungDiagram.card_ofPartition] at hc
    omega
  have hdich (v : Nat.Partition n) (hv : v ∈ C) :
      X ≤ YoungDiagram.ofPartition v ∨ YoungDiagram.ofPartition v ≤ U := by
    classical
    by_cases hs : X ≤ YoungDiagram.ofPartition v
    · exact Or.inl hs
    · right
      change ¬ X.cells ⊆ (YoungDiagram.ofPartition v).cells at hs
      obtain ⟨x,hx,hxv⟩ := Finset.not_subset.mp hs
      have hxA : x ∈ A.cells := (YoungDiagram.mem_inf.mp hx).1
      have hxB : x ∈ B.cells := (YoungDiagram.mem_inf.mp hx).2
      have hAv := clique_difference hn hC hp hv
      have hBv := clique_difference hn hC hq hv
      have hsub : U.cells.erase x ⊆ (YoungDiagram.ofPartition v).cells := by
        intro y hy
        obtain ⟨hyx,hy⟩ := Finset.mem_erase.mp hy
        rcases YoungDiagram.mem_sup.mp hy with hyA | hyB
        · by_contra hyv
          have he := Finset.card_le_one.mp hAv y (Finset.mem_sdiff.mpr ⟨hyA,hyv⟩)
            x (Finset.mem_sdiff.mpr ⟨hxA,hxv⟩)
          exact hyx he
        · by_contra hyv
          have he := Finset.card_le_one.mp hBv y (Finset.mem_sdiff.mpr ⟨hyB,hyv⟩)
            x (Finset.mem_sdiff.mpr ⟨hxB,hxv⟩)
          exact hyx he
      have hsize : (U.cells.erase x).card = n := by
        rw [Finset.card_erase_of_mem (YoungDiagram.mem_sup.mpr (Or.inl hxA))]
        change U.card - 1 = n
        rw [hU]
        omega
      have he : U.cells.erase x = (YoungDiagram.ofPartition v).cells := by
        apply Finset.eq_of_subset_of_card_le hsub
        change (YoungDiagram.ofPartition v).card ≤ _
        rw [YoungDiagram.card_ofPartition, hsize]
      intro y hy
      exact Finset.mem_of_mem_erase (he.symm ▸ hy)
  by_cases hstar : ∀ p ∈ C, X ≤ YoungDiagram.ofPartition p
  · exact Or.inl ⟨X,hX,hstar⟩
  · right
    push_neg at hstar
    obtain ⟨d,hd,hdX⟩ := hstar
    have hdU := (hdich d hd).resolve_left hdX
    change ¬ X.cells ⊆ (YoungDiagram.ofPartition d).cells at hdX
    obtain ⟨x,hx,hxd⟩ := Finset.not_subset.mp hdX
    refine ⟨U,hU,?_⟩
    intro v hv
    by_contra hnv
    have hvX := (hdich v hv).resolve_right hnv
    change ¬ (YoungDiagram.ofPartition v).cells ⊆ U.cells at hnv
    obtain ⟨y,hy,hyU⟩ := Finset.not_subset.mp hnv
    have hxy := Finset.card_le_one.mp (clique_difference hn hC hv hd)
      x (Finset.mem_sdiff.mpr ⟨hvX hx,hxd⟩)
      y (Finset.mem_sdiff.mpr ⟨hy,fun hyd => hyU (hdU hyd)⟩)
    have hxU : x ∈ U := le_sup_of_le_left inf_le_left hx
    exact hyU (hxy ▸ hxU)

end D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
