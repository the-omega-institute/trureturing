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

private theorem grid_enumeration (A : Finset (ℕ × ℕ))
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ x ≤ y) :
    ∃ c : Fin A.card → ℕ × ℕ, (∀ i, c i ∈ A) ∧
      StrictMono (fun i => (c i).1) ∧ StrictAnti (fun i => (c i).2) := by
  classical
  have hinj : Set.InjOn Prod.fst (A : Set (ℕ × ℕ)) := by
    intro x hx y hy he
    by_contra hne
    rcases le_total x.2 y.2 with hs | hs
    · exact hA x hx y hy hne ⟨le_of_eq he,hs⟩
    · exact hA y hy x hx hne.symm ⟨le_of_eq he.symm,hs⟩
  let rows := A.image Prod.fst
  have hr : rows.card = A.card := Finset.card_image_of_injOn hinj
  let e := rows.orderEmbOfFin hr
  have hm (i : Fin A.card) : ∃ c ∈ A, c.1 = e i :=
    Finset.mem_image.mp (rows.orderEmbOfFin_mem hr i)
  let c (i : Fin A.card) := Classical.choose (hm i)
  have hc (i : Fin A.card) : c i ∈ A ∧ (c i).1 = e i := Classical.choose_spec (hm i)
  refine ⟨c, fun i => (hc i).1, ?_, ?_⟩
  · intro i j hij
    rw [(hc i).2, (hc j).2]
    exact e.strictMono hij
  · intro i j hij
    have hrow : (c i).1 < (c j).1 := by
      rw [(hc i).2, (hc j).2]
      exact e.strictMono hij
    have hne : c i ≠ c j := by intro he; rw [he] at hrow; omega
    have hn := hA (c i) (hc i).1 (c j) (hc j).1 hne
    by_contra! hs
    exact hn ⟨le_of_lt hrow,hs⟩

private theorem strict_mono_index {q : ℕ} (f : Fin q → ℕ) (hf : StrictMono f)
    (i : Fin q) : i.val ≤ f i := by
  have hh : ∀ k : ℕ, ∀ hk : k < q, k ≤ f ⟨k,hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; omega
    | succ k ih =>
      intro hk
      have hk' : k < q := by omega
      have hi := ih hk'
      have hs := hf (show (⟨k,hk'⟩ : Fin q) < ⟨k+1,hk⟩ by simp)
      omega
  exact hh i.val i.isLt

private theorem antichain_staircase (d : YoungDiagram) (A : Finset (ℕ × ℕ))
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ x ≤ y)
    (hbelow : ∀ c ∈ A, ∀ x : ℕ × ℕ, x ≤ c → x ≠ c → x ∈ d) :
    staircase (A.card - 1) ≤ d := by
  obtain ⟨c,hc,hfirst,hsecond⟩ := grid_enumeration A hA
  have hlast : StrictMono (fun i => (c i.rev).2) := by
    intro i j hij
    exact hsecond (Fin.rev_lt_rev.mpr hij)
  intro x hx
  have hx' : x.1 + x.2 < A.card - 1 := (Finset.mem_filter.mp hx).2
  have hi : x.1 < A.card := by omega
  let i : Fin A.card := ⟨x.1,hi⟩
  have hrow := strict_mono_index (fun i => (c i).1) hfirst i
  have hcol := strict_mono_index (fun i => (c i.rev).2) hlast i.rev
  simp only [Fin.rev_rev, Fin.val_rev] at hcol
  apply hbelow (c i) (hc i) x
  · constructor <;> dsimp [i] at * <;> omega
  · intro he
    have he' := congrArg Prod.snd he
    dsimp [i] at *
    omega

private theorem maximal_antichain_staircase (d : YoungDiagram) (A : Finset (ℕ × ℕ))
    (hA : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ x ≤ y)
    (hmem : ∀ c ∈ A, c ∈ d) : staircase A.card ≤ d := by
  obtain ⟨c,hc,hfirst,hsecond⟩ := grid_enumeration A hA
  have hlast : StrictMono (fun i => (c i.rev).2) := by
    intro i j hij
    exact hsecond (Fin.rev_lt_rev.mpr hij)
  intro x hx
  have hx' : x.1 + x.2 < A.card := (Finset.mem_filter.mp hx).2
  have hi : x.1 < A.card := by omega
  let i : Fin A.card := ⟨x.1,hi⟩
  have hrow := strict_mono_index (fun i => (c i).1) hfirst i
  have hcol := strict_mono_index (fun i => (c i.rev).2) hlast i.rev
  simp only [Fin.rev_rev, Fin.val_rev] at hcol
  apply d.isLowerSet (b := c i) ?_ (hmem (c i) (hc i))
  constructor <;> dsimp [i] at * <;> omega

private theorem single_extension_cells {X d : YoungDiagram} {c : ℕ × ℕ}
    (hsub : X ≤ d) (hdiff : d.cells \ X.cells = {c}) : d.cells = insert c X.cells := by
  ext x
  have hh := Finset.ext_iff.mp hdiff x
  simp only [Finset.mem_sdiff, Finset.mem_singleton] at hh
  simp only [Finset.mem_insert]
  have hx := @hsub x
  aesop

private theorem star_contains_staircase {n : ℕ} (hn : 0 < n)
    (C : Finset (Nat.Partition n)) (X : YoungDiagram) (hsize : X.card = n - 1)
    (hsub : ∀ p ∈ C, X ≤ YoungDiagram.ofPartition p) : staircase (C.card - 1) ≤ X := by
  classical
  have hm (p : C) : ∃ c : ℕ × ℕ,
      (YoungDiagram.ofPartition p.val).cells \ X.cells = {c} := by
    apply Finset.card_eq_one.mp
    rw [Finset.card_sdiff_of_subset (hsub p.val p.property)]
    change (YoungDiagram.ofPartition p.val).card - X.card = 1
    rw [YoungDiagram.card_ofPartition, hsize]
    omega
  let f (p : C) := Classical.choose (hm p)
  have hf (p : C) : (YoungDiagram.ofPartition p.val).cells \ X.cells = {f p} :=
    Classical.choose_spec (hm p)
  have hnot (p : C) : f p ∉ X := by
    have hh : f p ∈ (YoungDiagram.ofPartition p.val).cells \ X.cells := by rw [hf]; simp
    exact (Finset.mem_sdiff.mp hh).2
  have hbelow (p : C) (x : ℕ × ℕ) (hx : x ≤ f p) (hne : x ≠ f p) : x ∈ X := by
    have hp : f p ∈ YoungDiagram.ofPartition p.val := by
      have hh : f p ∈ (YoungDiagram.ofPartition p.val).cells \ X.cells := by rw [hf]; simp
      exact (Finset.mem_sdiff.mp hh).1
    have hxP := (YoungDiagram.ofPartition p.val).isLowerSet hx hp
    by_contra hxX
    have hh := Finset.mem_sdiff.mpr ⟨hxP,hxX⟩
    rw [hf] at hh
    exact hne (Finset.mem_singleton.mp hh)
  have hinj : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply diagram_injective
    apply YoungDiagram.ext
    rw [single_extension_cells (hsub p.val p.property) (hf p),
      single_extension_cells (hsub q.val q.property) (hf q), he]
  let A := Finset.univ.image f
  have hAcard : A.card = C.card := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hanti : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ x ≤ y := by
    intro x hx y hy hne hle
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
    exact hnot p (hbelow q (f p) hle hne)
  have hb : ∀ c ∈ A, ∀ x : ℕ × ℕ, x ≤ c → x ≠ c → x ∈ X := by
    intro c hc x hx hne
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hc
    exact hbelow p x hx hne
  simpa only [hAcard] using antichain_staircase X A hanti hb

private theorem single_removal_cells {U d : YoungDiagram} {c : ℕ × ℕ}
    (hsub : d ≤ U) (hdiff : U.cells \ d.cells = {c}) : d.cells = U.cells.erase c := by
  ext x
  have hh := Finset.ext_iff.mp hdiff x
  simp only [Finset.mem_sdiff, Finset.mem_singleton] at hh
  simp only [Finset.mem_erase]
  have hx := @hsub x
  aesop

private theorem top_contains_staircase {n : ℕ}
    (C : Finset (Nat.Partition n)) (U : YoungDiagram) (hsize : U.card = n + 1)
    (hsub : ∀ p ∈ C, YoungDiagram.ofPartition p ≤ U) : staircase C.card ≤ U := by
  classical
  have hm (p : C) : ∃ c : ℕ × ℕ,
      U.cells \ (YoungDiagram.ofPartition p.val).cells = {c} := by
    apply Finset.card_eq_one.mp
    rw [Finset.card_sdiff_of_subset (hsub p.val p.property)]
    change U.card - (YoungDiagram.ofPartition p.val).card = 1
    rw [YoungDiagram.card_ofPartition, hsize]
    omega
  let f (p : C) := Classical.choose (hm p)
  have hf (p : C) : U.cells \ (YoungDiagram.ofPartition p.val).cells = {f p} :=
    Classical.choose_spec (hm p)
  have hmem (p : C) : f p ∈ U ∧ f p ∉ YoungDiagram.ofPartition p.val := by
    have hh : f p ∈ U.cells \ (YoungDiagram.ofPartition p.val).cells := by rw [hf]; simp
    exact Finset.mem_sdiff.mp hh
  have hinj : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply diagram_injective
    apply YoungDiagram.ext
    rw [single_removal_cells (hsub p.val p.property) (hf p),
      single_removal_cells (hsub q.val q.property) (hf q), he]
  let A := Finset.univ.image f
  have hAcard : A.card = C.card := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hanti : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ x ≤ y := by
    intro x hx y hy hne hle
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
    have hqp : f q ∈ YoungDiagram.ofPartition p.val := by
      change f q ∈ (YoungDiagram.ofPartition p.val).cells
      rw [single_removal_cells (hsub p.val p.property) (hf p)]
      exact Finset.mem_erase.mpr ⟨hne.symm,(hmem q).1⟩
    exact (hmem p).2 ((YoungDiagram.ofPartition p.val).isLowerSet hle hqp)
  have hb : ∀ c ∈ A, c ∈ U := by
    intro c hc
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hc
    exact (hmem p).1
  simpa only [hAcard] using maximal_antichain_staircase U A hanti hb

private theorem staircase_rowLen (r i : ℕ) : (staircase r).rowLen i = r - i := by
  have hm (j : ℕ) : j < (staircase r).rowLen i ↔ i + j < r := by
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    simp only [staircase, YoungDiagram.mem_mk, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    omega
  have h0 := hm 0
  have h1 := hm (staircase r).rowLen i
  have h2 := hm (r - i)
  omega

private theorem staircase_height (r : ℕ) : (staircase r).colLen 0 = r := by
  have hm (i : ℕ) : i < (staircase r).colLen 0 ↔ i < r := by
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen, staircase_rowLen]
    omega
  have h1 := hm (staircase r).colLen 0
  have h2 := hm r
  omega

private theorem triangular_step (r : ℕ) : triangular (r + 1) = triangular r + r + 1 := by
  unfold triangular
  have he : (r + 1) * (r + 1 + 1) = r * (r + 1) + 2 * (r + 1) := by ring
  omega

private theorem triangle_sum (r : ℕ) : (∑ i ∈ Finset.range r, r - i) = triangular r := by
  induction r with
  | zero => simp [triangular]
  | succ r ih =>
    rw [Finset.sum_range_succ]
    have he : (∑ i ∈ Finset.range r, r + 1 - i) =
        (∑ i ∈ Finset.range r, r - i) + r := by
      calc
        _ = ∑ i ∈ Finset.range r, (r - i + 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have := Finset.mem_range.mp hi
          omega
        _ = _ := by simp [Finset.sum_add_distrib]
    rw [he, ih]
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_left] using (triangular_step r).symm

private theorem staircase_card (r : ℕ) : (staircase r).card = triangular r := by
  calc
    _ = (staircase r).rowLens.sum := (YoungDiagram.sum_rowLens_eq_card _).symm
    _ = (∑ i ∈ Finset.range r, part ((staircase r).rowLen i)).sum :=
      congrArg Multiset.sum (row_parts (staircase r) r (by rw [staircase_height])).symm
    _ = ∑ i ∈ Finset.range r, (part ((staircase r).rowLen i)).sum := by
      exact map_sum Multiset.sumAddMonoidHom _ _
    _ = ∑ i ∈ Finset.range r, r - i := by simp only [part_sum, staircase_rowLen]
    _ = triangular r := triangle_sum r

private theorem triangular_mono : Monotone triangular := by
  intro r s hrs
  exact Nat.div_le_div_right (Nat.mul_le_mul hrs (Nat.add_le_add_right hrs 1))

private theorem triangular_ge (r : ℕ) : r ≤ triangular r := by
  induction r with
  | zero => simp [triangular]
  | succ r ih => rw [Nat.succ_eq_add_one, triangular_step]; omega

private theorem clique_bound {n : ℕ} (hn : 0 < n) (C : Finset (Nat.Partition n))
    (hC : (graph n).IsClique (C : Set (Nat.Partition n))) :
    triangular (C.card - 1) + 1 ≤ n := by
  by_cases hcard : 2 ≤ C.card
  · rcases clique_star_or_top hn C hC hcard with ⟨X,hX,hsub⟩ | ⟨U,hU,hsub⟩
    · have hh := Finset.card_le_card (star_contains_staircase hn C X hX hsub)
      change (staircase (C.card - 1)).card ≤ X.card at hh
      rw [staircase_card, hX] at hh
      omega
    · have hh := Finset.card_le_card (top_contains_staircase C U hU hsub)
      change (staircase C.card).card ≤ U.card at hh
      rw [staircase_card, hU] at hh
      have hs := triangular_step (C.card - 1)
      have he : C.card - 1 + 1 = C.card := by omega
      rw [he] at hs
      omega
  · have he : C.card - 1 = 0 := by omega
    simpa [he, triangular] using hn

private theorem local_realized {n : ℕ} (p : Nat.Partition n) :
    ∃ C : Finset (Nat.Partition n), (graph n).IsClique (C : Set (Nat.Partition n)) ∧
      p ∈ C ∧ localDimension p = C.card - 1 := by
  classical
  have hmem : {p} ∈ (cliques n).filter (p ∈ ·) := by simp [cliques]
  obtain ⟨C,hC,hEq⟩ := Finset.exists_mem_eq_sup _ ⟨{p},hmem⟩ (fun s => s.card - 1)
  have hC' := Finset.mem_filter.mp hC
  exact ⟨C, (Finset.mem_filter.mp hC'.1).2, hC'.2, hEq⟩

private theorem local_bound {n : ℕ} (hn : 0 < n) (p : Nat.Partition n) :
    triangular (localDimension p) + 1 ≤ n := by
  obtain ⟨C,hC,_,he⟩ := local_realized p
  rw [he]
  exact clique_bound hn C hC

private theorem maximum_realized (n : ℕ) :
    ∃ p : Nat.Partition n, maxDimension n = localDimension p := by
  obtain ⟨p,_,hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Nat.Partition n))
    (Finset.univ_nonempty) localDimension
  exact ⟨p,hp⟩

private theorem maximum_bound {n : ℕ} (hn : 0 < n) :
    triangular (maxDimension n) + 1 ≤ n := by
  obtain ⟨p,hp⟩ := maximum_realized n
  rw [hp]
  exact local_bound hn p

private def expandedStaircase (r e : ℕ) : YoungDiagram where
  cells := (staircase r).cells ∪ ({0} ×ˢ Finset.range (r + e))
  isLowerSet := by
    intro x y hxy hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.mem_union.mpr (Or.inl ((staircase r).isLowerSet hxy hy))
    · obtain ⟨hy0,hylen⟩ := Finset.mem_product.mp hy
      simp only [Finset.mem_singleton] at hy0
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_product.mpr
      constructor
      · simp only [Finset.mem_singleton]
        omega
      · apply Finset.mem_range.mpr
        have := Finset.mem_range.mp hylen
        omega

private theorem expanded_card (r e : ℕ) : (expandedStaircase r e).card = triangular r + e := by
  have hi : (staircase r).cells ∩ ({0} ×ˢ Finset.range (r + e)) =
      {0} ×ˢ Finset.range r := by
    ext ⟨i,j⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_range, staircase, YoungDiagram.mem_mk, Finset.mem_filter]
    omega
  have hc := Finset.card_inter_add_card_union (staircase r).cells
    ({0} ×ˢ Finset.range (r + e))
  rw [hi] at hc
  simp only [Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul] at hc
  change r + (expandedStaircase r e).card = (staircase r).card + (r + e) at hc
  rw [staircase_card] at hc
  omega

private def extensionCorner (r e : ℕ) (i : Fin (r + 1)) : ℕ × ℕ :=
  (i.val, if i.val = 0 then r + e else r - i.val)

private theorem corner_not_mem (r e : ℕ) (i : Fin (r + 1)) :
    extensionCorner r e i ∉ expandedStaircase r e := by
  simp only [expandedStaircase, YoungDiagram.mem_mk, Finset.mem_union, staircase,
    Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_singleton,
    extensionCorner]
  split_ifs <;> have := i.isLt <;> omega

private theorem corner_below (r e : ℕ) (i : Fin (r + 1)) (x : ℕ × ℕ)
    (hx : x ≤ extensionCorner r e i) (hne : x ≠ extensionCorner r e i) :
    x ∈ expandedStaircase r e := by
  rcases x with ⟨a,b⟩
  have hi := i.isLt
  simp only [extensionCorner, Prod.mk_le_mk] at hx
  by_cases hz : i.val = 0
  · apply Finset.mem_union.mpr
    right
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range]
    simp only [hz, ite_true] at hx
    simp only [extensionCorner, hz, ite_true, Prod.mk.injEq] at hne
    omega
  · apply Finset.mem_union.mpr
    left
    simp only [staircase, YoungDiagram.mem_mk, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    simp only [hz, ite_false] at hx
    simp only [extensionCorner, hz, ite_false, Prod.mk.injEq] at hne
    omega

private def cornerExtension (r e : ℕ) (i : Fin (r + 1)) : YoungDiagram where
  cells := insert (extensionCorner r e i) (expandedStaircase r e).cells
  isLowerSet := by
    intro x y hxy hy
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      by_cases he : x = extensionCorner r e i
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert.mpr (Or.inr (corner_below r e i x hxy he))
    · exact Finset.mem_insert.mpr (Or.inr ((expandedStaircase r e).isLowerSet hxy hy))

private theorem cornerExtension_card (r e : ℕ) (i : Fin (r + 1)) :
    (cornerExtension r e i).card = triangular r + e + 1 := by
  change (insert _ _).card = _
  rw [Finset.card_insert_of_notMem (corner_not_mem r e i)]
  exact congrArg (· + 1) (expanded_card r e)

private def cornerPartition (r e : ℕ) (i : Fin (r + 1)) :
    Nat.Partition (triangular r + e + 1) :=
  (cornerExtension r e i).toPartition (cornerExtension_card r e i)

private theorem cornerPartition_injective (r e : ℕ) : Function.Injective (cornerPartition r e) := by
  intro i j hij
  have hdiag := congrArg YoungDiagram.ofPartition hij
  simp only [cornerPartition, YoungDiagram.ofPartition_toPartition] at hdiag
  have hm : extensionCorner r e i ∈ cornerExtension r e j := by
    rw [← hdiag]
    exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hm with h | h
  · exact Fin.ext (congrArg Prod.fst h)
  · exact (corner_not_mem r e i h).elim

private theorem cornerPartitions_clique (r e : ℕ) :
    (graph (triangular r + e + 1)).IsClique
      ((Finset.univ.image (cornerPartition r e) : Finset _) : Set _) := by
  intro p hp q hq hpq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
  apply (transfer_iff_intersection (by omega) _ _).mpr
  simp only [cornerPartition, YoungDiagram.ofPartition_toPartition]
  have hne : extensionCorner r e i ≠ extensionCorner r e j := by
    intro he
    apply hpq
    congr 1
    exact Fin.ext (congrArg Prod.fst he)
  have he : ((cornerExtension r e i) ⊓ (cornerExtension r e j)).cells =
      (expandedStaircase r e).cells := by
    ext x
    simp only [YoungDiagram.cells_inf, cornerExtension, Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hi,hj⟩
      rcases hi with rfl | hi
      · rcases hj with hj | hj
        · exact (hne hj).elim
        · exact hj
      · exact hi
    · intro hx
      exact ⟨Or.inr hx,Or.inr hx⟩
  change _ = triangular r + e + 1 - 1
  change ((cornerExtension r e i) ⊓ (cornerExtension r e j)).cells.card = _
  rw [he]
  change (expandedStaircase r e).card = _
  rw [expanded_card]
  omega

private theorem exists_clique (r e : ℕ) :
    ∃ C : Finset (Nat.Partition (triangular r + e + 1)),
      (graph _).IsClique (C : Set _) ∧ C.card = r + 1 := by
  classical
  refine ⟨Finset.univ.image (cornerPartition r e), cornerPartitions_clique r e, ?_⟩
  rw [Finset.card_image_of_injective _ (cornerPartition_injective r e)]
  simp

private theorem clique_le_local {n : ℕ} (C : Finset (Nat.Partition n))
    (hC : (graph n).IsClique (C : Set _)) (p : Nat.Partition n) (hp : p ∈ C) :
    C.card - 1 ≤ localDimension p := by
  classical
  apply Finset.le_sup
  simp [cliques, hC, hp]

private theorem local_le_maximum {n : ℕ} (p : Nat.Partition n) :
    localDimension p ≤ maxDimension n := Finset.le_sup (Finset.mem_univ p)

private theorem lower_maximum (n r : ℕ) (hr : triangular r + 1 ≤ n) :
    r ≤ maxDimension n := by
  let e := n - (triangular r + 1)
  have he : triangular r + e + 1 = n := by omega
  have hh := exists_clique r e
  rw [he] at hh
  obtain ⟨C,hC,hcard⟩ := hh
  have hnon : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p,hp⟩ := hnon
  have hloc := clique_le_local C hC p hp
  have hmax := local_le_maximum p
  rw [hcard] at hloc
  omega

private theorem maximum_formula (n : ℕ) (hn : 0 < n) : maxDimension n =
    ((Finset.range (n + 1)).filter (fun r => triangular r + 1 ≤ n)).sup id := by
  apply le_antisymm
  · apply Finset.le_sup
    apply Finset.mem_filter.mpr
    have hh := maximum_bound hn
    have hl := triangular_ge (maxDimension n)
    exact ⟨Finset.mem_range.mpr (by omega),hh⟩
  · apply Finset.sup_le
    intro r hr
    exact lower_maximum n r (Finset.mem_filter.mp hr).2

private theorem maximum_at_threshold (r : ℕ) : maxDimension (triangular r + 1) = r := by
  have hlo := lower_maximum (triangular r + 1) r le_rfl
  have hhi := maximum_bound (by omega : 0 < triangular r + 1)
  apply le_antisymm _ hlo
  by_contra! hh
  have hm := triangular_mono (by omega : r + 1 ≤ maxDimension (triangular r + 1))
  rw [triangular_step] at hm
  omega

private theorem threshold_least (r : ℕ) :
    IsLeast {n : ℕ | 0 < n ∧ (layer r n).Nonempty} (triangular r + 1) := by
  constructor
  · refine ⟨by omega, ?_⟩
    obtain ⟨p,hp⟩ := maximum_realized (triangular r + 1)
    refine ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ p,?_⟩⟩
    have hh := maximum_at_threshold r
    omega
  · intro n hn
    obtain ⟨p,hp⟩ := hn.2
    have hh := local_bound hn.1 p
    have he := (Finset.mem_filter.mp hp).2
    rwa [he] at hh

private theorem threshold_value (r : ℕ) : threshold r = triangular r + 1 :=
  (threshold_least r).csInf_eq

private theorem threshold_solution : ThresholdClaim :=
  ⟨fun r => ⟨threshold_value r,threshold_least r⟩,maximum_formula⟩

private theorem expanded_zero (r : ℕ) : expandedStaircase r 0 = staircase r := by
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [expandedStaircase, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_range, Nat.add_zero, staircase, YoungDiagram.mem_mk, Finset.mem_filter]
  omega

private theorem family_eq_image (r : ℕ) : firstFamily r (triangular r + 1) =
    Finset.univ.image (cornerPartition r 0) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hsub,hdiff⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hdiff
    have hcm : c ∈ YoungDiagram.ofPartition p ∧ c ∉ staircase r := by
      apply Finset.mem_sdiff.mp
      rw [hc]
      simp
    have hb (x : ℕ × ℕ) (hx : x ≤ c) (hne : x ≠ c) : x ∈ staircase r := by
      have hxP := (YoungDiagram.ofPartition p).isLowerSet hx hcm.1
      by_contra hxS
      have hh := Finset.mem_sdiff.mpr ⟨hxP,hxS⟩
      rw [hc] at hh
      exact hne (Finset.mem_singleton.mp hh)
    have hlow : r ≤ c.1 + c.2 := by
      have hn := hcm.2
      simp only [staircase, YoungDiagram.mem_mk, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hn
      omega
    have hsum : c.1 + c.2 = r := by
      by_contra he
      have hgt : r < c.1 + c.2 := by omega
      by_cases hz : c.1 = 0
      · have hh := hb (0,c.2 - 1) (by constructor <;> omega) (by
          intro he'; have := congrArg Prod.snd he'; omega)
        have hh' := (Finset.mem_filter.mp hh).2
        omega
      · have hh := hb (c.1 - 1,c.2) (by constructor <;> omega) (by
          intro he'; have := congrArg Prod.fst he'; omega)
        have hh' := (Finset.mem_filter.mp hh).2
        omega
    let i : Fin (r + 1) := ⟨c.1,by omega⟩
    have hcorner : extensionCorner r 0 i = c := by
      apply Prod.ext
      · rfl
      · simp only [extensionCorner, i]
        split_ifs <;> omega
    have he : p = cornerPartition r 0 i := by
      apply diagram_injective
      simp only [cornerPartition, YoungDiagram.ofPartition_toPartition]
      apply YoungDiagram.ext
      rw [single_extension_cells hsub hc]
      change insert c (staircase r).cells = insert (extensionCorner r 0 i) _
      rw [hcorner, expanded_zero]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,he.symm⟩
  · intro hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · simp only [cornerPartition, YoungDiagram.ofPartition_toPartition, cornerExtension,
        expanded_zero]
      exact Finset.subset_insert _ _
    · have hn := corner_not_mem r 0 i
      rw [expanded_zero] at hn
      simp only [cornerPartition, YoungDiagram.ofPartition_toPartition, cornerExtension,
        expanded_zero]
      simp [hn]

private theorem family_card (r : ℕ) : (firstFamily r (triangular r + 1)).card = r + 1 := by
  rw [family_eq_image, Finset.card_image_of_injective _ (cornerPartition_injective r 0)]
  simp

private theorem family_clique (r : ℕ) : (graph (triangular r + 1)).IsClique
    ((firstFamily r (triangular r + 1) : Finset _) : Set _) := by
  rw [family_eq_image]
  exact cornerPartitions_clique r 0

private theorem first_layer_eq (r : ℕ) (hr : 2 ≤ r) :
    layer r (triangular r + 1) = firstFamily r (triangular r + 1) := by
  ext p
  constructor
  · intro hp
    have hlocal : localDimension p = r := (Finset.mem_filter.mp hp).2
    obtain ⟨C,hC,hpC,he⟩ := local_realized p
    have hcpos : 0 < C.card := Finset.card_pos.mpr ⟨p,hpC⟩
    have hcard : C.card = r + 1 := by omega
    rcases clique_star_or_top (by omega) C hC (by omega) with
      ⟨X,hX,hsub⟩ | ⟨U,hU,hsub⟩
    · have hstairs := star_contains_staircase (by omega) C X hX hsub
      have hcr : C.card - 1 = r := by omega
      rw [hcr] at hstairs
      have hEq : staircase r = X := by
        apply YoungDiagram.ext
        apply Finset.eq_of_subset_of_card_le hstairs
        change X.card ≤ (staircase r).card
        rw [staircase_card]
        omega
      have hpX := hsub p hpC
      rw [← hEq] at hpX
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,hpX,?_⟩
      rw [Finset.card_sdiff_of_subset hpX]
      change (YoungDiagram.ofPartition p).card - (staircase r).card = 1
      rw [YoungDiagram.card_ofPartition, staircase_card]
      omega
    · have hs := Finset.card_le_card (top_contains_staircase C U hU hsub)
      change (staircase C.card).card ≤ U.card at hs
      rw [staircase_card, hcard, triangular_step] at hs
      omega
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hlo := clique_le_local (firstFamily r (triangular r + 1)) (family_clique r) p hp
    rw [family_card] at hlo
    have hhi := local_le_maximum p
    rw [maximum_at_threshold] at hhi
    omega

private theorem first_occurrence_solution : FirstOccurrenceClaim := by
  intro r hr
  rw [threshold_value]
  exact ⟨first_layer_eq r hr, first_layer_eq r hr, family_card r⟩

/-- Both complete original questions, with the literal exact-layer threshold. -/
theorem result : ThresholdClaim ∧ FirstOccurrenceClaim :=
  ⟨threshold_solution, first_occurrence_solution⟩

end D5.S3.Combinatorics.Partitions.LyudogovskiySimplex
