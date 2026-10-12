/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowSeamCodes
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Combinatorics.Hall.Finite]
   utility: none
   digest: Binary label codes respect missed vertices and adjacent seam clauses. -/

import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes

open Finset

/-- A binary word is the finite set of its occupied coordinates. -/
abbrev Word (d : ℕ) := Finset (Fin d)

/-- The actual d-bit Boolean view of an occupied-coordinate word. -/
def wordBits {d : ℕ} (w : Word d) : Fin d → Bool := fun i => decide (i ∈ w)

private theorem wordBits_injective (d : ℕ) : Function.Injective (@wordBits d) := by
  intro a b eq
  ext i
  exact decide_eq_decide.mp (congrFun eq i)

/-- One owner at each missed coordinate, one extra first-bit owner, and one
owner at each later seam. The value of `pair` at coordinate zero is unused. -/
structure Clauses (d : ℕ) (Y : Type*) where
  unary : Fin d → Y
  extra : Y
  pair : Fin d → Y

variable {d : ℕ} {Y : Type*} [DecidableEq Y]

def first (hd : 0 < d) : Fin d := ⟨0, hd⟩
def prev (i : Fin d) : Fin d := ⟨i.val - 1, by omega⟩

/-- End coordinates of the adjacent occupied pairs in the word. -/
def pairEnds (w : Word d) : Finset (Fin d) :=
  w.filter (fun i => 0 < i.val ∧ prev i ∈ w)

/-- Exactly the labels whose clauses this word violates. Repetitions are
merged by finite-set union, never counted as separate labels. -/
def forbidden (C : Clauses d Y) (hd : 0 < d) (w : Word d) : Finset Y :=
  w.image C.unary ∪ (if first hd ∈ w then {C.extra} else ∅) ∪
    (pairEnds w).image C.pair

/-- The full list of words lawful for one label. -/
def codeList (C : Clauses d Y) (hd : 0 < d) (L : Y) : Finset (Word d) :=
  univ.filter (fun w => L ∉ forbidden C hd w)

/-- The labels with at least one displayed restriction. -/
def owners (C : Clauses d Y) (hd : 0 < d) : Finset Y :=
  univ.image C.unary ∪ {C.extra} ∪ ((univ.erase (first hd)).image C.pair)

private theorem pairEnds_small (w : Word d) (hw : w.card ≤ 2) :
    (pairEnds w).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiw, hip, hiPrev⟩ := mem_filter.mp hi
  obtain ⟨hjw, hjp, hjPrev⟩ := mem_filter.mp hj
  by_contra ne
  have nv : i.val ≠ j.val := fun h => ne (Fin.ext h)
  have impossible (a b : Fin d) (ha : a ∈ w) (hb : b ∈ w)
      (hap : 0 < a.val) (hprev : prev a ∈ w) (hlt : a.val < b.val) : False := by
    have pa : prev a ≠ a := by intro h; have := congrArg Fin.val h; simp [prev] at this; omega
    have pb : prev a ≠ b := by intro h; have := congrArg Fin.val h; simp [prev] at this; omega
    have ab : a ≠ b := by intro h; subst b; omega
    have sub : {prev a, a, b} ⊆ w := by
      simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hprev, ha, hb⟩
    have count : ({prev a, a, b} : Finset (Fin d)).card = 3 := by simp [pa, pb, ab]
    have := card_le_card sub
    omega
  rcases lt_or_gt_of_ne nv with hlt | hlt
  · exact impossible i j hiw hjw hip hiPrev hlt
  · exact impossible j i hjw hiw hjp hjPrev hlt

private theorem pairEnds_singleton (i : Fin d) : pairEnds ({i} : Word d) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hjw, hp, hprev⟩ := mem_filter.mp hj
  simp only [mem_singleton] at hjw hprev
  subst j
  have := congrArg Fin.val hprev
  simp [prev] at this
  omega

private theorem forbidden_unit (C : Clauses d Y) (hd : 0 < d) (i : Fin d) :
    (forbidden C hd {i}).card ≤ 2 := by
  simp only [forbidden, pairEnds_singleton, image_empty, union_empty, image_singleton]
  split_ifs
  · exact card_le_two
  · simp

private theorem forbidden_later_unit (C : Clauses d Y) (hd : 0 < d) (i : Fin d)
    (hi : i ≠ first hd) : (forbidden C hd {i}).card ≤ 1 := by
  simp [forbidden, pairEnds_singleton, Ne.symm hi]

private theorem forbidden_two (C : Clauses d Y) (hd : 0 < d) (w : Word d)
    (hw : w.card ≤ 2) : (forbidden C hd w).card ≤ 4 := by
  have hpair := (card_image_le (f := C.pair)).trans (pairEnds_small w hw)
  have hu := (card_image_le (f := C.unary)).trans hw
  have he : (if first hd ∈ w then ({C.extra} : Finset Y) else ∅).card ≤ 1 := by
    split_ifs <;> simp
  have h := (card_union_le (w.image C.unary ∪
    (if first hd ∈ w then {C.extra} else ∅)) ((pairEnds w).image C.pair)).trans
    (Nat.add_le_add (card_union_le _ _) le_rfl)
  unfold forbidden
  omega

private theorem owners_bound (C : Clauses d Y) (hd : 0 < d) :
    (owners C hd).card ≤ 2 * d := by
  have hu : (univ.image C.unary).card ≤ d := by simpa using card_image_le (s := univ) (f := C.unary)
  have hp : ((univ.erase (first hd)).image C.pair).card ≤ d - 1 := by
    simpa using (card_image_le (s := univ.erase (first hd)) (f := C.pair))
  have h := (card_union_le (univ.image C.unary ∪ {C.extra})
    ((univ.erase (first hd)).image C.pair)).trans
    (Nat.add_le_add (card_union_le _ _) le_rfl)
  unfold owners
  simp only [card_singleton] at h
  omega

private theorem forbidden_subset_owners (C : Clauses d Y) (hd : 0 < d) (w : Word d) :
    forbidden C hd w ⊆ owners C hd := by
  intro L hL
  simp only [forbidden, owners, mem_union, mem_image, mem_singleton, mem_erase, mem_univ,
    true_and] at hL ⊢
  rcases hL with (⟨i, hi, rfl⟩ | hx) | ⟨i, hi, rfl⟩
  · exact Or.inl (Or.inl ⟨i, rfl⟩)
  · exact Or.inl (Or.inr (by split_ifs at hx <;> simp_all))
  · right
    refine ⟨i, ?_, rfl⟩
    have hp := (mem_filter.mp hi).2.1
    refine ⟨?_, trivial⟩
    intro h; have := congrArg Fin.val h; simp [first] at this; omega

private theorem word_in_union (C : Clauses d Y) (hd : 0 < d) (S : Finset Y)
    (w : Word d) (h : (forbidden C hd w).card < S.card) :
    w ∈ S.biUnion (codeList C hd) := by
  obtain ⟨L, hL, good⟩ := exists_mem_notMem_of_card_lt_card h
  exact mem_biUnion.mpr ⟨L, hL, by simpa [codeList] using good⟩

private theorem zero_in_union (C : Clauses d Y) (hd : 0 < d) (S : Finset Y)
    (hS : S.Nonempty) : (∅ : Word d) ∈ S.biUnion (codeList C hd) := by
  obtain ⟨L, hL⟩ := hS
  exact mem_biUnion.mpr ⟨L, hL, by simp [codeList, forbidden, pairEnds]⟩


private theorem cube_union (C : Clauses d Y) (hd : 0 < d) (S : Finset Y)
    (L : Y) (hL : L ∈ S) (free : L ∉ owners C hd) :
    S.biUnion (codeList C hd) = univ := by
  apply eq_univ_of_forall
  intro w
  refine mem_biUnion.mpr ⟨L, hL, ?_⟩
  simp only [codeList, mem_filter, mem_univ, true_and]
  exact fun h => free (forbidden_subset_owners C hd w h)

private def ballOne (d : ℕ) : Finset (Word d) :=
  (univ : Finset (Fin d)).powersetCard 0 ∪ univ.powersetCard 1

private def ballTwo (d : ℕ) : Finset (Word d) :=
  ballOne d ∪ (univ : Finset (Fin d)).powersetCard 2

private theorem ballOne_card (d : ℕ) : (ballOne d).card = 1 + d := by
  rw [ballOne, card_union_of_disjoint (pairwise_disjoint_powersetCard univ (by decide : 0 ≠ 1))]
  simp [card_powersetCard]

private theorem ballTwo_card (d : ℕ) : (ballTwo d).card = 1 + d + d.choose 2 := by
  have disj : Disjoint (ballOne d) ((univ : Finset (Fin d)).powersetCard 2) := by
    apply disjoint_union_left.mpr
    exact ⟨pairwise_disjoint_powersetCard univ (by decide : 0 ≠ 2),
      pairwise_disjoint_powersetCard univ (by decide : 1 ≠ 2)⟩
  rw [ballTwo, card_union_of_disjoint disj, ballOne_card, card_powersetCard]
  simp

private theorem ballOne_subset (C : Clauses d Y) (hd : 0 < d) (S : Finset Y)
    (hS : 3 ≤ S.card) : ballOne d ⊆ S.biUnion (codeList C hd) := by
  intro w hw
  rcases mem_union.mp hw with hw | hw
  · have hz := (mem_powersetCard.mp hw).2
    have : w = ∅ := card_eq_zero.mp hz
    subst w
    exact zero_in_union C hd S (card_pos.mp (by omega))
  · obtain ⟨i, rfl⟩ := card_eq_one.mp (mem_powersetCard.mp hw).2
    exact word_in_union C hd S {i} (by have := forbidden_unit C hd i; omega)

private theorem ballTwo_subset (C : Clauses d Y) (hd : 0 < d) (S : Finset Y)
    (hS : 5 ≤ S.card) : ballTwo d ⊆ S.biUnion (codeList C hd) := by
  intro w hw
  rcases mem_union.mp hw with hw | hw
  · exact ballOne_subset C hd S (by omega) hw
  · exact word_in_union C hd S w (by
      have := forbidden_two C hd w (by have := (mem_powersetCard.mp hw).2; omega)
      omega)

private theorem two_lists_bound (C : Clauses d Y) (hd : 0 < d) (S : Finset Y)
    (hS : S.card = 2) : d ≤ (S.biUnion (codeList C hd)).card := by
  let units : Finset (Word d) := (univ.erase (first hd)).image singleton
  have sub : insert ∅ units ⊆ S.biUnion (codeList C hd) := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact zero_in_union C hd S (card_pos.mp (by omega))
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hw
      exact word_in_union C hd S {i} (by
        have := forbidden_later_unit C hd i (mem_erase.mp hi).1
        omega)
  have noZero : (∅ : Word d) ∉ units := by simp [units]
  have count : (insert ∅ units).card = d := by
    rw [card_insert_of_notMem noZero]
    dsimp [units]
    rw [card_image_of_injective _ singleton_injective]
    simp
    omega
  have h := card_le_card sub
  rw [count] at h
  exact h

private theorem weight_two_capacity (d : ℕ) (hd : 3 ≤ d) :
    2 * d ≤ 1 + d + d.choose 2 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hd
  induction a with
  | zero => decide
  | succ a ih =>
      rw [show 3 + (a + 1) = (3 + a) + 1 by omega, Nat.choose_succ_succ']
      simp only [Nat.choose_one_right]
      omega

/-- All subfamily inequalities for the actual unary/adjacent clause pattern.
The two-dimensional four-owner case is deliberately excluded here. -/
theorem list_union_inequalities [Fintype Y] (C : Clauses d Y) (hd : 2 ≤ d)
    (capacity : Fintype.card Y ≤ 2 ^ d)
    (regular : 3 ≤ d ∨ (owners C (by omega)).card ≤ 3 ∨ Fintype.card Y ≤ 3)
    (S : Finset Y) : S.card ≤ (S.biUnion (codeList C (by omega))).card := by
  by_cases free : ∃ L ∈ S, L ∉ owners C (by omega)
  · obtain ⟨L, hL, hfree⟩ := free
    rw [cube_union C (by omega) S L hL hfree]
    simpa using (card_le_univ S).trans capacity
  · have sub : S ⊆ owners C (by omega) := by
      intro L hL
      by_contra hn
      exact free ⟨L, hL, hn⟩
    have bound := (card_le_card sub).trans (owners_bound C (by omega))
    by_cases empty : S.card = 0
    · omega
    by_cases one : S.card = 1
    · have nz := zero_in_union C (by omega) S (card_pos.mp (by omega))
      have := card_pos.mpr ⟨∅, nz⟩
      omega
    by_cases two : S.card = 2
    · exact two ▸ hd.trans (two_lists_bound C (by omega) S two)
    have three : 3 ≤ S.card := by omega
    by_cases small : S.card ≤ d + 1
    · have count := card_le_card (ballOne_subset C (by omega) S three)
      rw [ballOne_card] at count
      omega
    · have high : 3 ≤ d := by
        rcases regular with h | h | h
        · exact h
        · have := (card_le_card sub).trans h; omega
        · have := (card_le_univ S).trans h; omega
      have count := card_le_card (ballTwo_subset C (by omega) S (by omega))
      rw [ballTwo_card] at count
      exact bound.trans ((weight_two_capacity d high).trans count)


/-- The four clause owners, in the source order A,B,C,D. -/
def fourOwners (C : Clauses 2 Y) : Fin 4 → Y :=
  ![C.unary 0, C.extra, C.unary 1, C.pair 1]

/-- The explicit alternative is 00,01,10,11, in coordinate order one,two. -/
def fourWords : Fin 4 → Word 2 := ![∅, {1}, {0}, {0, 1}]

private theorem owners_two (C : Clauses 2 Y) :
    owners C (by decide) = univ.image (fourOwners C) := by
  ext L
  simp [owners, first, fourOwners, Fin.univ_succ, image_insert, image_singleton,
    or_left_comm]

private theorem exceptional_choice [Fintype Y] (C : Clauses 2 Y)
    (capacity : Fintype.card Y ≤ 4) (hfour : 4 ≤ (owners C (by decide)).card) :
    Fintype.card Y = 4 ∧ Function.Injective (fourOwners C) ∧
    ∃ c : Y → Word 2, Function.Injective c ∧
      (∀ i : Fin 4, c (fourOwners C i) = fourWords i) ∧
      (∀ i : Fin 2, i ∉ c (C.unary i)) ∧ 0 ∉ c C.extra ∧
      (0 ∈ c (C.pair 1) ∧ 1 ∈ c (C.pair 1)) := by
  have hcard : (owners C (by decide)).card = 4 := by
    have := (card_le_univ (owners C (by decide))).trans capacity
    omega
  have total : Fintype.card Y = 4 := by
    have := card_le_univ (owners C (by decide)); omega
  have inj : Function.Injective (fourOwners C) := by
    have h : (univ.image (fourOwners C)).card = (univ : Finset (Fin 4)).card := by
      rw [← owners_two, hcard]; simp
    intro a b hab
    exact (card_image_iff.mp h) (mem_univ a) (mem_univ b) hab
  have surj : Function.Surjective (fourOwners C) := by
    have all : univ.image (fourOwners C) = univ := by
      apply eq_univ_of_card
      rw [← owners_two, hcard, total]
    intro L
    have := all.symm ▸ mem_univ L
    obtain ⟨i, _, hi⟩ := mem_image.mp this
    exact ⟨i, hi⟩
  let e := Equiv.ofBijective (fourOwners C) ⟨inj, surj⟩
  let c : Y → Word 2 := fun L => fourWords (e.symm L)
  have code (i : Fin 4) : c (fourOwners C i) = fourWords i := by
    change fourWords (e.symm (e i)) = fourWords i
    rw [e.symm_apply_apply]
  refine ⟨total, inj, c, ?_, code, ?_, ?_, ?_⟩
  · exact (by decide : Function.Injective fourWords).comp e.symm.injective
  · intro i; fin_cases i
    · have h := code 0; change c (C.unary 0) = ∅ at h; simp [h]
    · have h := code 2; change c (C.unary 1) = {0} at h; simp [h]
  · have h := code 1; change c C.extra = {1} at h; simp [h]
  · have h := code 3; change c (C.pair 1) = {0, 1} at h; simp [h]

/-- Unary restrictions always hold; the last alternative relaxes precisely
the sole adjacent-pair owner in dimension two. -/
def Selection [Fintype Y] (C : Clauses d Y) (hd : 0 < d) (c : Y → Word d) : Prop :=
  (∀ L, c L ∈ codeList C hd L) ∨
  (∃ h : d = 2, let C2 : Clauses 2 Y := h ▸ C
    let c2 : Y → Word 2 := h ▸ c
    Fintype.card Y = 4 ∧ Function.Injective (fourOwners C2) ∧
    (∀ i : Fin 4, c2 (fourOwners C2 i) = fourWords i) ∧
    (∀ i : Fin 2, i ∉ c2 (C2.unary i)) ∧ 0 ∉ c2 C2.extra ∧
    (0 ∈ c2 (C2.pair 1) ∧ 1 ∈ c2 (C2.pair 1)))

private theorem choose_codes [Fintype Y] (C : Clauses d Y) (hd : 2 ≤ d)
    (capacity : Fintype.card Y ≤ 2 ^ d) :
    ∃ c : Y → Word d, Function.Injective c ∧ Selection C (by omega) c := by
  by_cases regular : 3 ≤ d ∨ (owners C (by omega)).card ≤ 3 ∨ Fintype.card Y ≤ 3
  · obtain ⟨c, inj, lawful⟩ :=
      (all_card_le_biUnion_card_iff_existsInjective' (codeList C (by omega))).mp
        (list_union_inequalities C hd capacity regular)
    exact ⟨c, inj, Or.inl lawful⟩
  · have d2 : d = 2 := by omega
    subst d
    obtain ⟨total, distinct, c, inj, codes, unary, extra, pair⟩ :=
      exceptional_choice C (by simpa using capacity) (by omega)
    exact ⟨c, inj, Or.inr ⟨rfl, total, distinct, codes, unary, extra, pair⟩⟩

/-- All labels of the actual rotated full positive window, including labels
that own no restriction. -/
def labels {m : ℕ} (table : Fin (m + 1) → Y) : Finset Y := univ.image table

abbrev Label {m : ℕ} (table : Fin (m + 1) → Y) := ↥(labels table)

/-- Coordinate i represents source coordinate r=i+1, whose missed vertex
is m+1-2r in the actual window. -/
def missedVertex (m d : ℕ) (fit : 2 * d ≤ m + 1) (i : Fin d) : Fin (m + 1) :=
  ⟨m + 1 - 2 * (i.val + 1), by have := i.isLt; omega⟩

/-- The common boundary vertex is s_r=m+2-2r. At i=0 this is m;
only i>0 contributes an adjacent-pair restriction. -/
def seamVertex (m d : ℕ) (fit : 2 * d ≤ m + 1) (i : Fin d) : Fin (m + 1) :=
  ⟨m + 2 - 2 * (i.val + 1), by have := i.isLt; omega⟩

def tableLabel {m : ℕ} (table : Fin (m + 1) → Y) (v : Fin (m + 1)) :
    Label table := ⟨table v, mem_image.mpr ⟨v, mem_univ v, rfl⟩⟩

/-- Pull the clauses from the original vertex table, without an assumed code
table, injective choice or seam-feasibility hypothesis. -/
def sourceClauses {m : ℕ} (table : Fin (m + 1) → Y) (d : ℕ)
    (fit : 2 * d ≤ m + 1) : Clauses d (Label table) where
  unary i := tableLabel table (missedVertex m d fit i)
  extra := tableLabel table ⟨m, by omega⟩
  pair i := tableLabel table (seamVertex m d fit i)

private theorem source_capacity {m : ℕ} (table : Fin (m + 1) → Y)
    (hn : 3 ≤ (labels table).card) (hm : Odd m) :
    let d := Nat.clog 2 (labels table).card
    2 ≤ d ∧ 2 * d ≤ m + 1 ∧ (labels table).card ≤ 2 ^ d := by
  dsimp only
  have cap := Nat.le_pow_clog (by decide : 1 < 2) (labels table).card
  have low : 2 ≤ Nat.clog 2 (labels table).card := by
    have : 1 < Nat.clog 2 (labels table).card :=
      (Nat.lt_clog_iff_pow_lt (by decide)).mpr
        (by simpa using (show 2 < (labels table).card by omega))
    omega
  have tableBound : (labels table).card ≤ m + 1 := by
    simpa [labels] using card_image_le (s := univ) (f := table)
  obtain ⟨a, ha⟩ := hm
  have powBound : 2 * (a + 1) ≤ 2 ^ (a + 1) := by
    have bound : a + 1 ≤ 2 ^ a := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := a))
    rw [pow_succ]
    omega
  have arithmetic : m + 1 = 2 * (a + 1) := by omega
  have half : Nat.clog 2 (labels table).card ≤ a + 1 :=
    Nat.clog_le_of_le_pow (tableBound.trans (by
      calc m + 1 = 2 * (a + 1) := arithmetic
           _ ≤ 2 ^ (a + 1) := powBound))
  refine ⟨low, ?_, cap⟩
  calc 2 * Nat.clog 2 (labels table).card ≤ 2 * (a + 1) := Nat.mul_le_mul_left 2 half
       _ = m + 1 := arithmetic.symm



/-- Exact clause semantics: an occupied coordinate is bit one. -/
theorem mem_codeList_iff (C : Clauses d Y) (hd : 0 < d) (L : Y) (w : Word d) :
    w ∈ codeList C hd L ↔
    (∀ i : Fin d, C.unary i = L → i ∉ w) ∧
    (C.extra = L → first hd ∉ w) ∧
    (∀ i : Fin d, 0 < i.val → C.pair i = L → i ∉ w ∨ prev i ∉ w) := by
  simp only [codeList, mem_filter, mem_univ, true_and, forbidden, mem_union,
    not_or, mem_image, not_exists, not_and, pairEnds, mem_filter]
  constructor
  · rintro ⟨⟨hu, he⟩, hp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i eq hi; exact hu i hi eq
    · intro eq hi; rw [if_pos hi, mem_singleton] at he; exact he eq.symm
    · intro i hi eq
      by_cases hw : i ∈ w
      · right; intro hprev; exact hp i ⟨hw, hi, hprev⟩ eq
      · exact Or.inl hw
  · rintro ⟨hu, he, hp⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi eq; exact hu i eq hi
    · split_ifs with hi
      · simp only [mem_singleton]; exact fun eq => he eq.symm hi
      · simp
    · intro i hi eq
      exact (hp i hi.2.1 eq).elim (fun h => h hi.1) (fun h => h hi.2.2)

private theorem selected_unary [Fintype Y] (C : Clauses d Y) (hd : 0 < d)
    (c : Y → Word d) (selected : Selection C hd c) :
    (∀ i, i ∉ c (C.unary i)) ∧ first hd ∉ c C.extra := by
  rcases selected with regular | ⟨h, total, distinct, codes, unary, extra, pair⟩
  · exact ⟨fun i => ((mem_codeList_iff C hd _ _).mp (regular (C.unary i))).1 i rfl,
      ((mem_codeList_iff C hd _ _).mp (regular C.extra)).2.1 rfl⟩
  · subst d
    exact ⟨unary, extra⟩

/-- The actual ordered window starts at issued index r times m and contains
its m+1 path vertices, reduced modulo the original period m+2. -/
def sourceWindow (m r : ℕ) : Finset (ZMod (m + 2)) :=
  univ.image (fun h : Fin (m + 1) => (r * m : ℕ) + (h.val : ZMod (m + 2)))

private theorem translated_window (m : ℕ) (start j : ZMod (m + 2)) :
    j ∈ (univ.image (fun h : Fin (m + 1) => start + (h.val : ZMod (m + 2)))) ↔
    j ≠ start - 1 := by
  constructor
  · rintro hj eq
    obtain ⟨h, _, heq⟩ := mem_image.mp hj
    have off : (h.val : ZMod (m + 2)) = -1 := by rw [eq] at heq; linear_combination heq
    have hv := congrArg ZMod.val off
    rw [ZMod.val_natCast_of_lt (by have := h.isLt; omega), ZMod.val_neg_one] at hv
    have := h.isLt; omega
  · intro hj
    let off := j - start
    have bound : off.val < m + 1 := by
      have hv := ZMod.val_lt off
      by_contra hn
      have eq : off.val = m + 1 := by omega
      have eqoff : off = -1 := by
        rw [← ZMod.natCast_zmod_val off, eq]
        simpa only [ZMod.val_neg_one] using
          (ZMod.natCast_zmod_val (-1 : ZMod (m + 2)))
      apply hj
      dsimp [off] at eqoff
      linear_combination eqoff
    refine mem_image.mpr ⟨⟨off.val, bound⟩, mem_univ _, ?_⟩
    rw [ZMod.natCast_zmod_val]
    dsimp [off]; ring

/-- The source formulas identify the sole missed vertex, the donor outside
the child, and the common vertex at each later boundary. -/
theorem source_window_vertices (m d : ℕ) (fit : 2 * d ≤ m + 1) (i : Fin d) :
    (∀ j : ZMod (m + 2), j ∈ sourceWindow m (i.val + 1) ↔
      j ≠ ((missedVertex m d fit i).val : ZMod (m + 2))) ∧
    ((m + 1 : ℕ) : ZMod (m + 2)) ∈ sourceWindow m (i.val + 1) ∧
    (((i.val + 1) * m : ℕ) : ZMod (m + 2)) =
      ((seamVertex m d fit i).val : ZMod (m + 2)) ∧
    (((i.val * m + m : ℕ) : ZMod (m + 2))) =
      ((seamVertex m d fit i).val : ZMod (m + 2)) := by
  have twice : 2 * (i.val + 1) ≤ m + 1 := by have := i.isLt; omega
  have start : (((i.val + 1) * m : ℕ) : ZMod (m + 2)) =
      ((seamVertex m d fit i).val : ZMod (m + 2)) := by
    have hs : (seamVertex m d fit i).val + 2 * (i.val + 1) = m + 2 := by
      simp only [seamVertex]; omega
    have hz : ((m + 2 : ℕ) : ZMod (m + 2)) = 0 := by simp
    have cast := congrArg (fun n : ℕ => (n : ZMod (m + 2))) hs
    push_cast at cast hz ⊢
    linear_combination (i.val : ZMod (m + 2)) * hz - cast
  have edge : ((seamVertex m d fit i).val : ZMod (m + 2)) - 1 =
      ((missedVertex m d fit i).val : ZMod (m + 2)) := by
    have h : (missedVertex m d fit i).val + 1 = (seamVertex m d fit i).val := by
      simp only [missedVertex, seamVertex]; omega
    have cast := congrArg (fun n : ℕ => (n : ZMod (m + 2))) h
    push_cast at cast
    linear_combination -cast
  have rows : ∀ j : ZMod (m + 2), j ∈ sourceWindow m (i.val + 1) ↔
      j ≠ ((missedVertex m d fit i).val : ZMod (m + 2)) := by
    intro j
    rw [sourceWindow, translated_window, start, edge]
  refine ⟨rows, (rows _).mpr ?_, start, ?_⟩
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by
      have := (missedVertex m d fit i).isLt; omega)] at hv
    simp only [missedVertex] at hv
    omega
  · convert start using 1
    push_cast
    ring


/-- The simultaneous code selection on every label of the original table.
The minimal binary capacity supplies d>=2 and all valid vertex indices.
The exceptional branch preserves all unary conditions but violates the
sole pair clause with the explicit 11 word. No physical decoder is asserted. -/
theorem actual_table_codes {m : ℕ} (table : Fin (m + 1) → Y)
    (hm : Odd m) (hn : 3 ≤ (labels table).card) :
    let d := Nat.clog 2 (labels table).card
    ∃ (fit : 2 * d ≤ m + 1) (hd : 2 ≤ d) (c : Label table → Word d),
      Function.Injective c ∧ Function.Injective (fun L => wordBits (c L)) ∧
      Selection (sourceClauses table d fit) (by omega) c ∧
      (∀ i : Fin d, i ∉ c ((sourceClauses table d fit).unary i)) ∧
      first (by omega) ∉ c (sourceClauses table d fit).extra ∧
      (∀ i : Fin d, ∀ j : ZMod (m + 2),
        j ∈ sourceWindow m (i.val + 1) ↔
        j ≠ ((missedVertex m d fit i).val : ZMod (m + 2))) ∧
      (∀ i : Fin d, ((m + 1 : ℕ) : ZMod (m + 2)) ∈ sourceWindow m (i.val + 1)) ∧
      (∀ i : Fin d, (((i.val + 1) * m : ℕ) : ZMod (m + 2)) =
        ((seamVertex m d fit i).val : ZMod (m + 2))) ∧
      (∀ i : Fin d, ((i.val * m + m : ℕ) : ZMod (m + 2)) =
        ((seamVertex m d fit i).val : ZMod (m + 2))) := by
  dsimp only
  obtain ⟨hd, fit, capacity⟩ := source_capacity table hn hm
  let C := sourceClauses table (Nat.clog 2 (labels table).card) fit
  have cap : Fintype.card (Label table) ≤ 2 ^ Nat.clog 2 (labels table).card := by
    simpa only [Fintype.card_coe] using capacity
  obtain ⟨c, inj, selected⟩ := choose_codes C hd cap
  obtain ⟨unary, extra⟩ := selected_unary C (by omega) c selected
  refine ⟨fit, hd, c, inj, (wordBits_injective _).comp inj,
    selected, unary, extra, ?_, ?_, ?_, ?_⟩
  · intro i; exact (source_window_vertices m _ fit i).1
  · intro i; exact (source_window_vertices m _ fit i).2.1
  · intro i; exact (source_window_vertices m _ fit i).2.2.1
  · intro i; exact (source_window_vertices m _ fit i).2.2.2

#print axioms list_union_inequalities
#print axioms mem_codeList_iff
#print axioms source_window_vertices
#print axioms actual_table_codes

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.WindowSeamCodes
