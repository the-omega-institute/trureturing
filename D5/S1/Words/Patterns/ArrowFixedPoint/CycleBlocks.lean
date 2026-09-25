/- GID: D5/S1/Words/Patterns/ArrowFixedPoint/CycleBlocks
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/ArrowFixedPoint/CycleBlocks
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Singleton-complete standard cycle blocks and record-maximum cuts. -/

import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic

/-!
# Singleton-complete standard cycle blocks

The labels are zero-based `Fin n` values; adding one recovers the paper's
labels.  `recordCuts` cuts immediately before every new left-to-right maximum.
Each resulting block is decoded separately with `List.formPerm`; flattening the
blocks and applying `formPerm` once would instead make one cycle.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ArrowFixedPoint

open Equiv Equiv.Perm

noncomputable section

/-- Accumulator for cuts immediately before new left-to-right maxima.  The
current block is stored in reverse order. -/
private def recordCutsAux {α : Type*} [LinearOrder α] :
    α → List α → List α → List (List α)
  | _, current, [] => [current.reverse]
  | maximum, current, x :: xs =>
      if maximum < x then
        current.reverse :: recordCutsAux x [x] xs
      else
        recordCutsAux maximum (x :: current) xs

/-- Split a word immediately before each left-to-right maximum. -/
def recordCuts {α : Type*} [LinearOrder α] : List α → List (List α)
  | [] => []
  | x :: xs => recordCutsAux x [x] xs

private lemma flatten_recordCutsAux {α : Type*} [LinearOrder α]
    (maximum : α) (current rest : List α) :
    (recordCutsAux maximum current rest).flatten = current.reverse ++ rest := by
  induction rest generalizing maximum current with
  | nil => simp [recordCutsAux]
  | cons x xs ih =>
      simp only [recordCutsAux]
      split_ifs with h
      · rw [List.flatten_cons, ih]
        simp
      · rw [ih]
        simp

@[simp] theorem flatten_recordCuts {α : Type*} [LinearOrder α] (word : List α) :
    (recordCuts word).flatten = word := by
  cases word with
  | nil => rfl
  | cons x xs => simpa [recordCuts] using flatten_recordCutsAux x [x] xs

private lemma nil_not_mem_recordCutsAux {α : Type*} [LinearOrder α]
    (maximum : α) (current rest : List α) (hcurrent : current ≠ []) :
    [] ∉ recordCutsAux maximum current rest := by
  induction rest generalizing maximum current with
  | nil => simp [recordCutsAux, hcurrent]
  | cons x xs ih =>
      simp only [recordCutsAux]
      split_ifs
      · simp [hcurrent, ih x [x] (by simp)]
      · exact ih maximum (x :: current) (by simp)

theorem nil_not_mem_recordCuts {α : Type*} [LinearOrder α] (word : List α) :
    [] ∉ recordCuts word := by
  cases word with
  | nil => simp [recordCuts]
  | cons x xs => exact nil_not_mem_recordCutsAux x [x] xs (by simp)

/-- The orbit of `x`, including singleton fixed-point orbits. -/
def orbit {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (p.SameCycle x)

/-- The largest label in the complete orbit of `x`. -/
def orbitMaximum {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Fin n) : Fin n :=
  (orbit p x).max' ⟨x, by simp [orbit, Equiv.Perm.SameCycle.rfl]⟩

private lemma orbit_eq_of_sameCycle {n : ℕ} (p : Equiv.Perm (Fin n))
    {x y : Fin n} (h : p.SameCycle x y) : orbit p x = orbit p y := by
  ext z
  simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

lemma orbitMaximum_eq_of_sameCycle {n : ℕ} (p : Equiv.Perm (Fin n))
    {x y : Fin n} (h : p.SameCycle x y) : orbitMaximum p x = orbitMaximum p y := by
  simp only [orbitMaximum, orbit_eq_of_sameCycle p h]

/-- One singleton-complete standard cycle, based at its orbit maximum. -/
def standardBlock {n : ℕ} (p : Equiv.Perm (Fin n)) (m : Fin n) : List (Fin n) :=
  if p m = m then [m] else p.toList m

/-- Orbit maxima, in increasing order. -/
def orbitMaxima {n : ℕ} (p : Equiv.Perm (Fin n)) : List (Fin n) :=
  (Finset.univ.filter fun m => orbitMaximum p m = m).sort (· ≤ ·)

/-- Complete standard cycle blocks: maxima first and maxima increasing. -/
def standardCycleBlocks {n : ℕ} (p : Equiv.Perm (Fin n)) : List (List (Fin n)) :=
  (orbitMaxima p).map (standardBlock p)

/-- The literal cycle-erasure word. -/
def standardCycleWord {n : ℕ} (p : Equiv.Perm (Fin n)) : List (Fin n) :=
  (standardCycleBlocks p).flatten

private lemma mem_standardBlock_iff {n : ℕ} (p : Equiv.Perm (Fin n))
    {m x : Fin n} (_hm : orbitMaximum p m = m) :
    x ∈ standardBlock p m ↔ p.SameCycle m x := by
  by_cases hfix : p m = m
  · simp only [standardBlock, hfix, if_pos, List.mem_singleton]
    exact ⟨fun h => h ▸ Equiv.Perm.SameCycle.rfl,
      fun h => (h.eq_of_left hfix).symm⟩
  · rw [standardBlock, if_neg hfix, Equiv.Perm.mem_toList_iff]
    exact and_iff_left (Equiv.Perm.mem_support.mpr hfix)

private lemma standardBlock_head_max {n : ℕ} (p : Equiv.Perm (Fin n))
    {m : Fin n} (hm : orbitMaximum p m = m) :
    ∃ tail, standardBlock p m = m :: tail ∧ ∀ x ∈ tail, x < m := by
  by_cases hfix : p m = m
  · exact ⟨[], by simp [standardBlock, hfix], by simp⟩
  · have hsupp : m ∈ p.support := Equiv.Perm.mem_support.mpr hfix
    have hne : p.toList m ≠ [] := by
      intro hnil
      exact (Equiv.Perm.toList_eq_nil_iff.mp hnil) hsupp
    obtain ⟨a, tail, hlist⟩ := List.exists_cons_of_ne_nil hne
    have ha : a = m := by
      have hzero := p.toList_getElem_zero m hsupp
      simpa [hlist] using hzero
    subst a
    refine ⟨tail, by simp [standardBlock, hfix, hlist], ?_⟩
    intro x hx
    have hcycle : p.SameCycle m x := by
      rw [← mem_standardBlock_iff p hm]
      simp [standardBlock, hfix, hlist, hx]
    have hle : x ≤ m := by
      rw [← hm]
      unfold orbitMaximum
      exact Finset.le_max' (orbit p m) x (by simpa [orbit] using hcycle)
    have hne' : x ≠ m := by
      have hn := p.nodup_toList m
      rw [hlist, List.nodup_cons] at hn
      exact fun h => hn.1 (h ▸ hx)
    exact lt_of_le_of_ne hle hne'

lemma standardCycleBlocks_head_max {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ∀ block ∈ standardCycleBlocks p,
      ∃ m tail, block = m :: tail ∧ ∀ x ∈ tail, x < m := by
  intro block hblock
  simp only [standardCycleBlocks, List.mem_map] at hblock
  obtain ⟨m, hm, rfl⟩ := hblock
  obtain ⟨tail, htail, hlt⟩ := standardBlock_head_max p (by
    simpa [orbitMaxima] using hm)
  exact ⟨m, tail, htail, hlt⟩

lemma standardCycleWord_mem {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Fin n) :
    x ∈ standardCycleWord p := by
  let m := orbitMaximum p x
  have hcycle : p.SameCycle m x := by
    apply Equiv.Perm.SameCycle.symm
    have hmaxMem : orbitMaximum p x ∈ orbit p x := by
      unfold orbitMaximum
      exact Finset.max'_mem _ _
    simpa [m, orbit] using hmaxMem
  have hmEq : orbitMaximum p m = m := by
    simpa [m] using orbitMaximum_eq_of_sameCycle p hcycle
  have hm : m ∈ orbitMaxima p := by simpa [orbitMaxima] using hmEq
  simp only [standardCycleWord, standardCycleBlocks, List.mem_flatten, List.mem_map]
  exact ⟨standardBlock p m, ⟨m, hm, rfl⟩,
    (mem_standardBlock_iff p hmEq).mpr hcycle⟩

lemma standardCycleWord_nodup {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (standardCycleWord p).Nodup := by
  rw [standardCycleWord, List.nodup_flatten]
  constructor
  · intro block hblock
    simp only [standardCycleBlocks, List.mem_map] at hblock
    obtain ⟨m, _, rfl⟩ := hblock
    by_cases hfix : p m = m
    · simp [standardBlock, hfix]
    · simpa [standardBlock, hfix] using p.nodup_toList m
  · rw [standardCycleBlocks, List.pairwise_map]
    have hsorted : (orbitMaxima p).Pairwise (· < ·) := by
      simpa [orbitMaxima] using
        (Finset.sortedLT_sort
          (Finset.univ.filter fun m => orbitMaximum p m = m)).pairwise
    refine hsorted.imp_of_mem ?_
    intro a b haMem hbMem hab
    rw [List.disjoint_left]
    intro x hxa hxb
    have ha : orbitMaximum p a = a := by simpa [orbitMaxima] using haMem
    have hb : orbitMaximum p b = b := by simpa [orbitMaxima] using hbMem
    have hca := (mem_standardBlock_iff p ha).mp hxa
    have hcb := (mem_standardBlock_iff p hb).mp hxb
    have hab' : p.SameCycle a b := hca.trans hcb.symm
    have heq : a = b := by
      simpa [ha, hb] using orbitMaximum_eq_of_sameCycle p hab'
    exact (ne_of_lt hab) heq

private def BlocksMaxFirst {α : Type*} [LT α] (blocks : List (List α)) : Prop :=
  ∀ block ∈ blocks, ∃ m tail, block = m :: tail ∧ ∀ x ∈ tail, x < m

private def BlocksMaxIncreasing {α : Type*} [LT α] (blocks : List (List α)) : Prop :=
  blocks.Pairwise fun left right =>
    ∀ m leftTail k rightTail,
      left = m :: leftTail → right = k :: rightTail → m < k

private lemma recordCutsAux_append_not_lt {α : Type*} [LinearOrder α]
    (maximum : α) (current front rest : List α)
    (hfront : ∀ x ∈ front, ¬maximum < x) :
    recordCutsAux maximum current (front ++ rest) =
      recordCutsAux maximum (front.reverse ++ current) rest := by
  induction front generalizing current with
  | nil => simp
  | cons x xs ih =>
      rw [List.cons_append, recordCutsAux, if_neg (hfront x (by simp))]
      rw [ih (x :: current) (fun y hy => hfront y (by simp [hy]))]
      simp [List.reverse_cons, List.append_assoc]

private lemma recordCuts_flatten_of_standard {α : Type*} [LinearOrder α]
    (blocks : List (List α)) (hfirst : BlocksMaxFirst blocks)
    (horder : BlocksMaxIncreasing blocks) :
    recordCuts blocks.flatten = blocks := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
      obtain ⟨m, tail, rfl, htail⟩ := hfirst block (by simp)
      have htail' : ∀ x ∈ tail, ¬m < x := fun x hx => (htail x hx).asymm
      cases blocks with
      | nil =>
          rw [List.flatten_cons, List.flatten_nil, List.append_nil]
          simp only [recordCuts]
          have haux := recordCutsAux_append_not_lt m [m] tail [] htail'
          conv_lhs => rw [← List.append_nil tail]
          rw [haux]
          simp [recordCutsAux]
      | cons next blocks =>
          obtain ⟨k, nextTail, rfl, hnext⟩ := hfirst next (by simp)
          have hmk : m < k := by
            unfold BlocksMaxIncreasing at horder
            rw [List.pairwise_cons] at horder
            exact horder.1 (k :: nextTail) (by simp) m tail k nextTail rfl rfl
          have hfirstTail : BlocksMaxFirst ((k :: nextTail) :: blocks) := by
            intro b hb
            exact hfirst b (by simp [hb])
          have horderTail : BlocksMaxIncreasing ((k :: nextTail) :: blocks) := by
            exact (List.pairwise_cons.mp horder).2
          rw [List.flatten_cons, List.flatten_cons]
          change recordCutsAux m [m]
            (tail ++ (k :: (nextTail ++ blocks.flatten))) = _
          rw [recordCutsAux_append_not_lt m [m] tail
            (k :: (nextTail ++ blocks.flatten)) htail']
          rw [recordCutsAux, if_pos hmk]
          simp only [List.reverse_append, List.reverse_singleton,
            List.nil_append, List.cons_append]
          have hrec := ih hfirstTail horderTail
          simpa [recordCuts, List.flatten_cons] using congrArg (List.cons (m :: tail)) hrec

private lemma standardCycleBlocks_max_increasing {n : ℕ} (p : Equiv.Perm (Fin n)) :
    BlocksMaxIncreasing (standardCycleBlocks p) := by
  unfold BlocksMaxIncreasing
  rw [standardCycleBlocks, List.pairwise_map]
  have hsorted : (orbitMaxima p).Pairwise (· < ·) := by
    simpa [orbitMaxima] using
      (Finset.sortedLT_sort
        (Finset.univ.filter fun m => orbitMaximum p m = m)).pairwise
  refine hsorted.imp_of_mem ?_
  intro a b ha hb hab m ta k tb hma hkb
  obtain ⟨ta', ha', _⟩ := standardBlock_head_max p (by
    simpa [orbitMaxima] using ha)
  obtain ⟨tb', hb', _⟩ := standardBlock_head_max p (by
    simpa [orbitMaxima] using hb)
  have : m = a := by simpa [ha'] using (congrArg List.head? hma).symm
  have : k = b := by simpa [hb'] using (congrArg List.head? hkb).symm
  subst m
  subst k
  exact hab

/-- Cutting a complete standard cycle word recovers exactly its cycle blocks. -/
theorem recordCuts_standardCycleWord {n : ℕ} (p : Equiv.Perm (Fin n)) :
    recordCuts (standardCycleWord p) = standardCycleBlocks p := by
  exact recordCuts_flatten_of_standard _ (standardCycleBlocks_head_max p)
    (standardCycleBlocks_max_increasing p)

end

end D5.S1.Words.Patterns.ArrowFixedPoint
