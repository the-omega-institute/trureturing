/- GID: D5/S3/Combinatorics/Lattices/Tamari/BracketRows
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Lattices/Tamari/BracketRows
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Interval rows compare by their endpoints in the complete bracket order. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.UpperLower.Closure
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

/-
Copyright (c) 2026 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in
docs/reports/licenses/garber-boolean-antichains/Mathlib-APACHE-2.0-LICENSE.txt.
Authors: Julian Kuelshammer
-/

/-!
The predicate and subtype below are a port from
Mathlib/Combinatorics/Enumerative/Catalan/BracketingFunction.lean in Mathlib PR #44762,
commit 96e7345a164bf518920d5a9f94b557cc27b62e07.
This extraction uses the direct Fin import and omits the unused decidability derivation
and auxiliary declarations.
-/

set_option autoImplicit false

namespace Function

variable {n : ℕ}

/-- A function `a : Fin n → Fin n` is bracketing if `i ≤ a i` for all `i` and for all `i` and `j`
such that `i ≤ j ≤ a i` one has `a j ≤ a i`. -/
def IsBracketing (a : Fin n → Fin n) : Prop :=
  (∀ i, i ≤ a i) ∧ (∀ i j, i ≤ j → j ≤ a i → a j ≤ a i)

end Function

/-- The `Type` of bracketing functions `Fin n → Fin n`. -/
abbrev BracketingFunctions (n : ℕ) : Type := {a : Fin n → Fin n // a.IsBracketing}

/-!
# Interval rows and their generated lower sets

For ambient size `n + 1`, the row indices are the one-based integers in `[1, n]`.
Coordinates and values of the bracketing functions themselves are zero-based.
-/

namespace D5.S3.Combinatorics.Lattices.Tamari

/-- For ambient size `N = n + 1`, the one-based row indices are `1 ≤ s ≤ n`. -/
abbrev RowIndex (n : ℕ) := {s : ℕ // 1 ≤ s ∧ s ≤ n}

/-- The admissible one-based left endpoints for the row indexed by `s`. -/
abbrev LeftEndpoint {n : ℕ} (s : RowIndex n) := {a : ℕ // 1 ≤ a ∧ a ≤ s.val}

/-- The shift between zero-based enumeration and the one-based row indices. -/
def rowIndexEquiv (n : ℕ) : Fin n ≃ RowIndex n where
  toFun i := ⟨i.val + 1, Nat.zero_lt_succ _, i.isLt⟩
  invFun s := ⟨s.val - 1, by have := s.property; omega⟩
  left_inv i := Fin.ext (Nat.add_sub_cancel_right _ _)
  right_inv s := Subtype.ext (Nat.sub_add_cancel s.property.1)

variable {n : ℕ}

private def coord (s : RowIndex n) : Fin (n + 1) :=
  ((rowIndexEquiv n).symm s).castSucc

private theorem coord_oneBased (s : RowIndex n) : (coord s).val + 1 = s.val :=
  Nat.sub_add_cancel s.property.1

private def rowValue (s : RowIndex n) (a : LeftEndpoint s) (i : Fin (n + 1)) :
    Fin (n + 1) :=
  if a.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val then coord s else Fin.last n

private theorem rowValue_of_mem (s : RowIndex n) (a : LeftEndpoint s) (i : Fin (n + 1))
    (hi : a.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val) : rowValue s a i = coord s :=
  ite_eq_left hi

private theorem rowValue_of_not_mem (s : RowIndex n) (a : LeftEndpoint s) (i : Fin (n + 1))
    (hi : ¬ (a.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val)) : rowValue s a i = Fin.last n :=
  ite_eq_right hi

/-- The interval row as an element of the nested bracketing subtype. -/
def row (s : RowIndex n) (a : LeftEndpoint s) : BracketingFunctions (n + 1) :=
  ⟨rowValue s a, by
    constructor
    · intro i
      by_cases hi : a.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val
      · rw [rowValue_of_mem s a i hi]
        change i.val ≤ (coord s).val
        have hs := coord_oneBased s
        omega
      · rw [rowValue_of_not_mem s a i hi]
        exact Fin.le_last i
    · intro i j hij hj
      by_cases hi : a.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val
      · rw [rowValue_of_mem s a i hi] at hj ⊢
        have hij' : i.val ≤ j.val := hij
        have hj' : j.val ≤ (coord s).val := hj
        have hs := coord_oneBased s
        have hjInterval : a.val ≤ j.val + 1 ∧ j.val + 1 ≤ s.val := by omega
        rw [rowValue_of_mem s a j hjInterval]
      · rw [rowValue_of_not_mem s a i hi]
        exact Fin.le_last _⟩

theorem row_value_oneBased (s : RowIndex n) (a : LeftEndpoint s) (i : Fin (n + 1)) :
    ((row s a).val i).val + 1 =
      if a.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val then s.val else n + 1 := by
  change (rowValue s a i).val + 1 = _
  by_cases hi : a.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val
  · rw [rowValue_of_mem s a i hi, ite_eq_left hi, coord_oneBased]
  · rw [rowValue_of_not_mem s a i hi, ite_eq_right hi, Fin.val_last]

private theorem rowValue_le_coord_iff (s t : RowIndex n) (a : LeftEndpoint s)
    (i : Fin (n + 1)) :
    rowValue s a i ≤ coord t ↔ (a.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val) ∧ s.val ≤ t.val := by
  by_cases hi : a.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val
  · rw [rowValue_of_mem s a i hi]
    simp only [hi, true_and]
    change (coord s).val ≤ (coord t).val ↔ s.val ≤ t.val
    have hs := coord_oneBased s
    have ht := coord_oneBased t
    omega
  · rw [rowValue_of_not_mem s a i hi]
    simp only [hi, false_and, iff_false]
    exact not_le_of_gt (Fin.castSucc_lt_last ((rowIndexEquiv n).symm t))

/-- The subtype order compares rows only within the same right endpoint. -/
theorem row_le_row_iff (s t : RowIndex n) (a : LeftEndpoint s) (b : LeftEndpoint t) :
    row s a ≤ row t b ↔ s = t ∧ a.val ≤ b.val := by
  change (∀ i, rowValue s a i ≤ rowValue t b i) ↔ _
  constructor
  · intro h
    have htInterval : b.val ≤ (coord t).val + 1 ∧ (coord t).val + 1 ≤ t.val := by
      rw [coord_oneBased]
      exact ⟨b.property.2, le_rfl⟩
    have ht := h (coord t)
    rw [rowValue_of_mem t b (coord t) htInterval, rowValue_le_coord_iff] at ht
    have hts := ht.1.2
    rw [coord_oneBased] at hts
    have hst : s = t := Subtype.ext (le_antisymm ht.2 hts)
    subst t
    let left : RowIndex n := ⟨b.val, b.property.1, b.property.2.trans s.property.2⟩
    have hbIndex : (coord left).val + 1 = b.val := coord_oneBased left
    have hbInterval : b.val ≤ (coord left).val + 1 ∧ (coord left).val + 1 ≤ s.val := by
      rw [hbIndex]
      exact ⟨le_rfl, b.property.2⟩
    have hb := h (coord left)
    rw [rowValue_of_mem s b (coord left) hbInterval, rowValue_le_coord_iff, hbIndex] at hb
    exact ⟨rfl, hb.1.1⟩
  · rintro ⟨rfl, hab⟩ i
    by_cases hi : b.val ≤ i.val + 1 ∧ i.val + 1 ≤ s.val
    · rw [rowValue_of_mem s b i hi, rowValue_le_coord_iff]
      exact ⟨⟨hab.trans hi.1, hi.2⟩, le_rfl⟩
    · rw [rowValue_of_not_mem s b i hi]
      exact Fin.le_last _

/-- One actual row for every proper right endpoint. -/
def rowFamily (A : (s : RowIndex n) → LeftEndpoint s) (s : RowIndex n) :
    BracketingFunctions (n + 1) :=
  row s (A s)

theorem lowerClosure_rowFamily_le_iff (A B : (s : RowIndex n) → LeftEndpoint s) :
    lowerClosure (Set.range (rowFamily A)) ≤ lowerClosure (Set.range (rowFamily B)) ↔
      ∀ s, (A s).val ≤ (B s).val := by
  rw [lowerClosure_le]
  constructor
  · intro h s
    have hs := h (Set.mem_range_self s)
    change rowFamily A s ∈ lowerClosure (Set.range (rowFamily B)) at hs
    obtain ⟨_, ⟨t, rfl⟩, hst⟩ := mem_lowerClosure.mp hs
    obtain ⟨rfl, hab⟩ := (row_le_row_iff s t (A s) (B t)).mp hst
    exact hab
  · rintro h _ ⟨s, rfl⟩
    exact mem_lowerClosure.mpr ⟨rowFamily B s, Set.mem_range_self s,
      (row_le_row_iff s s (A s) (B s)).mpr ⟨rfl, h s⟩⟩

theorem rowFamily_injective (A : (s : RowIndex n) → LeftEndpoint s) :
    Function.Injective (rowFamily A) := by
  intro s t h
  exact ((row_le_row_iff s t (A s) (A t)).mp h.le).1

/-- Each such generated family has exactly `n` distinct rows. -/
theorem rowFamily_ncard (A : (s : RowIndex n) → LeftEndpoint s) :
    (Set.range (rowFamily A)).ncard = n :=
  (Set.ncard_range_of_injective (rowFamily_injective A)).trans
    ((Nat.card_congr (rowIndexEquiv n).symm).trans (Nat.card_fin n))

end D5.S3.Combinatorics.Lattices.Tamari

/-! # Coordinate infima and the complete bracket lattice -/

namespace D5.S3.Combinatorics.Lattices.Tamari

noncomputable section

variable {n : ℕ}

/-- A coordinate minimum uses the last index as its empty-family value. -/
private def values (C : Set (BracketingFunctions (n + 1))) (i : Fin (n + 1)) : Set ℕ :=
  insert n (Set.range fun b : C => (b.val.val i).val)

private theorem min_mem (C : Set (BracketingFunctions (n + 1))) (i : Fin (n + 1)) :
    sInf (values C i) ∈ values C i :=
  Nat.sInf_mem ⟨n, Set.mem_insert _ _⟩

private def meetValue (C : Set (BracketingFunctions (n + 1))) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨sInf (values C i), Nat.lt_succ_of_le (Nat.sInf_le (Set.mem_insert _ _))⟩

private theorem meetValue_le {C : Set (BracketingFunctions (n + 1))} {b : BracketingFunctions (n + 1)}
    (hb : b ∈ C) (i : Fin (n + 1)) : meetValue C i ≤ b.val i :=
  Nat.sInf_le (Set.mem_insert_of_mem _ (Set.mem_range_self (⟨b, hb⟩ : C)))

private theorem meetValue_eq_or (C : Set (BracketingFunctions (n + 1))) (i : Fin (n + 1)) :
    meetValue C i = Fin.last n ∨ ∃ b ∈ C, meetValue C i = b.val i := by
  rcases Set.mem_insert_iff.mp (min_mem C i) with h | ⟨b, hb⟩
  · exact Or.inl (Fin.ext h)
  · exact Or.inr ⟨b.val, b.property, Fin.ext hb.symm⟩

private def meetSet (C : Set (BracketingFunctions (n + 1))) : BracketingFunctions (n + 1) :=
  ⟨meetValue C, by
    constructor
    · intro i
      rcases meetValue_eq_or C i with h | ⟨b, _, h⟩
      · rw [h]; exact Fin.le_last i
      · rw [h]; exact b.property.1 i
    · intro i j hij hj
      rcases meetValue_eq_or C i with h | ⟨b, hb, h⟩
      · rw [h]; exact Fin.le_last _
      · rw [h] at hj ⊢
        exact (meetValue_le hb j).trans (b.property.2 i j hij hj)⟩

private theorem meetSet_isGLB (C : Set (BracketingFunctions (n + 1))) : IsGLB C (meetSet C) := by
  refine ⟨fun _ hb i => meetValue_le hb i, fun b hb i => ?_⟩
  change b.val i ≤ meetValue C i
  rcases meetValue_eq_or C i with h | ⟨d, hd, h⟩
  · rw [h]; exact Fin.le_last _
  · rw [h]; exact hb hd i

/-- The bracket order has coordinatewise meets and its joins are meets of upper bounds. -/
instance bracketCompleteLattice (n : ℕ) : CompleteLattice (BracketingFunctions (n + 1)) :=
  letI : InfSet (BracketingFunctions (n + 1)) := ⟨meetSet⟩
  completeLatticeOfInf _ meetSet_isGLB

theorem sInf_coord_min (C : Set (BracketingFunctions (n + 1))) (i : Fin (n + 1)) :
    ((sInf C).val i).val = sInf (insert n (Set.range fun b : C => (b.val.val i).val)) :=
  rfl

theorem sInf_coord_eq_or (C : Set (BracketingFunctions (n + 1))) (i : Fin (n + 1)) :
    (sInf C).val i = Fin.last n ∨ ∃ b ∈ C, (sInf C).val i = b.val i :=
  meetValue_eq_or C i

@[simp]
theorem top_coord (i : Fin (n + 1)) :
    (⊤ : BracketingFunctions (n + 1)).val i = Fin.last n := by
  apply Fin.ext
  rw [← sInf_empty, sInf_coord_min]
  rw [Set.range_eq_empty]
  simp

theorem sup_eq_inf_upper (a b : BracketingFunctions (n + 1)) :
    a ⊔ b = sInf {c | a ≤ c ∧ b ≤ c} := rfl

end

end D5.S3.Combinatorics.Lattices.Tamari
