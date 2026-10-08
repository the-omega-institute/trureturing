/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftTree
   mirror-E: none(waiver:finite-continuation-tree)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic]
   utility: none
   digest: Matching low positions and high distances preserves first-letter continuations. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftTree

def leftChild (word : List Bool) (reserve : ℕ) (maximumActive : Bool) (index : ℕ) :
    List Bool × ℕ × Bool :=
  if index < word.length then
    if word.getD index false then
      if maximumActive && decide (index + 1 = word.length) then ([true], reserve + 1, true)
      else ([], reserve + 1, false)
    else (word.take index, reserve + 1, false)
  else (word ++ List.replicate (index - word.length) false ++ [true],
    reserve - (index - word.length), true)

def leftCount : ℕ → List Bool → ℕ → Bool → ℕ
  | 0, _, _, _ => 1
  | depth + 1, word, reserve, maximumActive =>
    ∑ index ∈ Finset.range (word.length + reserve),
      let child := leftChild word reserve maximumActive index
      leftCount depth child.1 child.2.1 child.2.2

theorem left_internal_isomorphisms (depth : ℕ) :
    (∀ (suffix : List Bool) (reserve : ℕ) (maximumActive : Bool),
      (maximumActive = true → suffix ≠ []) →
      leftCount depth (true :: suffix) reserve maximumActive =
        leftCount depth (false :: suffix) reserve maximumActive) ∧
    (∀ reserve : ℕ, leftCount depth [true] reserve true =
      leftCount depth [] (reserve + 1) false) := by
  induction depth with
  | zero => exact ⟨by intros; rfl, by intro reserve; rfl⟩
  | succ depth ih =>
    constructor
    · intro suffix reserve maximumActive hflag
      simp only [leftCount, List.length_cons]
      apply Finset.sum_congr rfl
      intro index _hindex
      by_cases hlow : index < suffix.length + 1
      · cases index with
        | zero =>
          have hnotLast : ¬ (maximumActive = true ∧ suffix.length = 0) := by
            rintro ⟨hactive, hlength⟩
            exact hflag hactive (List.length_eq_zero_iff.mp hlength)
          cases maximumActive <;> simp_all [leftChild, List.getD]
        | succ index =>
          cases hentry : suffix.getD index false with
          | false =>
            simp only [List.getD,
              List.getElem?_eq_getElem (by omega : index < suffix.length),
              Option.getD_some] at hentry
            simpa [leftChild, hlow, hentry, List.take_succ_cons, List.getD] using
              ih.1 (suffix.take index) (reserve + 1) false (by simp)
          | true =>
            simp only [List.getD,
              List.getElem?_eq_getElem (by omega : index < suffix.length),
              Option.getD_some] at hentry
            simp [leftChild, hlow, hentry, List.getD]
      · simpa [leftChild, hlow] using
          ih.1 (suffix ++ List.replicate (index - (suffix.length + 1)) false ++ [true])
            (reserve - (index - (suffix.length + 1))) true (by simp)
    · intro reserve
      simp only [leftCount, List.length_cons, List.length_nil, Nat.zero_add]
      rw [Nat.add_comm 1 reserve]
      apply Finset.sum_congr rfl
      intro index _hindex
      cases index with
      | zero => simp [leftChild, List.getD]
      | succ index =>
        simpa [leftChild, List.replicate_succ, Nat.succ_sub_succ_eq_sub] using
          ih.1 (List.replicate index false ++ [true]) (reserve - index) true (by simp)

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftTree
