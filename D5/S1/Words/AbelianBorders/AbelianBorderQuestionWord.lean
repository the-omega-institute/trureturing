/- GID: D5/S1/Words/AbelianBorders/AbelianBorderQuestionWord
   generality: G
   mirror-B: D5/B/S1/Words/AbelianBorders/AbelianBorderQuestionWord
   mirror-E: none(waiver:explicit-ternary-word)
   anchors: []
   utility: none
   digest: A ternary word with balanced blocks and unbounded runs between square markers. -/

import D5.S1.Words.AbelianBorders.AbelianBorderQuestionDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.AbelianBorders
open AbelianBorderQuestionDefs
namespace Counterexample

/-- The length-fifteen excursion, with five occurrences of each letter. -/
def A : List (Fin 3) := [1, 1, 0, 0, 2, 2, 2, 2, 2, 0, 0, 0, 1, 1, 1]

/-- The short balanced block. -/
def B : List (Fin 3) := [0, 1, 2]

noncomputable def block (j : ℕ) : List (Fin 3) := by
  classical
  exact if IsSquare j then B else A

/-- Finite initial concatenations determine the infinite word compatibly. -/
noncomputable def initial : ℕ → List (Fin 3)
  | 0 => []
  | j + 1 => initial j ++ block j

noncomputable def word (n : ℕ) : Fin 3 := (initial (n + 1)).getD n 0

/-- Prefix compatibility constructs the word and its bounded balanced decomposition. -/
theorem word_structure :
    (∀ j r, r ≤ (block j).length →
      factor word 0 ((initial j).length + r) = initial j ++ (block j).take r) ∧
    (∀ j (a : Fin 3), (initial j).count a = (initial j).count 0) ∧
    BoundedWeakAbelianPeriodic word := by
  classical
  have size (j : ℕ) : 3 ≤ (block j).length ∧ (block j).length ≤ 15 := by
    unfold block
    split <;> decide
  have counts (j : ℕ) (a : Fin 3) : (block j).count a = (block j).count 0 := by
    unfold block
    split <;> fin_cases a <;> decide
  have grows : ∀ j, j ≤ (initial j).length := by
    intro j
    induction j with
    | zero => simp [initial]
    | succ j ih =>
      simp only [initial, List.length_append]
      have := (size j).1
      omega
  have extension : ∀ j k, j ≤ k → ∃ v, initial k = initial j ++ v := by
    intro j k h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    induction d with
    | zero => exact ⟨[], by simp⟩
    | succ d ih =>
      obtain ⟨v, hv⟩ := ih (by omega)
      exact ⟨v ++ block (j + d), by simp [initial, hv, List.append_assoc]⟩
  have stable (j : ℕ) (n : ℕ) (hn : n < (initial j).length) :
      word n = (initial j).getD n 0 := by
    unfold word
    rcases le_total j (n + 1) with h | h
    · obtain ⟨v, hv⟩ := extension j (n + 1) h
      rw [hv]
      simp [List.getD, List.getElem?_append_left hn]
    · obtain ⟨v, hv⟩ := extension (n + 1) j h
      rw [hv]
      have hn' : n < (initial (n + 1)).length := by have := grows (n + 1); omega
      simp [List.getD, List.getElem?_append_left hn']
  have prefixFormula (j r : ℕ) (hr : r ≤ (block j).length) :
      factor word 0 ((initial j).length + r) = initial j ++ (block j).take r := by
    have ht : (initial j ++ (block j).take r) =
        (initial (j + 1)).take ((initial j).length + r) := by
      simp [initial, List.take_append]
    rw [ht]
    apply List.ext_getElem
    · simp [factor, initial, List.length_take, Nat.min_eq_left (by omega :
        (initial j).length + r ≤ (initial j).length + (block j).length)]
    · intro n hn hm
      have hn' : n < (initial (j + 1)).length := by
        simp only [List.length_take] at hm
        omega
      simp only [factor, List.getElem_map, List.getElem_range, Nat.zero_add]
      rw [List.getElem_take]
      exact (stable (j + 1) n hn').trans (List.getElem_eq_getD 0).symm
  have balanced : ∀ j (a : Fin 3), (initial j).count a = (initial j).count 0 := by
    intro j a
    induction j with
    | zero => simp [initial]
    | succ j ih => simp only [initial, List.count_append, ih, counts]
  refine ⟨prefixFormula, balanced, ?_⟩
  let t : ℕ → ℕ := fun j => (initial j).length
  have step (j : ℕ) : t (j + 1) = t j + (block j).length := by
    simp [t, initial]
  have increasing : StrictMono t := strictMono_nat_of_lt_succ fun j => by
    rw [step]
    have := (size j).1
    omega
  have tile (j : ℕ) : factor word (t j) (t (j + 1) - t j) = block j := by
    have hs : t (j + 1) - t j = (block j).length := by rw [step]; omega
    rw [hs]
    apply List.ext_getElem
    · simp [factor]
    · intro n hn hm
      have hn' : t j + n < (initial (j + 1)).length := by
        change t j + n < t (j + 1)
        rw [step]
        omega
      simp only [factor, List.getElem_map, List.getElem_range]
      rw [stable (j + 1) (t j + n) hn', ← List.getElem_eq_getD (h := hn') 0]
      simp [initial, t, List.getElem_append_right]
  refine ⟨t, 15, increasing, ?_, ?_⟩
  · intro j
    rw [step]
    simpa using (size j).2
  · intro j
    rw [tile, tile]
    refine ⟨?_, ?_, ?_⟩
    · have := (size j).1; exact List.ne_nil_of_length_pos (by omega)
    · have := (size 0).1; exact List.ne_nil_of_length_pos (by omega)
    · intro a
      have ratio (i : ℕ) : (block i).length = 3 * (block i).count 0 := by
        unfold block
        split <;> decide
      simp only [letterCount, counts, ratio]
      ring

end Counterexample
end D5.S1.Words.AbelianBorders
