/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Sites
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Sites
   mirror-E: none(waiver:left-active-site-invariants)
   anchors: []
   utility: none
   digest: Locates the maximum and every active lower site by forbidden-pattern witnesses. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Left
import D5.S3.Combinatorics.WeakAscent.WeakAscentGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Sites

open WeakAscentDefs WeakAscentQuadrupleDefs WeakAscent215Left WeakAscentGrowth
open D5.S3.Combinatorics.Nonnesting.NonnestingDefs (Occurs)
open D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs

theorem left_active_structure (word : List ℕ) (hne : word ≠ [])
    (hword : word ∈ avoiders word.length [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) :
    word.foldr max 0 < 1 + wasc word ∧
    (∀ letter, word.foldr max 0 < letter → letter ≤ 1 + wasc word →
      word ++ [letter] ∈
        avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] ∧
      letter ∉ word) ∧
    (word ++ [word.foldr max 0] ∈
      avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] ↔
      word.getLast?.getD 0 = word.foldr max 0) ∧
    (∀ letter, letter ≤ word.foldr max 0 →
      word ++ [letter] ∈
        avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] →
      letter ≠ word.foldr max 0 → letter < word.getLast?.getD 0) := by
  classical
  have hlength : 0 < word.length := List.length_pos_iff.mpr hne
  have read_bound (index : ℕ) (hindex : index < word.length) :
      word.getD index 0 ≤ word.foldr max 0 := by
    rw [List.getD_eq_getElem _ _ hindex]
    exact List.le_max_of_le (List.getElem_mem hindex) (Nat.le_refl _)
  have last_read : word.getD (word.length - 1) 0 = word.getLast?.getD 0 := by
    rw [List.getLast?_eq_some_getLast hne, Option.getD_some,
      List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]
  have hlast : word.getLast?.getD 0 ≤ word.foldr max 0 := by
    rw [← last_read]
    exact read_bound _ (by omega)
  have maximum_mem : word.foldr max 0 ∈ word := by
    have heq : word.foldr max 0 = word.max hne := by
      apply Nat.le_antisymm
      · exact List.max_le_of_forall_le word _ fun value hvalue => List.le_max_of_mem hvalue
      · exact List.le_max_of_le (List.max_mem hne) (Nat.le_refl _)
    rw [heq]
    exact List.max_mem hne
  obtain ⟨maximumIndex, hmaximumIndex, hmaximumValue⟩ :=
    List.mem_iff_getElem.mp maximum_mem
  have maximum_read : word.getD maximumIndex 0 = word.foldr max 0 := by
    rw [List.getD_eq_getElem _ _ hmaximumIndex]
    exact hmaximumValue
  have threshold_bound : repeatedThreshold word ≤ word.foldr max 0 := by
    unfold repeatedThreshold
    apply Finset.sup_le_iff.mpr
    intro second hsecond
    split
    · exact read_bound second (Finset.mem_range.mp hsecond)
    · exact Nat.zero_le _
  have hheight := height_dominates word hword.2.1
  have inversion_before_last (hlastlt : word.getLast?.getD 0 < word.foldr max 0) :
      maximumIndex < word.length - 1 := by
    by_contra hnot
    have heq : maximumIndex = word.length - 1 := by omega
    rw [heq, last_read] at maximum_read
    omega
  refine ⟨hheight, ?_, ?_, ?_⟩
  · intro letter hrecord hbound
    refine ⟨(left_append_iff word hne hword letter).mpr
      ⟨threshold_bound.trans (Nat.le_of_lt hrecord), hbound, ?_⟩, ?_⟩
    · rintro ⟨first, second, hfs, hs, hinv, hlow, hhigh⟩
      have hfirst := read_bound first (by omega)
      omega
    · intro hmem
      have hle : letter ≤ word.foldr max 0 := List.le_max_of_le hmem (Nat.le_refl _)
      omega
  · constructor
    · intro hchild
      have hcriterion := (left_append_iff word hne hword _).mp hchild
      by_contra hnot
      have hstrict : word.getLast?.getD 0 < word.foldr max 0 := by omega
      exact hcriterion.2.2 ⟨maximumIndex, word.length - 1,
        inversion_before_last hstrict, by omega, by rw [last_read, maximum_read]; omega,
        by rw [last_read]; exact hlast, by rw [maximum_read]⟩
    · intro hlastmax
      apply (left_append_iff word hne hword _).mpr
      refine ⟨threshold_bound, Nat.le_of_lt hheight, ?_⟩
      rintro ⟨first, second, hfs, hs, hinv, hlow, hhigh⟩
      have hfirst := read_bound first (by omega)
      have hfirstmax : word.getD first 0 = word.foldr max 0 := by omega
      have hsecondBefore : second < word.length - 1 := by
        by_contra hnot
        have heq : second = word.length - 1 := by omega
        rw [heq, last_read, hlastmax] at hinv
        omega
      have hocc : Occurs [2, 1, 2] word := by
        apply (occurs_three_iff 2 1 2 word (by omega) (by omega) (by omega)
          (by intro rank hrank hmax; omega)).mpr
        refine ⟨first, second, word.length - 1, hfs, hsecondBefore, by omega, ?_⟩
        rw [last_read, hlastmax]
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      exact hword.2.2 [2, 1, 2] (by simp) hocc
  · intro letter hlow hchild hnotmax
    by_cases hlastmax : word.getLast?.getD 0 = word.foldr max 0
    · omega
    · have hstrict : word.getLast?.getD 0 < word.foldr max 0 := by omega
      have hcriterion := (left_append_iff word hne hword letter).mp hchild
      by_contra hnot
      exact hcriterion.2.2 ⟨maximumIndex, word.length - 1,
        inversion_before_last hstrict, by omega, by rw [last_read, maximum_read]; omega,
        by rw [last_read]; omega, by rw [maximum_read]; exact hlow⟩

end D5.S3.Combinatorics.WeakAscent.WeakAscent215Sites
