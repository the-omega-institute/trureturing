/- GID: D5/S3/Combinatorics/LevelSequence/LevelSequenceDescent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LevelSequence/LevelSequenceDescent
   mirror-E: none(waiver:pattern-pair-characterization)
   anchors: [mathlib/module/Mathlib.Data.List.GetD]
   utility: none
   digest: Strong descents characterize avoidance and determine legal appended letters. -/

import D5.S3.Combinatorics.LevelSequence.LevelSequenceDefs
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LevelSequence.LevelSequenceDescent

open LevelSequenceDefs

theorem strong_descent (word : List ℕ) :
    (¬ Contains101 word ∧ ¬ Contains102 word) ↔
      ∀ first middle last : ℕ, first < middle → middle < last → last < word.length →
        word.getD middle 0 < word.getD first 0 → word.getD last 0 < word.getD first 0 := by
  constructor
  · rintro ⟨no101, no102⟩ first middle last before after inside descent
    by_contra notBelow
    have above : word.getD first 0 ≤ word.getD last 0 := Nat.le_of_not_gt notBelow
    rcases lt_or_eq_of_le above with strict | equal
    · exact no102 ⟨first, middle, last, before, after, inside, descent, strict⟩
    · exact no101 ⟨first, middle, last, before, after, inside, descent, equal.symm⟩
  · intro descent
    constructor
    · rintro ⟨first, middle, last, before, after, inside, drop, equal⟩
      have below := descent first middle last before after inside drop
      omega
    · rintro ⟨first, middle, last, before, after, inside, drop, rise⟩
      have below := descent first middle last before after inside drop
      omega

theorem append_criterion (word : List ℕ) (letter : ℕ) (nonempty : word ≠ []) :
    (IsLevel (word ++ [letter]) ∧
      ¬ Contains101 (word ++ [letter]) ∧ ¬ Contains102 (word ++ [letter])) ↔
    IsLevel word ∧ ¬ Contains101 word ∧ ¬ Contains102 word ∧
      letter ≤ 1 + lev word ∧
      ∀ first middle : ℕ, first < middle → middle < word.length →
        word.getD middle 0 < word.getD first 0 → letter < word.getD first 0 := by
  have positive : 0 < word.length := List.length_pos_iff.mpr nonempty
  have oldEntry (index : ℕ) (inside : index < word.length) :
      (word ++ [letter]).getD index 0 = word.getD index 0 :=
    List.getD_append _ _ _ _ inside
  have lastEntry : (word ++ [letter]).getD word.length 0 = letter := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  have oldPrefix (index : ℕ) (inside : index ≤ word.length) :
      (word ++ [letter]).take index = word.take index := by
    rw [List.take_append, Nat.sub_eq_zero_of_le inside]
    simp
  constructor
  · rintro ⟨level, no101, no102⟩
    have oldLevel : IsLevel word := by
      intro index inside
      have bound := level index (by simp; omega)
      rw [oldEntry index inside, oldPrefix index (by omega)] at bound
      exact bound
    have oldAvoidance : ¬ Contains101 word ∧ ¬ Contains102 word := by
      constructor
      · rintro ⟨first, middle, last, before, after, inside, drop, equal⟩
        apply no101
        refine ⟨first, middle, last, before, after, by simp; omega, ?_, ?_⟩
        · simpa only [oldEntry first (by omega), oldEntry middle (by omega)] using drop
        · simpa only [oldEntry first (by omega), oldEntry last inside] using equal
      · rintro ⟨first, middle, last, before, after, inside, drop, rise⟩
        apply no102
        refine ⟨first, middle, last, before, after, by simp; omega, ?_, ?_⟩
        · simpa only [oldEntry first (by omega), oldEntry middle (by omega)] using drop
        · simpa only [oldEntry first (by omega), oldEntry last inside] using rise
    refine ⟨oldLevel, oldAvoidance.1, oldAvoidance.2, ?_, ?_⟩
    · have bound := level word.length (by simp)
      rw [lastEntry, oldPrefix word.length le_rfl, List.take_length,
        if_neg (by omega)] at bound
      exact bound
    · intro first middle before inside drop
      by_contra notBelow
      have above : word.getD first 0 ≤ letter := Nat.le_of_not_gt notBelow
      rcases lt_or_eq_of_le above with rise | equal
      · apply no102
        refine ⟨first, middle, word.length, before, inside, by simp, ?_, ?_⟩
        · simpa only [oldEntry first (by omega), oldEntry middle inside] using drop
        · simpa only [oldEntry first (by omega), lastEntry] using rise
      · apply no101
        refine ⟨first, middle, word.length, before, inside, by simp, ?_, ?_⟩
        · simpa only [oldEntry first (by omega), oldEntry middle inside] using drop
        · simpa only [oldEntry first (by omega), lastEntry] using equal.symm
  · rintro ⟨level, no101, no102, bound, barrier⟩
    have newLevel : IsLevel (word ++ [letter]) := by
      intro index inside
      by_cases old : index < word.length
      · rw [oldEntry index old, oldPrefix index (by omega)]
        exact level index old
      · have hlen : index < word.length + 1 := by
          simpa only [List.length_append, List.length_singleton] using inside
        have final : index = word.length := by omega
        subst index
        rw [lastEntry, oldPrefix word.length le_rfl, List.take_length,
          if_neg (by omega)]
        exact bound
    refine ⟨newLevel, ?_, ?_⟩
    · rintro ⟨first, middle, last, before, after, inside, drop, equal⟩
      have middleOld : middle < word.length := by
        simp only [List.length_append, List.length_singleton] at inside
        omega
      have firstOld : first < word.length := by omega
      rw [oldEntry first firstOld, oldEntry middle middleOld] at drop
      by_cases lastOld : last < word.length
      · apply no101
        refine ⟨first, middle, last, before, after, lastOld, drop, ?_⟩
        simpa only [oldEntry first firstOld, oldEntry last lastOld] using equal
      · have final : last = word.length := by
          simp only [List.length_append, List.length_singleton] at inside
          omega
        subst last
        rw [oldEntry first firstOld, lastEntry] at equal
        have below := barrier first middle before middleOld drop
        omega
    · rintro ⟨first, middle, last, before, after, inside, drop, rise⟩
      have middleOld : middle < word.length := by
        simp only [List.length_append, List.length_singleton] at inside
        omega
      have firstOld : first < word.length := by omega
      rw [oldEntry first firstOld, oldEntry middle middleOld] at drop
      by_cases lastOld : last < word.length
      · apply no102
        refine ⟨first, middle, last, before, after, lastOld, drop, ?_⟩
        simpa only [oldEntry first firstOld, oldEntry last lastOld] using rise
      · have final : last = word.length := by
          simp only [List.length_append, List.length_singleton] at inside
          omega
        subst last
        rw [oldEntry first firstOld, lastEntry] at rise
        have below := barrier first middle before middleOld drop
        omega

end D5.S3.Combinatorics.LevelSequence.LevelSequenceDescent
