/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Left
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Left
   mirror-E: none(waiver:left-pattern-append-classification)
   anchors: [mathlib/module/Mathlib.Data.Finset.Range]
   utility: none
   digest: Classifies the forbidden triples created by appending to the left class. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentQuadrupleDefs
import D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs
import Mathlib.Data.Finset.Range

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Left

open WeakAscentDefs WeakAscentQuadrupleDefs
open D5.S3.Combinatorics.Nonnesting.NonnestingDefs (Occurs)
open D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs

noncomputable def repeatedThreshold (word : List ℕ) : ℕ := by
  classical
  exact (Finset.range word.length).sup fun second =>
    if ∃ first, first < second ∧ word.getD first 0 = word.getD second 0
    then word.getD second 0 else 0

theorem left_append_iff (word : List ℕ) (hne : word ≠ [])
    (hword : word ∈ avoiders word.length [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]])
    (letter : ℕ) :
    word ++ [letter] ∈
      avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] ↔
    repeatedThreshold word ≤ letter ∧ letter ≤ 1 + wasc word ∧
      ¬ ∃ first second, first < second ∧ second < word.length ∧
        word.getD second 0 < word.getD first 0 ∧
        word.getD second 0 ≤ letter ∧ letter ≤ word.getD first 0 := by
  classical
  have triple211 (values : List ℕ) : Occurs [2, 1, 1] values ↔
      ∃ first second third, first < second ∧ second < third ∧ third < values.length ∧
        values.getD second 0 = values.getD third 0 ∧
        values.getD third 0 < values.getD first 0 := by
    constructor
    · intro hocc
      obtain ⟨first, second, third, hfs, hst, ht, hab, hac, hbc, heab, heac, hebc⟩ :=
        (occurs_three_iff 2 1 1 values (by omega) (by omega) (by omega)
          (by intro rank hrank hmax; omega)).mp hocc
      exact ⟨first, second, third, hfs, hst, ht, by omega, by omega⟩
    · rintro ⟨first, second, third, hfs, hst, ht, heq, hlt⟩
      apply (occurs_three_iff 2 1 1 values (by omega) (by omega) (by omega)
        (by intro rank hrank hmax; omega)).mpr
      exact ⟨first, second, third, hfs, hst, ht,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
  have triple212 (values : List ℕ) : Occurs [2, 1, 2] values ↔
      ∃ first second third, first < second ∧ second < third ∧ third < values.length ∧
        values.getD first 0 = values.getD third 0 ∧
        values.getD second 0 < values.getD third 0 := by
    constructor
    · intro hocc
      obtain ⟨first, second, third, hfs, hst, ht, hab, hac, hbc, heab, heac, hebc⟩ :=
        (occurs_three_iff 2 1 2 values (by omega) (by omega) (by omega)
          (by intro rank hrank hmax; omega)).mp hocc
      exact ⟨first, second, third, hfs, hst, ht, by omega, by omega⟩
    · rintro ⟨first, second, third, hfs, hst, ht, heq, hlt⟩
      apply (occurs_three_iff 2 1 2 values (by omega) (by omega) (by omega)
        (by intro rank hrank hmax; omega)).mpr
      exact ⟨first, second, third, hfs, hst, ht,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
  have triple221 (values : List ℕ) : Occurs [2, 2, 1] values ↔
      ∃ first second third, first < second ∧ second < third ∧ third < values.length ∧
        values.getD first 0 = values.getD second 0 ∧
        values.getD third 0 < values.getD second 0 := by
    constructor
    · intro hocc
      obtain ⟨first, second, third, hfs, hst, ht, hab, hac, hbc, heab, heac, hebc⟩ :=
        (occurs_three_iff 2 2 1 values (by omega) (by omega) (by omega)
          (by intro rank hrank hmax; omega)).mp hocc
      exact ⟨first, second, third, hfs, hst, ht, by omega, by omega⟩
    · rintro ⟨first, second, third, hfs, hst, ht, heq, hlt⟩
      apply (occurs_three_iff 2 2 1 values (by omega) (by omega) (by omega)
        (by intro rank hrank hmax; omega)).mpr
      exact ⟨first, second, third, hfs, hst, ht,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
  have triple312 (values : List ℕ) : Occurs [3, 1, 2] values ↔
      ∃ first second third, first < second ∧ second < third ∧ third < values.length ∧
        values.getD second 0 < values.getD third 0 ∧
        values.getD third 0 < values.getD first 0 := by
    constructor
    · intro hocc
      obtain ⟨first, second, third, hfs, hst, ht, hab, hac, hbc, heab, heac, hebc⟩ :=
        (occurs_three_iff 3 1 2 values (by omega) (by omega) (by omega)
          (by intro rank hrank hmax; omega)).mp hocc
      exact ⟨first, second, third, hfs, hst, ht, by omega, by omega⟩
    · rintro ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩
      apply (occurs_three_iff 3 1 2 values (by omega) (by omega) (by omega)
        (by intro rank hrank hmax; omega)).mpr
      exact ⟨first, second, third, hfs, hst, ht,
        by omega, by omega, by omega, by omega, by omega, by omega⟩
  have extend (relation : ℕ → ℕ → ℕ → Prop) :
      (∃ first second third, first < second ∧ second < third ∧
        third < (word ++ [letter]).length ∧
        relation ((word ++ [letter]).getD first 0)
          ((word ++ [letter]).getD second 0) ((word ++ [letter]).getD third 0)) ↔
      (∃ first second third, first < second ∧ second < third ∧ third < word.length ∧
        relation (word.getD first 0) (word.getD second 0) (word.getD third 0)) ∨
      (∃ first second, first < second ∧ second < word.length ∧
        relation (word.getD first 0) (word.getD second 0) letter) := by
    have old_read (index : ℕ) (hindex : index < word.length) :
        (word ++ [letter]).getD index 0 = word.getD index 0 :=
      List.getD_append _ _ _ _ hindex
    have new_read : (word ++ [letter]).getD word.length 0 = letter := by
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
      simp
    constructor
    · rintro ⟨first, second, third, hfs, hst, ht, hrel⟩
      have ht' : third < word.length + 1 := by simpa using ht
      by_cases hold : third < word.length
      · rw [old_read first (by omega), old_read second (by omega),
          old_read third hold] at hrel
        exact Or.inl ⟨first, second, third, hfs, hst, hold, hrel⟩
      · have heq : third = word.length := by omega
        subst third
        rw [old_read first (by omega), old_read second (by omega), new_read] at hrel
        exact Or.inr ⟨first, second, hfs, hst, hrel⟩
    · rintro (⟨first, second, third, hfs, hst, ht, hrel⟩ |
          ⟨first, second, hfs, hs, hrel⟩)
      · refine ⟨first, second, third, hfs, hst, by simpa using (by omega :
          third < word.length + 1), ?_⟩
        rwa [old_read first (by omega), old_read second (by omega), old_read third ht]
      · refine ⟨first, second, word.length, hfs, hs, by simp, ?_⟩
        rwa [old_read first (by omega), old_read second hs, new_read]
  have hweak : IsWeakAscent (word ++ [letter]) ↔ letter ≤ 1 + wasc word := by
    have hlength : 0 < word.length := List.length_pos_iff.mpr hne
    constructor
    · intro h
      have hb := h word.length (by simp)
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),
        List.take_append_of_le_length (Nat.le_refl _), List.take_length] at hb
      simpa [show word.length ≠ 0 by omega] using hb
    · intro hb index hindex
      have hi : index < word.length + 1 := by simpa using hindex
      by_cases hold : index < word.length
      · rw [List.getD_append _ _ _ _ hold,
          List.take_append_of_le_length (Nat.le_of_lt hold)]
        exact hword.2.1 index hold
      · have heq : index = word.length := by omega
        subst index
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),
          List.take_append_of_le_length (Nat.le_refl _), List.take_length]
        simpa [show word.length ≠ 0 by omega] using hb
  have hthreshold : repeatedThreshold word ≤ letter ↔
      ∀ first second, first < second → second < word.length →
        word.getD first 0 = word.getD second 0 → word.getD second 0 ≤ letter := by
    unfold repeatedThreshold
    constructor
    · intro h first second hfs hs heq
      have hsup := Finset.le_sup
        (f := fun second => if ∃ first, first < second ∧
          word.getD first 0 = word.getD second 0 then word.getD second 0 else 0)
        (Finset.mem_range.mpr hs)
      rw [if_pos ⟨first, hfs, heq⟩] at hsup
      exact hsup.trans h
    · intro h
      apply Finset.sup_le_iff.mpr
      intro second hs
      split
      · rename_i hrepeat
        obtain ⟨first, hfs, heq⟩ := hrepeat
        exact h first second hfs (Finset.mem_range.mp hs) heq
      · exact Nat.zero_le _
  have h211 := hword.2.2 [2, 1, 1] (by simp)
  have h212 := hword.2.2 [2, 1, 2] (by simp)
  have h221 := hword.2.2 [2, 2, 1] (by simp)
  have h312 := hword.2.2 [3, 1, 2] (by simp)
  have append211 : Occurs [2, 1, 1] (word ++ [letter]) ↔
      ∃ first second, first < second ∧ second < word.length ∧
        word.getD second 0 = letter ∧ letter < word.getD first 0 := by
    rw [triple211, extend (fun first second third => second = third ∧ third < first)]
    have hold : ¬ ∃ first second third, first < second ∧ second < third ∧
        third < word.length ∧ word.getD second 0 = word.getD third 0 ∧
        word.getD third 0 < word.getD first 0 := by rwa [← triple211]
    exact or_iff_right hold
  have append212 : Occurs [2, 1, 2] (word ++ [letter]) ↔
      ∃ first second, first < second ∧ second < word.length ∧
        word.getD first 0 = letter ∧ word.getD second 0 < letter := by
    rw [triple212, extend (fun first second third => first = third ∧ second < third)]
    have hold : ¬ ∃ first second third, first < second ∧ second < third ∧
        third < word.length ∧ word.getD first 0 = word.getD third 0 ∧
        word.getD second 0 < word.getD third 0 := by rwa [← triple212]
    exact or_iff_right hold
  have append221 : Occurs [2, 2, 1] (word ++ [letter]) ↔
      ∃ first second, first < second ∧ second < word.length ∧
        word.getD first 0 = word.getD second 0 ∧ letter < word.getD second 0 := by
    rw [triple221, extend (fun first second third => first = second ∧ third < second)]
    have hold : ¬ ∃ first second third, first < second ∧ second < third ∧
        third < word.length ∧ word.getD first 0 = word.getD second 0 ∧
        word.getD third 0 < word.getD second 0 := by rwa [← triple221]
    exact or_iff_right hold
  have append312 : Occurs [3, 1, 2] (word ++ [letter]) ↔
      ∃ first second, first < second ∧ second < word.length ∧
        word.getD second 0 < letter ∧ letter < word.getD first 0 := by
    rw [triple312, extend (fun first second third => second < third ∧ third < first)]
    have hold : ¬ ∃ first second third, first < second ∧ second < third ∧
        third < word.length ∧ word.getD second 0 < word.getD third 0 ∧
        word.getD third 0 < word.getD first 0 := by rwa [← triple312]
    exact or_iff_right hold
  constructor
  · intro hchild
    have hbound := hweak.mp hchild.2.1
    have hn211 := hchild.2.2 [2, 1, 1] (by simp)
    have hn212 := hchild.2.2 [2, 1, 2] (by simp)
    have hn221 := hchild.2.2 [2, 2, 1] (by simp)
    have hn312 := hchild.2.2 [3, 1, 2] (by simp)
    refine ⟨hthreshold.mpr ?_, hbound, ?_⟩
    · intro first second hfs hs heq
      by_contra hnot
      exact hn221 (append221.mpr ⟨first, second, hfs, hs, heq, by omega⟩)
    · rintro ⟨first, second, hfs, hs, hinv, hlow, hhigh⟩
      by_cases heqlow : word.getD second 0 = letter
      · exact hn211 (append211.mpr ⟨first, second, hfs, hs, heqlow, by omega⟩)
      · by_cases heqhigh : word.getD first 0 = letter
        · exact hn212 (append212.mpr ⟨first, second, hfs, hs, heqhigh, by omega⟩)
        · exact hn312 (append312.mpr ⟨first, second, hfs, hs, by omega, by omega⟩)
  · rintro ⟨hrepeat, hbound, hinterval⟩
    refine ⟨by simp, hweak.mpr hbound, ?_⟩
    intro pattern hpattern hocc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
    rcases hpattern with rfl | rfl | rfl | rfl
    · obtain ⟨first, second, hfs, hs, heq, hlt⟩ := append211.mp hocc
      exact hinterval ⟨first, second, hfs, hs, by omega, by omega, by omega⟩
    · obtain ⟨first, second, hfs, hs, heq, hlt⟩ := append212.mp hocc
      exact hinterval ⟨first, second, hfs, hs, by omega, by omega, by omega⟩
    · obtain ⟨first, second, hfs, hs, heq, hlt⟩ := append221.mp hocc
      have hb := hthreshold.mp hrepeat first second hfs hs heq
      omega
    · obtain ⟨first, second, hfs, hs, hlow, hhigh⟩ := append312.mp hocc
      exact hinterval ⟨first, second, hfs, hs, by omega, by omega, by omega⟩

end D5.S3.Combinatorics.WeakAscent.WeakAscent215Left
