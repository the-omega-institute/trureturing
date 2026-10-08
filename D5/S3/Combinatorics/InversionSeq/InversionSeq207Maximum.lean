/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Maximum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Maximum
   mirror-E: none(waiver:maximum-pattern-decomposition)
   anchors: []
   utility: none
   digest: Maximum triples force terminal blocks, ordered suffixes and legal deletion. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Maximum

open D5.S3.Combinatorics Nonnesting InversionSeqOccurs

theorem maximum_decomposition (word : List ℕ) (patterns : List (List ℕ))
    (hclass : patterns = [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] ∨
      patterns = [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]])
    (hword : word ∈ InversionSeqDefs.avoiders word.length patterns)
    (first : ℕ)
    (hmax : ∀ index < word.length, word.getD index 0 ≤ word.getD first 0) :
    (∀ second : ℕ, first < second → second < word.length →
      word.getD second 0 = word.getD first 0 →
      ∀ later : ℕ, first < later → later < word.length →
        word.getD later 0 = word.getD first 0) ∧
    ((∀ index < word.length, word.getD index 0 = word.getD first 0 → index = first) →
      ∀ earlier later : ℕ, first < earlier → earlier < later → later < word.length →
        (patterns = [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] →
          word.getD later 0 < word.getD earlier 0) ∧
        (patterns = [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]] →
          word.getD earlier 0 ≤ word.getD later 0)) ∧
    (∀ deleted : ℕ, deleted < word.length → word.getD deleted 0 = word.getD first 0 →
      word.eraseIdx deleted ∈ InversionSeqDefs.avoiders (word.length - 1) patterns) := by
  have h101 : ¬ NonnestingDefs.Occurs [2, 1, 2] word := by
    apply hword.2.2 [2, 1, 2]
    rcases hclass with hleft | hright
    · simp [hleft]
    · simp [hright]
  have h110 : ¬ NonnestingDefs.Occurs [2, 2, 1] word := by
    apply hword.2.2 [2, 2, 1]
    rcases hclass with hleft | hright
    · simp [hleft]
    · simp [hright]
  refine ⟨?_, ?_, ?_⟩
  · intro second hsecond hsecondlen hsame later hlater hlaterlen
    have hlower := hmax later hlaterlen
    by_contra hdifferent
    have hstrict : word.getD later 0 < word.getD first 0 := by omega
    by_cases hbefore : later < second
    · apply h101
      apply (occurs_three_iff 2 1 2 word (by omega) (by omega) (by omega)
        (by omega)).mpr
      exact ⟨first, later, second, hlater, hbefore, hsecondlen, by omega⟩
    · have hafter : second < later := by
        by_contra hnot
        have heq : second = later := by omega
        subst later
        omega
      apply h110
      apply (occurs_three_iff 2 2 1 word (by omega) (by omega) (by omega)
        (by omega)).mpr
      exact ⟨first, second, later, hsecond, hafter, hlaterlen, by omega⟩
  · intro hunique earlier later hearlier hlater hlaterlen
    have hearlierlen : earlier < word.length := by omega
    have hearliermax := hmax earlier hearlierlen
    have hlatermax := hmax later hlaterlen
    have hearlierstrict : word.getD earlier 0 < word.getD first 0 := by
      have hne : word.getD earlier 0 ≠ word.getD first 0 := by
        intro heq
        have := hunique earlier hearlierlen heq
        omega
      omega
    have hlaterstrict : word.getD later 0 < word.getD first 0 := by
      have hne : word.getD later 0 ≠ word.getD first 0 := by
        intro heq
        have := hunique later hlaterlen heq
        omega
      omega
    constructor
    · intro hleft
      by_contra hdecreasing
      by_cases heq : word.getD earlier 0 = word.getD later 0
      · apply hword.2.2 [2, 1, 1] (by simp [hleft])
        apply (occurs_three_iff 2 1 1 word (by omega) (by omega) (by omega)
          (by omega)).mpr
        exact ⟨first, earlier, later, hearlier, hlater, hlaterlen, by omega⟩
      · apply hword.2.2 [3, 1, 2] (by simp [hleft])
        apply (occurs_three_iff 3 1 2 word (by omega) (by omega) (by omega)
          (by omega)).mpr
        exact ⟨first, earlier, later, hearlier, hlater, hlaterlen, by omega⟩
    · intro hright
      by_contra hincreasing
      apply hword.2.2 [3, 2, 1] (by simp [hright])
      apply (occurs_three_iff 3 2 1 word (by omega) (by omega) (by omega)
        (by omega)).mpr
      exact ⟨first, earlier, later, hearlier, hlater, hlaterlen, by omega⟩
  · intro deleted hdeleted hsame
    have hlength := List.length_eraseIdx_add_one hdeleted
    have hdeletedbound : word.getD first 0 ≤ deleted := by
      have := hword.2.1 deleted hdeleted
      rwa [hsame] at this
    refine ⟨by omega, ?_, ?_⟩
    · intro index hindex
      by_cases hbefore : index < deleted
      · have heq : (word.eraseIdx deleted).getD index 0 = word.getD index 0 := by
          unfold List.getD
          rw [List.getElem?_eraseIdx_of_lt hbefore]
        rw [heq]
        exact hword.2.1 index (by omega)
      · have hafter : deleted ≤ index := by omega
        have heq : (word.eraseIdx deleted).getD index 0 = word.getD (index + 1) 0 := by
          unfold List.getD
          rw [List.getElem?_eraseIdx_of_ge hafter]
        rw [heq]
        have hupper := hmax (index + 1) (by omega)
        omega
    · intro pattern hpattern hocc
      apply hword.2.2 pattern hpattern
      obtain ⟨values, hstep, hmem, hsublist, _⟩ := hocc
      exact ⟨values, hstep,
        fun index hpos hbound => (List.eraseIdx_sublist word deleted).mem
          (hmem index hpos hbound),
        hsublist.trans (List.eraseIdx_sublist word deleted), by simp⟩

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Maximum
