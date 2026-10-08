/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207LeftChildren
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207LeftChildren
   mirror-E: none(waiver:left-active-child-construction)
   anchors: []
   utility: none
   digest: Terminal descent and repeat witnesses determine every left child active value. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Append

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftChildren

open D5.S3.Combinatorics.Nonnesting InversionSeqOccurs InversionSeq207Append

theorem left_children_exact (word : List ℕ) (value maximumIndex : ℕ)
    (hword : word ∈ InversionSeqDefs.avoiders word.length
      [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]])
    (hvalue : word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1)
      [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]])
    (hmaximumIndex : maximumIndex < word.length)
    (hmaximum : ∀ index < word.length,
      word.getD index 0 ≤ word.getD maximumIndex 0) :
    (∀ earlier occurrence : ℕ, earlier < occurrence → occurrence < word.length →
      word.getD occurrence 0 = value → word.getD earlier 0 ≤ value) ∧
    (∀ candidate : ℕ,
      (word ++ [value]) ++ [candidate] ∈ InversionSeqDefs.avoiders (word.length + 2)
        [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] ↔
      candidate ≤ word.length + 1 ∧
      ((value < word.getD maximumIndex 0 ∧
          (word.getD maximumIndex 0 < candidate ∨
            (candidate < value ∧ value ∉ word ∧
              word ++ [candidate] ∈ InversionSeqDefs.avoiders (word.length + 1)
                [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]))) ∨
        (value = word.getD maximumIndex 0 ∧ value ≤ candidate) ∨
        (word.getD maximumIndex 0 < value ∧
          (candidate ≤ word.getD maximumIndex 0 →
            word ++ [candidate] ∈ InversionSeqDefs.avoiders (word.length + 1)
              [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]])))) := by
  have hget (index : ℕ) (hindex : index < word.length) :
      (word ++ [value]).getD index 0 = word.getD index 0 :=
    List.getD_append word [value] 0 index hindex
  have hlast : (word ++ [value]).getD word.length 0 = value := by
    rw [List.getD_append_right word [value] 0 word.length le_rfl]
    simp
  have hmem (entry : ℕ) :
      entry ∈ word ↔ ∃ index, index < word.length ∧ word.getD index 0 = entry := by
    constructor
    · intro hentry
      obtain ⟨index, hindex, heq⟩ := List.mem_iff_getElem.mp hentry
      exact ⟨index, hindex, by simpa [List.getD, hindex] using heq⟩
    · rintro ⟨index, hindex, heq⟩
      have hentry := List.getElem_mem (l := word) (n := index) hindex
      have heqEntry : word[index] = entry := by simpa [List.getD, hindex] using heq
      rwa [heqEntry] at hentry
  have hceiling (entries : List ℕ) (bound : ℕ) :
      repeatedCeiling entries ≤ bound ↔
      ∀ first second : ℕ, first < second → second < entries.length →
        entries.getD first 0 = entries.getD second 0 → entries.getD second 0 ≤ bound := by
    simp only [repeatedCeiling, Finset.sup_le_iff, Finset.mem_range]
    constructor
    · intro hbound first second hfirst hsecond heq
      have hentry := hbound second hsecond first hfirst
      rwa [if_pos heq] at hentry
    · intro hbound second hsecond first hfirst
      split_ifs with heq
      · exact hbound first second hfirst hsecond heq
      · exact Nat.zero_le bound
  have hceilingMax : repeatedCeiling word ≤ word.getD maximumIndex 0 := by
    apply (hceiling word _).mpr
    intro first second hfirst hsecond heq
    exact hmaximum second hsecond
  have hmaximumBound : word.getD maximumIndex 0 ≤ maximumIndex :=
    hword.2.1 maximumIndex hmaximumIndex
  have hmaxmem : word.getD maximumIndex 0 ∈ word :=
    (hmem _).mpr ⟨maximumIndex, hmaximumIndex, rfl⟩
  have hactive := (left_append_iff word value hword).mp hvalue
  have hnewRepeat (candidate : ℕ) :
      repeatedCeiling (word ++ [value]) ≤ candidate ↔
      repeatedCeiling word ≤ candidate ∧ (value ∈ word → value ≤ candidate) := by
    rw [hceiling]
    constructor
    · intro hbound
      constructor
      · apply (hceiling word _).mpr
        intro first second hfirst hsecond heq
        have hfirstlen : first < word.length := by omega
        simpa only [hget second hsecond] using hbound first second hfirst
          (by simp; omega) (by rwa [hget first hfirstlen, hget second hsecond])
      · intro hused
        obtain ⟨index, hindex, heq⟩ := (hmem value).mp hused
        have hboundLast := hbound index word.length hindex (by simp)
          (by rw [hget index hindex, hlast]; exact heq)
        simpa only [hlast] using hboundLast
    · rintro ⟨hold, hused⟩ first second hfirst hsecond heq
      have hsecondlen : second < word.length + 1 := by simpa using hsecond
      by_cases hprefix : second < word.length
      · rw [hget first (by omega), hget second hprefix] at heq
        rw [hget second hprefix]
        exact (hceiling word _).mp hold first second hfirst hprefix heq
      · have heqIndex : second = word.length := by omega
        subst second
        rw [hget first hfirst, hlast] at heq
        rw [hlast]
        exact hused ((hmem value).mpr ⟨first, hfirst, heq⟩)
  have hnewDescent (candidate : ℕ) :
      (∀ first second : ℕ, first < second → second < (word ++ [value]).length →
        (word ++ [value]).getD second 0 < (word ++ [value]).getD first 0 →
        candidate < (word ++ [value]).getD second 0 ∨
          (word ++ [value]).getD first 0 < candidate) ↔
      (∀ first second : ℕ, first < second → second < word.length →
        word.getD second 0 < word.getD first 0 →
        candidate < word.getD second 0 ∨ word.getD first 0 < candidate) ∧
      (value < word.getD maximumIndex 0 →
        candidate < value ∨ word.getD maximumIndex 0 < candidate) := by
    constructor
    · intro hbound
      constructor
      · intro first second hfirst hsecond hdescent
        simpa only [hget first (by omega), hget second hsecond] using
          hbound first second hfirst (by simp; omega)
            (by rwa [hget first (by omega), hget second hsecond])
      · intro hlow
        simpa only [hget maximumIndex hmaximumIndex, hlast] using
          hbound maximumIndex word.length hmaximumIndex (by simp)
            (by rwa [hget maximumIndex hmaximumIndex, hlast])
    · rintro ⟨hold, hnew⟩ first second hfirst hsecond hdescent
      have hsecondlen : second < word.length + 1 := by simpa using hsecond
      by_cases hprefix : second < word.length
      · rw [hget first (by omega), hget second hprefix] at hdescent ⊢
        exact hold first second hfirst hprefix hdescent
      · have heqIndex : second = word.length := by omega
        subst second
        rw [hget first hfirst, hlast] at hdescent ⊢
        have hfirstMax := hmaximum first hfirst
        rcases hnew (by omega) with hbelow | habove
        · exact Or.inl hbelow
        · exact Or.inr (by omega)
  have hchild (candidate : ℕ) :
      (word ++ [value]) ++ [candidate] ∈ InversionSeqDefs.avoiders (word.length + 2)
        [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] ↔
      repeatedCeiling word ≤ candidate ∧ candidate ≤ word.length + 1 ∧
      (value ∈ word → value ≤ candidate) ∧
      (∀ first second : ℕ, first < second → second < word.length →
        word.getD second 0 < word.getD first 0 →
        candidate < word.getD second 0 ∨ word.getD first 0 < candidate) ∧
      (value < word.getD maximumIndex 0 →
        candidate < value ∨ word.getD maximumIndex 0 < candidate) := by
    have happ := left_append_iff (word ++ [value]) candidate (by simpa using hvalue)
    have hdescent := hnewDescent candidate
    simp only [List.length_append, List.length_singleton] at happ
    simp only [List.length_append, List.length_singleton] at hdescent
    rw [show word.length + 1 + 1 = word.length + 2 by omega,
      hnewRepeat, hdescent] at happ
    exact happ.trans (by tauto)
  have hhigh (candidate : ℕ) (hhigh : word.getD maximumIndex 0 < candidate) :
      repeatedCeiling word ≤ candidate ∧
      (∀ first second : ℕ, first < second → second < word.length →
        word.getD second 0 < word.getD first 0 →
        candidate < word.getD second 0 ∨ word.getD first 0 < candidate) := by
    refine ⟨by omega, ?_⟩
    intro first second hfirst hsecond hdescent
    have hfirstMax := hmaximum first (by omega)
    exact Or.inr (by omega)
  constructor
  · intro earlier occurrence hearlier hoccurrence heq
    by_contra hnot
    apply hvalue.2.2 [2, 1, 1] (by simp)
    apply (occurs_three_iff 2 1 1 (word ++ [value])
      (by omega) (by omega) (by omega) (by omega)).mpr
    refine ⟨earlier, occurrence, word.length, hearlier, hoccurrence, by simp, ?_⟩
    rw [hget earlier (by omega), hget occurrence hoccurrence, hlast]
    omega
  · intro candidate
    rw [hchild candidate]
    constructor
    · rintro ⟨hrepeat, hbound, hused, hdescent, hnew⟩
      refine ⟨hbound, ?_⟩
      rcases lt_trichotomy value (word.getD maximumIndex 0) with hlow | heq | hhigh
      · left
        refine ⟨hlow, ?_⟩
        rcases hnew hlow with hbelow | habove
        · right
          refine ⟨hbelow, ?_, ?_⟩
          · intro hmem
            have := hused hmem
            omega
          · apply (left_append_iff word candidate hword).mpr
            exact ⟨hrepeat, by omega, hdescent⟩
        · exact Or.inl habove
      · exact Or.inr (Or.inl ⟨heq, by have := hused (heq ▸ hmaxmem); omega⟩)
      · right; right
        refine ⟨hhigh, ?_⟩
        intro hbelow
        apply (left_append_iff word candidate hword).mpr
        exact ⟨hrepeat, by omega, hdescent⟩
    · rintro ⟨hbound, hcase⟩
      rcases hcase with ⟨hlow, habove | ⟨hbelow, hunused, hold⟩⟩ |
          ⟨heq, hbelow⟩ | ⟨hhighValue, hold⟩
      · obtain ⟨hrepeat, hdescent⟩ := hhigh candidate habove
        exact ⟨hrepeat, hbound, by intros; omega, hdescent, by intros; omega⟩
      · obtain ⟨hrepeat, _, hdescent⟩ := (left_append_iff word candidate hword).mp hold
        exact ⟨hrepeat, hbound, fun hused => False.elim (hunused hused), hdescent,
          fun _ => Or.inl hbelow⟩
      · have hmaxbelow : word.getD maximumIndex 0 ≤ candidate := by omega
        refine ⟨by omega, hbound, by intros; omega, ?_, by intros; omega⟩
        intro first second hfirst hsecond hdescent
        have hsecondMax := hmaximum second hsecond
        rcases hactive.2.2 first second hfirst hsecond hdescent with hbelow | habove
        · omega
        · exact Or.inr (by omega)
      · have hunused : value ∉ word := by
          intro hused
          obtain ⟨index, hindex, heq⟩ := (hmem value).mp hused
          have := hmaximum index hindex
          omega
        have hprior : repeatedCeiling word ≤ candidate ∧
            (∀ first second : ℕ, first < second → second < word.length →
              word.getD second 0 < word.getD first 0 →
              candidate < word.getD second 0 ∨ word.getD first 0 < candidate) := by
          by_cases hbelow : candidate ≤ word.getD maximumIndex 0
          · obtain ⟨hrepeat, _, hdescent⟩ :=
              (left_append_iff word candidate hword).mp (hold hbelow)
            exact ⟨hrepeat, hdescent⟩
          · exact hhigh candidate (by omega)
        exact ⟨hprior.1, hbound, fun hused => False.elim (hunused hused), hprior.2,
          by intros; omega⟩

end D5.S3.Combinatorics.InversionSeq.InversionSeq207LeftChildren
