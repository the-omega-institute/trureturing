/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Append
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Append
   mirror-E: none(waiver:append-pattern-witnesses)
   anchors: [mathlib/module/Mathlib.Data.Finset.Lattice.Fold]
   utility: none
   digest: New terminal pattern witnesses give the exact append criteria for both classes. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Append

open D5.S3.Combinatorics.Nonnesting InversionSeqOccurs

def repeatedCeiling (word : List ℕ) : ℕ :=
  (Finset.range word.length).sup fun second =>
    (Finset.range second).sup fun first =>
      if word.getD first 0 = word.getD second 0 then word.getD second 0 else 0

def secondLargest (word : List ℕ) : ℕ :=
  (Finset.range word.length).sup fun second =>
    (Finset.range second).sup fun first => min (word.getD first 0) (word.getD second 0)

theorem left_append_iff (word : List ℕ) (value : ℕ)
    (hword : word ∈ InversionSeqDefs.avoiders word.length
      [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]) :
    word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1)
      [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]] ↔
      repeatedCeiling word ≤ value ∧ value ≤ word.length ∧
      ∀ first second : ℕ, first < second → second < word.length →
        word.getD second 0 < word.getD first 0 →
        value < word.getD second 0 ∨ word.getD first 0 < value := by
  have hbad (entries : List ℕ) :
      (∃ pattern ∈ [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]],
        NonnestingDefs.Occurs pattern entries) ↔
      ∃ first second third : ℕ,
        first < second ∧ second < third ∧ third < entries.length ∧
        ((entries.getD first 0 = entries.getD second 0 ∧
          entries.getD third 0 < entries.getD second 0) ∨
        (entries.getD second 0 < entries.getD first 0 ∧
          entries.getD second 0 ≤ entries.getD third 0 ∧
          entries.getD third 0 ≤ entries.getD first 0)) := by
    constructor
    · rintro ⟨pattern, hpattern, hocc⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl | rfl
      · obtain ⟨first, second, third, hfirst, hsecond, hthird, hrels⟩ :=
          (occurs_three_iff 2 1 1 entries (by omega) (by omega) (by omega)
            (by omega)).mp hocc
        exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
      · obtain ⟨first, second, third, hfirst, hsecond, hthird, hrels⟩ :=
          (occurs_three_iff 2 1 2 entries (by omega) (by omega) (by omega)
            (by omega)).mp hocc
        exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
      · obtain ⟨first, second, third, hfirst, hsecond, hthird, hrels⟩ :=
          (occurs_three_iff 2 2 1 entries (by omega) (by omega) (by omega)
            (by omega)).mp hocc
        exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
      · obtain ⟨first, second, third, hfirst, hsecond, hthird, hrels⟩ :=
          (occurs_three_iff 3 1 2 entries (by omega) (by omega) (by omega)
            (by omega)).mp hocc
        exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
    · rintro ⟨first, second, third, hfirst, hsecond, hthird, hequal | hdescent⟩
      · refine ⟨[2, 2, 1], by simp, ?_⟩
        apply (occurs_three_iff 2 2 1 entries (by omega) (by omega) (by omega)
          (by omega)).mpr
        exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
      · by_cases hbottom : entries.getD third 0 = entries.getD second 0
        · refine ⟨[2, 1, 1], by simp, ?_⟩
          apply (occurs_three_iff 2 1 1 entries (by omega) (by omega) (by omega)
            (by omega)).mpr
          exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
        · by_cases htop : entries.getD third 0 = entries.getD first 0
          · refine ⟨[2, 1, 2], by simp, ?_⟩
            apply (occurs_three_iff 2 1 2 entries (by omega) (by omega) (by omega)
              (by omega)).mpr
            exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
          · refine ⟨[3, 1, 2], by simp, ?_⟩
            apply (occurs_three_iff 3 1 2 entries (by omega) (by omega) (by omega)
              (by omega)).mpr
            exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
  have hget (index : ℕ) (hindex : index < word.length) :
      (word ++ [value]).getD index 0 = word.getD index 0 :=
    List.getD_append word [value] 0 index hindex
  have hlast : (word ++ [value]).getD word.length 0 = value := by
    rw [List.getD_append_right word [value] 0 word.length le_rfl]
    simp
  have hinv : InversionSeqDefs.IsInversionSeq (word ++ [value]) ↔
      value ≤ word.length := by
    constructor
    · intro hbound
      have := hbound word.length (by simp)
      rwa [hlast] at this
    · intro hbound index hindex
      by_cases hprefix : index < word.length
      · rw [hget index hprefix]
        exact hword.2.1 index hprefix
      · have heq : index = word.length := by simp only [List.length_append,
          List.length_cons, List.length_nil] at hindex; omega
        subst index
        rwa [hlast]
  have hceiling : repeatedCeiling word ≤ value ↔
      ∀ first second : ℕ, first < second → second < word.length →
        word.getD first 0 = word.getD second 0 → word.getD second 0 ≤ value := by
    simp only [repeatedCeiling, Finset.sup_le_iff, Finset.mem_range]
    constructor
    · intro hbound first second hfirst hsecond heq
      have hentry := hbound second hsecond first hfirst
      rwa [if_pos heq] at hentry
    · intro hbound second hsecond first hfirst
      split_ifs with heq
      · exact hbound first second hfirst hsecond heq
      · exact Nat.zero_le value
  constructor
  · intro happ
    have hno : ¬ ∃ pattern ∈ [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]],
        NonnestingDefs.Occurs pattern (word ++ [value]) := by
      rintro ⟨pattern, hpattern, hocc⟩
      exact happ.2.2 pattern hpattern hocc
    refine ⟨hceiling.mpr ?_, hinv.mp happ.2.1, ?_⟩
    · intro first second hfirst hsecond heq
      by_contra hbound
      apply hno
      apply (hbad (word ++ [value])).mpr
      refine ⟨first, second, word.length, hfirst, hsecond, by simp, Or.inl ?_⟩
      rw [hget first (by omega), hget second hsecond, hlast]
      exact ⟨heq, by omega⟩
    · intro first second hfirst hsecond hdescent
      by_contra houtside
      apply hno
      apply (hbad (word ++ [value])).mpr
      refine ⟨first, second, word.length, hfirst, hsecond, by simp, Or.inr ?_⟩
      rw [hget first (by omega), hget second hsecond, hlast]
      exact ⟨hdescent, by omega⟩
  · rintro ⟨hbound, hvalue, houtside⟩
    refine ⟨by simp, hinv.mpr hvalue, ?_⟩
    intro pattern hpattern hocc
    obtain ⟨first, second, third, hfirst, hsecond, hthird, hcase⟩ :=
      (hbad (word ++ [value])).mp ⟨pattern, hpattern, hocc⟩
    by_cases hprefix : third < word.length
    · have hbadprefix := (hbad word).mpr
        ⟨first, second, third, hfirst, hsecond, hprefix, by
          rwa [hget first (by omega), hget second (by omega),
            hget third hprefix] at hcase⟩
      obtain ⟨pattern, hpattern, hocc⟩ := hbadprefix
      exact hword.2.2 pattern hpattern hocc
    · have heq : third = word.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hthird
        omega
      subst third
      rw [hget first (by omega), hget second hsecond, hlast] at hcase
      rcases hcase with hequal | hdescent
      · have := hceiling.mp hbound first second hfirst hsecond hequal.1
        omega
      · have := houtside first second hfirst hsecond hdescent.1
        omega

theorem right_append_iff (word : List ℕ) (value : ℕ)
    (hword : word ∈ InversionSeqDefs.avoiders word.length
      [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]]) :
    word ++ [value] ∈ InversionSeqDefs.avoiders (word.length + 1)
      [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]] ↔
      secondLargest word ≤ value ∧ value ≤ word.length ∧
      ∀ first second : ℕ, first < second → second < word.length →
        word.getD second 0 < word.getD first 0 → word.getD first 0 ≠ value := by
  have hbad (entries : List ℕ) :
      (∃ pattern ∈ [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]],
        NonnestingDefs.Occurs pattern entries) ↔
      ∃ first second third : ℕ,
        first < second ∧ second < third ∧ third < entries.length ∧
        ((entries.getD third 0 < entries.getD first 0 ∧
          entries.getD third 0 < entries.getD second 0) ∨
        (entries.getD first 0 = entries.getD third 0 ∧
          entries.getD second 0 < entries.getD first 0)) := by
    constructor
    · rintro ⟨pattern, hpattern, hocc⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl | rfl
      · obtain ⟨first, second, third, hfirst, hsecond, hthird, hrels⟩ :=
          (occurs_three_iff 2 1 2 entries (by omega) (by omega) (by omega)
            (by omega)).mp hocc
        exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
      · obtain ⟨first, second, third, hfirst, hsecond, hthird, hrels⟩ :=
          (occurs_three_iff 2 2 1 entries (by omega) (by omega) (by omega)
            (by omega)).mp hocc
        exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
      · obtain ⟨first, second, third, hfirst, hsecond, hthird, hrels⟩ :=
          (occurs_three_iff 2 3 1 entries (by omega) (by omega) (by omega)
            (by omega)).mp hocc
        exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
      · obtain ⟨first, second, third, hfirst, hsecond, hthird, hrels⟩ :=
          (occurs_three_iff 3 2 1 entries (by omega) (by omega) (by omega)
            (by omega)).mp hocc
        exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
    · rintro ⟨first, second, third, hfirst, hsecond, hthird, hgreater | hdescent⟩
      · rcases lt_trichotomy (entries.getD first 0) (entries.getD second 0) with
          hlt | heq | hgt
        · refine ⟨[2, 3, 1], by simp, ?_⟩
          apply (occurs_three_iff 2 3 1 entries (by omega) (by omega) (by omega)
            (by omega)).mpr
          exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
        · refine ⟨[2, 2, 1], by simp, ?_⟩
          apply (occurs_three_iff 2 2 1 entries (by omega) (by omega) (by omega)
            (by omega)).mpr
          exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
        · refine ⟨[3, 2, 1], by simp, ?_⟩
          apply (occurs_three_iff 3 2 1 entries (by omega) (by omega) (by omega)
            (by omega)).mpr
          exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
      · refine ⟨[2, 1, 2], by simp, ?_⟩
        apply (occurs_three_iff 2 1 2 entries (by omega) (by omega) (by omega)
          (by omega)).mpr
        exact ⟨first, second, third, hfirst, hsecond, hthird, by omega⟩
  have hget (index : ℕ) (hindex : index < word.length) :
      (word ++ [value]).getD index 0 = word.getD index 0 :=
    List.getD_append word [value] 0 index hindex
  have hlast : (word ++ [value]).getD word.length 0 = value := by
    rw [List.getD_append_right word [value] 0 word.length le_rfl]
    simp
  have hinv : InversionSeqDefs.IsInversionSeq (word ++ [value]) ↔
      value ≤ word.length := by
    constructor
    · intro hbound
      have := hbound word.length (by simp)
      rwa [hlast] at this
    · intro hbound index hindex
      by_cases hprefix : index < word.length
      · rw [hget index hprefix]
        exact hword.2.1 index hprefix
      · have heq : index = word.length := by simp only [List.length_append,
          List.length_cons, List.length_nil] at hindex; omega
        subst index
        rwa [hlast]
  have hsecondBound : secondLargest word ≤ value ↔
      ∀ first second : ℕ, first < second → second < word.length →
        word.getD first 0 ≤ value ∨ word.getD second 0 ≤ value := by
    simp only [secondLargest, Finset.sup_le_iff, Finset.mem_range, min_le_iff]
    constructor
    · intro hbound first second hfirst hsecond
      exact hbound second hsecond first hfirst
    · intro hbound second hsecond first hfirst
      exact hbound first second hfirst hsecond
  constructor
  · intro happ
    have hno : ¬ ∃ pattern ∈ [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]],
        NonnestingDefs.Occurs pattern (word ++ [value]) := by
      rintro ⟨pattern, hpattern, hocc⟩
      exact happ.2.2 pattern hpattern hocc
    refine ⟨hsecondBound.mpr ?_, hinv.mp happ.2.1, ?_⟩
    · intro first second hfirst hsecond
      by_contra hbound
      apply hno
      apply (hbad (word ++ [value])).mpr
      refine ⟨first, second, word.length, hfirst, hsecond, by simp, Or.inl ?_⟩
      rw [hget first (by omega), hget second hsecond, hlast]
      constructor <;> omega
    · intro first second hfirst hsecond hdescent heq
      apply hno
      apply (hbad (word ++ [value])).mpr
      refine ⟨first, second, word.length, hfirst, hsecond, by simp, Or.inr ?_⟩
      rw [hget first (by omega), hget second hsecond, hlast]
      exact ⟨heq, hdescent⟩
  · rintro ⟨hbound, hvalue, htop⟩
    refine ⟨by simp, hinv.mpr hvalue, ?_⟩
    intro pattern hpattern hocc
    obtain ⟨first, second, third, hfirst, hsecond, hthird, hcase⟩ :=
      (hbad (word ++ [value])).mp ⟨pattern, hpattern, hocc⟩
    by_cases hprefix : third < word.length
    · have hbadprefix := (hbad word).mpr
        ⟨first, second, third, hfirst, hsecond, hprefix, by
          rwa [hget first (by omega), hget second (by omega),
            hget third hprefix] at hcase⟩
      obtain ⟨pattern, hpattern, hocc⟩ := hbadprefix
      exact hword.2.2 pattern hpattern hocc
    · have heq : third = word.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hthird
        omega
      subst third
      rw [hget first (by omega), hget second hsecond, hlast] at hcase
      rcases hcase with hgreater | hdescent
      · have := hsecondBound.mp hbound first second hfirst hsecond
        omega
      · exact htop first second hfirst hsecond hdescent.2 hdescent.1

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Append
