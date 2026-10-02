/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicPrepend
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicPrepend
   mirror-E: none(waiver:prepend-predecessor-and-pattern-witnesses)
   anchors: []
   utility: none
   digest: Prepending a maximum transports positive sites with a decreasing-prefix 3124 guard. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasic2143
import D5.S3.Combinatorics.Fishburn.FishburnBasicPatternTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicPrepend

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasic2143 FishburnBasicPatterns FishburnBasicPatternTransport

theorem prepend_inherited_sites (n : ℕ) (p : List ℕ) (hpositive : 1 ≤ n)
    (hperm : p.Perm (List.range' 1 n)) (hfish : IsFishburn p)
    (patterns : List (List ℕ))
    (hpatterns : ∀ pattern ∈ patterns, pattern = [1, 3, 2, 4] ∨
      pattern = [2, 1, 4, 3] ∨ pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4])
    (site : ℕ) (hsite : site ≤ p.length) :
    ((n + 1) :: p).insertIdx (site + 1) (n + 2) ∈ avoiders (n + 2) patterns ↔
      site ≠ 0 ∧ p.insertIdx site (n + 1) ∈ avoiders (n + 1) patterns ∧
      ([3, 1, 2, 4] ∈ patterns → ∀ first second, first < second → second < site →
        p.getD second 0 < p.getD first 0) := by
  let child := (n + 1) :: p
  have hmax : ∀ value ∈ p, value < n + 1 := by
    intro value hm
    have hrange := hperm.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, hoffset, heq⟩ := hrange
    omega
  have hbound (index : ℕ) (hi : index < p.length) : p.getD index 0 < n + 1 := by
    rw [List.getD_eq_getElem p 0 hi]
    exact hmax _ (List.getElem_mem hi)
  have hmaxchild : ∀ value ∈ child, value < n + 2 := by
    intro value hm
    change value ∈ (n + 1) :: p at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · omega
    · have := hmax value hm
      omega
  have hchildperm : child.Perm (List.range' 1 (n + 1)) := by
    apply (hperm.cons (n + 1)).trans
    rw [List.range'_concat]
    simpa [Nat.add_comm] using
      (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
  have hchildfish : IsFishburn child := by
    apply (isFishburn_insertIdx_max_iff p (n + 1) 0 (by omega) hmax).mpr
    exact ⟨hfish, by intro before later heq; omega⟩
  have hchildsite : site + 1 ≤ child.length := by simp only [child, List.length_cons]; omega
  have hat : child.getD 0 0 = n + 1 := rfl
  have hsucc (index : ℕ) : child.getD (index + 1) 0 = p.getD index 0 := by
    simp only [child, List.getD_cons_succ]
  have htail (index : ℕ) (hi : 0 < index) :
      child.getD index 0 = p.getD (index - 1) 0 := by
    obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : index ≠ 0)
    simpa using hsucc previous
  have hfishshift : IsFishburn (child.insertIdx (site + 1) (n + 2)) ↔
      site ≠ 0 ∧ IsFishburn (p.insertIdx site (n + 1)) := by
    rw [isFishburn_insertIdx_max_iff child (n + 2) (site + 1) hchildsite hmaxchild,
      isFishburn_insertIdx_max_iff p (n + 1) site hsite hmax]
    constructor
    · rintro ⟨_, hsafe⟩
      have hnonzero : site ≠ 0 := by
        intro hzero
        have hnmem : n ∈ p := by
          apply hperm.mem_iff.mpr
          simp only [List.mem_range', Nat.one_mul]
          exact ⟨n - 1, by omega, by omega⟩
        obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hnmem
        have hentry : p.getD index 0 = n := by
          rwa [List.getD_eq_getElem p 0 hindex]
        have hbad := hsafe 0 (index + 1) (by omega) (by omega)
          (by simp only [child, List.length_cons]; omega)
        exact hbad (by rw [hat, hsucc, hentry])
      refine ⟨hnonzero, hfish, ?_⟩
      intro before later hbefore hlater hlaterbound heq
      apply hsafe (before + 1) (later + 1) (by omega) (by omega)
        (by simp only [child, List.length_cons]; omega)
      rwa [hsucc, hsucc]
    · rintro ⟨hnonzero, _, hsafe⟩
      refine ⟨hchildfish, ?_⟩
      intro before later hbefore hlater hlaterbound heq
      rw [htail before (by omega), htail later (by omega)] at heq
      exact hsafe (before - 1) (later - 1) (by omega) (by omega)
        (by simp only [child, List.length_cons] at hlaterbound; omega) heq
  by_cases hzero : site = 0
  · constructor
    · intro hmember
      exact False.elim ((hfishshift.mp hmember.2.1).1 hzero)
    · intro hmember
      exact False.elim (hmember.1 hzero)
  have htransport := maximum_pattern_transport n p hperm 0 site (by omega) hsite
  have htests := maximum_pattern_tests n p hperm 0 (by omega)
  have hbase132 : NonnestingDefs.Occurs [1, 3, 2, 4] child ↔
      NonnestingDefs.Occurs [1, 3, 2, 4] p := by
    simpa [child] using htests.1
  have hbase142 : NonnestingDefs.Occurs [1, 4, 2, 3] child ↔
      NonnestingDefs.Occurs [1, 4, 2, 3] p := by
    simpa [child] using htests.2.2
  have hbase312 : NonnestingDefs.Occurs [3, 1, 2, 4] child ↔
      NonnestingDefs.Occurs [3, 1, 2, 4] p := by
    simpa [child] using htests.2.1
  have hsite132 := maximum_pattern_tests n p hperm site hsite
  have h132 : NonnestingDefs.Occurs [1, 3, 2, 4]
      (child.insertIdx (site + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [1, 3, 2, 4] (p.insertIdx site (n + 1)) := by
    have hs := htransport.1
    simp only [show ¬ site ≤ 0 by omega, if_false, List.insertIdx_zero] at hs
    rw [hbase132, hsite132.1] at hs
    rw [hsite132.1]
    simpa [child, or_assoc] using hs
  have h142 : NonnestingDefs.Occurs [1, 4, 2, 3]
      (child.insertIdx (site + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [1, 4, 2, 3] (p.insertIdx site (n + 1)) := by
    have hs := htransport.2.2
    simp only [show ¬ site ≤ 0 by omega, if_false, List.insertIdx_zero] at hs
    rw [hbase142, hsite132.2.2] at hs
    rw [hsite132.2.2]
    simpa [child, or_assoc] using hs
  have h312 : NonnestingDefs.Occurs [3, 1, 2, 4]
      (child.insertIdx (site + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [3, 1, 2, 4] (p.insertIdx site (n + 1)) ∨
      ∃ first second, first < second ∧ second < site ∧
        p.getD first 0 < p.getD second 0 := by
    have hs := htransport.2.1
    simp only [show ¬ site ≤ 0 by omega, if_false, List.insertIdx_zero] at hs
    rw [hbase312, hsite132.2.1] at hs
    rw [hsite132.2.1]
    simpa [child, or_assoc] using hs
  have hguard2143 :
      (∃ first second third, first < second ∧ second < site + 1 ∧
        site + 1 ≤ third ∧ third < child.length ∧
        child.getD second 0 < child.getD first 0 ∧
        child.getD first 0 < child.getD third 0) ↔
      ∃ first second third, first < second ∧ second < site ∧ site ≤ third ∧
        third < p.length ∧ p.getD second 0 < p.getD first 0 ∧
        p.getD first 0 < p.getD third 0 := by
    constructor
    · rintro ⟨first, second, third, hfs, hs, ht, htb, hlow, hhigh⟩
      have hfirst : 0 < first := by
        by_contra hnot
        have heq : first = 0 := by omega
        rw [heq, hat, htail third (by omega)] at hhigh
        have hb := hbound (third - 1)
          (by simp only [child, List.length_cons] at htb; omega)
        omega
      rw [htail first hfirst, htail second (by omega)] at hlow
      rw [htail first hfirst, htail third (by omega)] at hhigh
      refine ⟨first - 1, second - 1, third - 1, by omega, by omega, by omega,
        ?_, hlow, hhigh⟩
      simp only [child, List.length_cons] at htb
      omega
    · rintro ⟨first, second, third, hfs, hs, ht, htb, hlow, hhigh⟩
      refine ⟨first + 1, second + 1, third + 1, by omega, by omega, by omega,
        by simp only [child, List.length_cons]; omega, ?_, ?_⟩
      · rwa [hsucc, hsucc]
      · rwa [hsucc, hsucc]
  have hbase2143 : NonnestingDefs.Occurs [2, 1, 4, 3] child ↔
      NonnestingDefs.Occurs [2, 1, 4, 3] p := by
    simpa [child] using maximum_2143_test n p hperm 0 (by omega)
  have h2143 : NonnestingDefs.Occurs [2, 1, 4, 3]
      (child.insertIdx (site + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [2, 1, 4, 3] (p.insertIdx site (n + 1)) := by
    rw [maximum_2143_test (n + 1) child hchildperm (site + 1) hchildsite,
      maximum_2143_test n p hperm site hsite, hbase2143, hguard2143]
  have hinj (first second : ℕ) (hf : first < p.length) (hs : second < p.length)
      (heq : p.getD first 0 = p.getD second 0) : first = second :=
    (List.getD_inj hf hs (hperm.nodup_iff.mpr (List.nodup_range' 1))).mp heq
  constructor
  · intro hmember
    have hf := hfishshift.mp hmember.2.1
    refine ⟨hf.1, ⟨?_, hf.2, ?_⟩, ?_⟩
    · exact (List.perm_insertIdx (n + 1) p hsite).trans hchildperm
    · intro pattern hm hocc
      rcases hpatterns pattern hm with rfl | rfl | rfl | rfl
      · exact hmember.2.2 _ hm (h132.mpr hocc)
      · exact hmember.2.2 _ hm (h2143.mpr hocc)
      · exact hmember.2.2 _ hm (h142.mpr hocc)
      · exact hmember.2.2 _ hm (h312.mpr (Or.inl hocc))
    · intro hm first second hfs hs
      have hnot : ¬ p.getD first 0 < p.getD second 0 := by
        intro hlt
        exact hmember.2.2 _ hm (h312.mpr (Or.inr ⟨first, second, hfs, hs, hlt⟩))
      have hne : p.getD first 0 ≠ p.getD second 0 := by
        intro heq
        have := hinj first second (by omega) (by omega) heq
        omega
      omega
  · rintro ⟨hnonzero, hmember, hdecreasing⟩
    refine ⟨?_, hfishshift.mpr ⟨hnonzero, hmember.2.1⟩, ?_⟩
    · apply (List.perm_insertIdx (n + 2) child hchildsite).trans
      apply (hchildperm.cons (n + 2)).trans
      have hrange : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
        simpa only [Nat.one_mul, Nat.add_assoc, Nat.reduceAdd,
          show 1 + (n + 1) = n + 2 by omega] using
          (List.range'_concat (s := 1) (n := n + 1) (step := 1))
      rw [hrange]
      simpa using
        (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
    · intro pattern hm hocc
      rcases hpatterns pattern hm with rfl | rfl | rfl | rfl
      · exact hmember.2.2 _ hm (h132.mp hocc)
      · exact hmember.2.2 _ hm (h2143.mp hocc)
      · exact hmember.2.2 _ hm (h142.mp hocc)
      · rcases h312.mp hocc with hold | ⟨first, second, hfs, hs, hlt⟩
        · exact hmember.2.2 _ hm hold
        · have := hdecreasing hm first second hfs hs
          omega

end D5.S3.Combinatorics.Fishburn.FishburnBasicPrepend
