/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFivePrepend
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFivePrepend
   mirror-E: none(waiver:prepending-active-gap-rules)
   anchors: []
   utility: none
   digest: Prepending a maximum shifts A sites and keeps exactly decreasing-prefix B sites. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicGaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFivePrepend

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion FishburnBasicPatterns

set_option maxHeartbeats 1200000 in
theorem prepend_site_rules (n : ℕ) (p : List ℕ) (hpositive : 1 ≤ n)
    (hperm : p.Perm (List.range' 1 n)) (hfish : IsFishburn p)
    (site : ℕ) (hsite : site ≤ p.length) :
    (((n + 1) :: p).insertIdx (site + 1) (n + 2) ∈
      avoiders (n + 2) [[1, 3, 2, 4], [1, 4, 2, 3]] ↔
      site ≠ 0 ∧ p.insertIdx site (n + 1) ∈
        avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]]) ∧
    (((n + 1) :: p).insertIdx (site + 1) (n + 2) ∈
      avoiders (n + 2) [[1, 3, 2, 4], [3, 1, 2, 4]] ↔
      site ≠ 0 ∧ p.insertIdx site (n + 1) ∈
        avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] ∧
      ∀ first second, first < second → second < site →
        p.getD second 0 < p.getD first 0) := by
  let child := (n + 1) :: p
  have hmax : ∀ value ∈ p, value < n + 1 := by
    intro value hvalue
    have hm := hperm.mem_iff.mp hvalue
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨offset, hoffset, heq⟩ := hm
    omega
  have hbound : ∀ index, index < p.length → p.getD index 0 < n + 1 := by
    intro index hindex
    rw [List.getD_eq_getElem p 0 hindex]
    exact hmax _ (List.getElem_mem hindex)
  have hmaxchild : ∀ value ∈ child, value < n + 2 := by
    intro value hvalue
    change value ∈ (n + 1) :: p at hvalue
    simp only [List.mem_cons] at hvalue
    rcases hvalue with rfl | hvalue
    · omega
    · have := hmax value hvalue
      omega
  have hchildperm : child.Perm (List.range' 1 (n + 1)) := by
    apply (hperm.cons (n + 1)).trans
    rw [List.range'_concat]
    simpa [Nat.add_comm] using
      (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
  have hchildfish : IsFishburn child := by
    have hf := isFishburn_insertIdx_max_iff p (n + 1) 0 (by omega) hmax
    apply hf.mpr
    exact ⟨hfish, by intro before later hbefore; omega⟩
  have hchildsite : site + 1 ≤ child.length := by simp [child]; omega
  have hat : child.getD 0 0 = n + 1 := rfl
  have hsucc : ∀ index, child.getD (index + 1) 0 = p.getD index 0 := by
    intro index
    simp only [child, List.getD_cons_succ]
  have htail : ∀ index, 0 < index → child.getD index 0 = p.getD (index - 1) 0 := by
    intro index hindex
    obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : index ≠ 0)
    simpa using hsucc previous
  have hparentinsertperm : (p.insertIdx site (n + 1)).Perm (List.range' 1 (n + 1)) := by
    exact (List.perm_insertIdx (n + 1) p hsite).trans hchildperm
  have hchildinsertperm : (child.insertIdx (site + 1) (n + 2)).Perm
      (List.range' 1 (n + 2)) := by
    apply (List.perm_insertIdx (n + 2) child hchildsite).trans
    apply (hchildperm.cons (n + 2)).trans
    have hrange : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
      simpa only [Nat.one_mul, Nat.add_assoc, Nat.reduceAdd,
        show 1 + (n + 1) = n + 2 by omega] using
        (List.range'_concat (s := 1) (n := n + 1) (step := 1))
    rw [hrange]
    simpa using
      (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
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
        have hbad := hsafe 0 (index + 1) (by omega) (by omega) (by simp [child]; omega)
        exact hbad (by rw [hat, hsucc, hentry])
      refine ⟨hnonzero, hfish, ?_⟩
      intro before later hbefore hlater hbound heq
      apply hsafe (before + 1) (later + 1) (by omega) (by omega) (by simp [child]; omega)
      rwa [hsucc, hsucc]
    · rintro ⟨hnonzero, _, hsafe⟩
      refine ⟨hchildfish, ?_⟩
      intro before later hbefore hlater hbound heq
      have hbeforepos : 0 < before := by omega
      have hlaterpos : 0 < later := by omega
      rw [htail before hbeforepos, htail later hlaterpos] at heq
      exact hsafe (before - 1) (later - 1) (by omega) (by omega)
        (by simp only [child, List.length_cons] at hbound; omega) heq
  have hinj : ∀ first second, first < p.length → second < p.length →
      p.getD first 0 = p.getD second 0 → first = second := by
    intro first second hfirst hsecond heq
    exact (List.getD_inj hfirst hsecond (hperm.nodup_iff.mpr (List.nodup_range' 1))).mp heq
  have h132shift :
      (∃ first second third, first < second ∧ second < third ∧ third < site + 1 ∧
        child.getD first 0 < child.getD third 0 ∧
        child.getD third 0 < child.getD second 0) ↔
      (∃ first second third, first < second ∧ second < third ∧ third < site ∧
        p.getD first 0 < p.getD third 0 ∧ p.getD third 0 < p.getD second 0) := by
    constructor
    · rintro ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩
      have hfirst : 0 < first := by
        by_contra hnot
        have heq : first = 0 := by omega
        rw [heq, hat, htail third (by omega)] at hlow
        have := hbound (third - 1) (by omega)
        omega
      rw [htail first hfirst, htail third (by omega)] at hlow
      rw [htail third (by omega), htail second (by omega)] at hhigh
      exact ⟨first - 1, second - 1, third - 1, by omega, by omega, by omega, hlow, hhigh⟩
    · rintro ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩
      refine ⟨first + 1, second + 1, third + 1, by omega, by omega, by omega, ?_, ?_⟩
      · rwa [hsucc, hsucc]
      · rwa [hsucc, hsucc]
  have h142shift :
      (∃ first second third, first < site + 1 ∧ site + 1 ≤ second ∧ second < third ∧
        third < child.length ∧ child.getD first 0 < child.getD second 0 ∧
        child.getD second 0 < child.getD third 0) ↔
      (∃ first second third, first < site ∧ site ≤ second ∧ second < third ∧
        third < p.length ∧ p.getD first 0 < p.getD second 0 ∧
        p.getD second 0 < p.getD third 0) := by
    constructor
    · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
      have hlen : child.length = p.length + 1 := rfl
      have hfirst : 0 < first := by
        by_contra hnot
        have heq : first = 0 := by omega
        rw [heq, hat, htail second (by omega)] at hlow
        have := hbound (second - 1) (by omega)
        omega
      rw [htail first hfirst, htail second (by omega)] at hlow
      rw [htail second (by omega), htail third (by omega)] at hhigh
      exact ⟨first - 1, second - 1, third - 1, by omega, by omega, by omega, by omega,
        hlow, hhigh⟩
    · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
      refine ⟨first + 1, second + 1, third + 1, by omega, by omega, by omega,
        by simp [child]; omega, ?_, ?_⟩
      · rwa [hsucc, hsucc]
      · rwa [hsucc, hsucc]
  have h312shift :
      (∃ first second third, first < second ∧ second < third ∧ third < site + 1 ∧
        child.getD second 0 < child.getD third 0 ∧
        child.getD third 0 < child.getD first 0) ↔
      (∃ first second third, first < second ∧ second < third ∧ third < site ∧
        p.getD second 0 < p.getD third 0 ∧ p.getD third 0 < p.getD first 0) ∨
      ∃ first second, first < second ∧ second < site ∧
        p.getD first 0 < p.getD second 0 := by
    constructor
    · rintro ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩
      by_cases hzero : first = 0
      · right
        rw [htail second (by omega), htail third (by omega)] at hlow
        exact ⟨second - 1, third - 1, by omega, by omega, hlow⟩
      · left
        rw [htail second (by omega), htail third (by omega)] at hlow
        rw [htail third (by omega), htail first (by omega)] at hhigh
        exact ⟨first - 1, second - 1, third - 1, by omega, by omega, by omega, hlow, hhigh⟩
    · rintro (⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ |
        ⟨first, second, hfs, hs, hlow⟩)
      · refine ⟨first + 1, second + 1, third + 1, by omega, by omega, by omega, ?_, ?_⟩
        · rwa [hsucc, hsucc]
        · rwa [hsucc, hsucc]
      · refine ⟨0, first + 1, second + 1, by omega, by omega, by omega, ?_, ?_⟩
        · rwa [hsucc, hsucc]
        · rw [hat, hsucc]
          exact hbound second (by omega)
  have hzero := maximum_pattern_tests n p hperm 0 (by omega)
  have hbase132 : NonnestingDefs.Occurs [1, 3, 2, 4] child ↔
      NonnestingDefs.Occurs [1, 3, 2, 4] p := by
    simpa [child] using hzero.1
  have hbase312 : NonnestingDefs.Occurs [3, 1, 2, 4] child ↔
      NonnestingDefs.Occurs [3, 1, 2, 4] p := by
    simpa [child] using hzero.2.1
  have hbase142 : NonnestingDefs.Occurs [1, 4, 2, 3] child ↔
      NonnestingDefs.Occurs [1, 4, 2, 3] p := by
    simpa [child] using hzero.2.2
  have hold := maximum_pattern_tests n p hperm site hsite
  have hnew := maximum_pattern_tests (n + 1) child hchildperm (site + 1) hchildsite
  have h132 : NonnestingDefs.Occurs [1, 3, 2, 4] (child.insertIdx (site + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [1, 3, 2, 4] (p.insertIdx site (n + 1)) := by
    rw [hnew.1, hold.1, hbase132, h132shift]
  have h142 : NonnestingDefs.Occurs [1, 4, 2, 3] (child.insertIdx (site + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [1, 4, 2, 3] (p.insertIdx site (n + 1)) := by
    rw [hnew.2.2, hold.2.2, hbase142, h142shift]
  have h312 : NonnestingDefs.Occurs [3, 1, 2, 4] (child.insertIdx (site + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [3, 1, 2, 4] (p.insertIdx site (n + 1)) ∨
      ∃ first second, first < second ∧ second < site ∧
        p.getD first 0 < p.getD second 0 := by
    rw [hnew.2.1, hold.2.1, hbase312, h312shift, or_assoc]
  constructor
  · constructor
    · intro hmember
      have hf := hfishshift.mp hmember.2.1
      refine ⟨hf.1, hparentinsertperm, hf.2, ?_⟩
      intro pattern hpattern hocc
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [1, 4, 2, 3] := by
        simpa using hpattern
      rcases hc with rfl | rfl
      · exact hmember.2.2 _ (by simp) (h132.mpr hocc)
      · exact hmember.2.2 _ (by simp) (h142.mpr hocc)
    · rintro ⟨hnonzero, hmember⟩
      refine ⟨hchildinsertperm, hfishshift.mpr ⟨hnonzero, hmember.2.1⟩, ?_⟩
      intro pattern hpattern hocc
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [1, 4, 2, 3] := by
        simpa using hpattern
      rcases hc with rfl | rfl
      · exact hmember.2.2 _ (by simp) (h132.mp hocc)
      · exact hmember.2.2 _ (by simp) (h142.mp hocc)
  · constructor
    · intro hmember
      have hf := hfishshift.mp hmember.2.1
      refine ⟨hf.1, ⟨hparentinsertperm, hf.2, ?_⟩, ?_⟩
      · intro pattern hpattern hocc
        have hc : pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] := by
          simpa using hpattern
        rcases hc with rfl | rfl
        · exact hmember.2.2 _ (by simp) (h132.mpr hocc)
        · exact hmember.2.2 _ (by simp) (h312.mpr (Or.inl hocc))
      · intro first second hfs hs
        have hnot : ¬ p.getD first 0 < p.getD second 0 := by
          intro hlt
          exact hmember.2.2 _ (by simp) (h312.mpr (Or.inr ⟨first, second, hfs, hs, hlt⟩))
        have hne : p.getD first 0 ≠ p.getD second 0 := by
          intro heq
          have := hinj first second (by omega) (by omega) heq
          omega
        omega
    · rintro ⟨hnonzero, hmember, hdecreasing⟩
      refine ⟨hchildinsertperm, hfishshift.mpr ⟨hnonzero, hmember.2.1⟩, ?_⟩
      intro pattern hpattern hocc
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] := by
        simpa using hpattern
      rcases hc with rfl | rfl
      · exact hmember.2.2 _ (by simp) (h132.mp hocc)
      · rcases h312.mp hocc with hprevious | ⟨first, second, hfs, hs, hlt⟩
        · exact hmember.2.2 _ (by simp) hprevious
        · have := hdecreasing first second hfs hs
          omega

end D5.S3.Combinatorics.Fishburn.FishburnTenFivePrepend
