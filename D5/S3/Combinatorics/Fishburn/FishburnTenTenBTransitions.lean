/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenBTransitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenBTransitions
   mirror-E: none(waiver:classical-b-active-slot-transition)
   anchors: []
   utility: none
   digest: New maximum witnesses determine the internal and append B active-slot transitions. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicClassicalPatterns
import D5.S3.Combinatorics.Fishburn.FishburnBasicPatterns
import D5.S3.Combinatorics.Fishburn.FishburnBasic2143
import D5.S3.Combinatorics.Fishburn.FishburnClassicalDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenBTransitions

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs
open FishburnBasicClassicalPatterns FishburnBasicPatterns FishburnBasic2143

set_option maxHeartbeats 1600000 in
theorem b_internal_transition (n : ℕ) (p : List ℕ)
    (hmember : p ∈ classicalAvoiders n [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]])
    (site : ℕ) (hsite : site < n)
    (hactive : p.insertIdx site (n + 1) ∈
      classicalAvoiders (n + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]])
    (gap : ℕ) (hgap : gap ≤ n + 1) :
    (p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈
        classicalAvoiders (n + 2) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] ↔
      gap = site + 1 ∨ gap = site + 2 ∧ p.insertIdx (site + 1) (n + 1) ∈
        classicalAvoiders (n + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] := by
  have hcriteria (size : ℕ) (word : List ℕ)
      (hm : word ∈ classicalAvoiders size [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]])
      (cut : ℕ) (hc : cut ≤ word.length) :
      word.insertIdx cut (size + 1) ∈
          classicalAvoiders (size + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] ↔
        (∀ first second, cut ≤ first → first < second → second < word.length →
          word.getD first 0 ≤ word.getD second 0) ∧
        (∀ first second third, first < second → second < third → third < cut →
          word.getD second 0 < word.getD third 0 →
          word.getD first 0 ≤ word.getD third 0) ∧
        (∀ first second third, first < second → second < cut → cut ≤ third →
          third < word.length → word.getD second 0 < word.getD first 0 →
          word.getD third 0 ≤ word.getD first 0) := by
    have h321 := (maximum_classical_pattern_tests size word hm.1 cut hc).1
    have h3124 := (maximum_pattern_tests size word hm.1 cut hc).2.1
    have h2143 := maximum_2143_test size word hm.1 cut hc
    constructor
    · intro hchild
      refine ⟨?_, ?_, ?_⟩
      · intro first second hf hfs hb
        by_contra hnot
        apply hchild.2 [3, 2, 1] (by simp)
        exact h321.mpr (Or.inr ⟨first, second, hf, hfs, hb, by omega⟩)
      · intro first second third hfs hst ht hlt
        by_contra hnot
        apply hchild.2 [3, 1, 2, 4] (by simp)
        exact h3124.mpr (Or.inr ⟨first, second, third, hfs, hst, ht, hlt, by omega⟩)
      · intro first second third hfs hs ht hb hlt
        by_contra hnot
        apply hchild.2 [2, 1, 4, 3] (by simp)
        exact h2143.mpr (Or.inr ⟨first, second, third, hfs, hs, ht, hb, hlt, by omega⟩)
    · rintro ⟨hright, hleft, hcross⟩
      refine ⟨?_, ?_⟩
      · apply (List.perm_insertIdx (size + 1) word hc).trans
        apply (hm.1.cons (size + 1)).trans
        rw [List.range'_concat]
        simpa [Nat.add_comm] using
          (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
      · intro pattern hpattern hocc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl | rfl
        · rcases h321.mp hocc with hocc | ⟨first, second, hf, hfs, hb, hlt⟩
          · exact hm.2 [3, 2, 1] (by simp) hocc
          · have := hright first second hf hfs hb
            omega
        · rcases h2143.mp hocc with hocc |
            ⟨first, second, third, hfs, hs, ht, hb, hlt, hgt⟩
          · exact hm.2 [2, 1, 4, 3] (by simp) hocc
          · have := hcross first second third hfs hs ht hb hlt
            omega
        · rcases h3124.mp hocc with hocc |
            ⟨first, second, third, hfs, hst, ht, hlt, hgt⟩
          · exact hm.2 [3, 1, 2, 4] (by simp) hocc
          · have := hleft first second third hfs hst ht hlt
            omega
  have hlen : p.length = n := by simpa using hmember.1.length_eq
  have hsitebound : site ≤ p.length := by omega
  let child := p.insertIdx site (n + 1)
  have hchildlen : child.length = n + 1 := by
    rw [List.length_insertIdx_of_le_length hsitebound, hlen]
  have hbound (index : ℕ) (hi : index < n) : p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 (by omega)]
      exact List.getElem_mem _
    have hrange := hmember.1.mem_iff.mp hm
    simp only [List.mem_range'_1] at hrange
    omega
  have hne (first second : ℕ) (hf : first < n) (hs : second < n)
      (hneq : first ≠ second) : p.getD first 0 ≠ p.getD second 0 := by
    intro heq
    exact hneq ((List.getD_inj (by omega) (by omega)
      (hmember.1.nodup_iff.mpr (List.nodup_range' 1))).mp heq)
  have hbefore (index : ℕ) (hi : index < site) :
      child.getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
      List.getD_eq_getElem p 0 (by omega)]
  have hat : child.getD site 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  let lower := fun index : ℕ => if index < site then index else index - 1
  let lift := fun index : ℕ => if index < site then index else index + 1
  have hlowerbound (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
      lower index < n := by dsimp [lower]; split_ifs <;> omega
  have hlowerentry (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
      child.getD index 0 = p.getD (lower index) 0 := by
    dsimp [lower]
    split_ifs with hlt
    · exact hbefore index hlt
    · rw [List.getD_eq_getElem child 0 hi, List.getElem_insertIdx_of_gt (by omega),
        List.getD_eq_getElem p 0 (by omega)]
  have hlowermono (first second : ℕ) (hlt : first < second)
      (hf : first ≠ site) (hs : second ≠ site) : lower first < lower second := by
    dsimp [lower]; split_ifs <;> omega
  have hliftbound (index : ℕ) (hi : index < n) : lift index < child.length := by
    dsimp [lift]; split_ifs <;> omega
  have hliftentry (index : ℕ) (hi : index < n) :
      child.getD (lift index) 0 = p.getD index 0 := by
    dsimp [lift]
    split_ifs with hlt
    · exact hbefore index hlt
    · rw [List.getD_eq_getElem child 0 (by omega),
        List.getElem_insertIdx_of_gt (by omega), List.getD_eq_getElem p 0 (by omega)]
      simp only [Nat.add_sub_cancel]
  have hliftmono (first second : ℕ) (hlt : first < second) : lift first < lift second := by
    dsimp [lift]; split_ifs <;> omega
  obtain ⟨hright, hleft, hcross⟩ := (hcriteria n p hmember site hsitebound).mp hactive
  have hfirst : child.insertIdx (site + 1) (n + 2) ∈
      classicalAvoiders (n + 2) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] := by
    apply (hcriteria (n + 1) child hactive (site + 1) (by omega)).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro first second hf hfs hb
      rw [hlowerentry first (by omega) (by omega), hlowerentry second hb (by omega)]
      apply hright (lower first) (lower second)
      · dsimp [lower]; split_ifs <;> omega
      · exact hlowermono first second hfs (by omega) (by omega)
      · have := hlowerbound second hb (by omega)
        omega
    · intro first second third hfs hst ht hlt
      by_cases heq : third = site
      · subst third
        rw [hbefore first (by omega), hat]
        have := hbound first (by omega)
        omega
      · rw [hbefore second (by omega), hbefore third (by omega)] at hlt
        rw [hbefore first (by omega), hbefore third (by omega)]
        exact hleft first second third hfs hst (by omega) hlt
    · intro first second third hfs hs ht hb hlt
      by_cases heq : second = site
      · subst second
        rw [hat, hbefore first hfs] at hlt
        have := hbound first (by omega)
        omega
      by_cases hfirsteq : first = site
      · omega
      rw [hbefore second (by omega), hbefore first (by omega)] at hlt
      rw [hlowerentry third hb (by omega), hbefore first (by omega)]
      apply hcross first second (lower third) hfs (by omega)
      · dsimp [lower]; split_ifs <;> omega
      · have := hlowerbound third hb (by omega)
        omega
      · exact hlt
  have hsecond : child.insertIdx (site + 2) (n + 2) ∈
        classicalAvoiders (n + 2) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] ↔
      p.insertIdx (site + 1) (n + 1) ∈
        classicalAvoiders (n + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] := by
    rw [hcriteria (n + 1) child hactive (site + 2) (by omega),
      hcriteria n p hmember (site + 1) (by omega)]
    constructor
    · rintro ⟨hchildright, hchildleft, hchildcross⟩
      refine ⟨?_, ?_, ?_⟩
      · intro first second hf hfs hb
        have hh := hchildright (lift first) (lift second)
          (by dsimp [lift]; split_ifs <;> omega) (hliftmono first second hfs)
          (hliftbound second (by omega))
        rwa [hliftentry first (by omega), hliftentry second (by omega)] at hh
      · intro first second third hfs hst ht hlt
        have hh := hchildleft (lift first) (lift second) (lift third)
          (hliftmono first second hfs) (hliftmono second third hst)
          (by dsimp [lift]; split_ifs <;> omega)
        rw [hliftentry second (by omega), hliftentry third (by omega),
          hliftentry first (by omega)] at hh
        exact hh hlt
      · intro first second third hfs hs ht hb hlt
        have hh := hchildcross (lift first) (lift second) (lift third)
          (hliftmono first second hfs) (by dsimp [lift]; split_ifs <;> omega)
          (by dsimp [lift]; split_ifs <;> omega) (hliftbound third (by omega))
        rw [hliftentry second (by omega), hliftentry first (by omega),
          hliftentry third (by omega)] at hh
        exact hh hlt
    · rintro ⟨hparentright, hparentleft, hparentcross⟩
      refine ⟨?_, ?_, ?_⟩
      · intro first second hf hfs hb
        rw [hlowerentry first (by omega) (by omega), hlowerentry second hb (by omega)]
        apply hparentright (lower first) (lower second)
        · dsimp [lower]; split_ifs <;> omega
        · exact hlowermono first second hfs (by omega) (by omega)
        · have := hlowerbound second hb (by omega)
          omega
      · intro first second third hfs hst ht hlt
        by_cases hf : first = site
        · omega
        by_cases hs : second = site
        · subst second
          rw [hat, hlowerentry third (by omega) (by omega)] at hlt
          have := hbound (lower third) (hlowerbound third (by omega) (by omega))
          omega
        by_cases hthird : third = site
        · subst third
          rw [hat, hlowerentry first (by omega) hf]
          have := hbound (lower first) (hlowerbound first (by omega) hf)
          omega
        rw [hlowerentry second (by omega) hs,
          hlowerentry third (by omega) hthird] at hlt
        rw [hlowerentry first (by omega) hf, hlowerentry third (by omega) hthird]
        apply hparentleft (lower first) (lower second) (lower third)
          (hlowermono first second hfs hf hs) (hlowermono second third hst hs hthird)
        · dsimp [lower]; split_ifs <;> omega
        · exact hlt
      · intro first second third hfs hs ht hb hlt
        by_cases hfirsteq : first = site
        · subst first
          rw [hat, hlowerentry third hb (by omega)]
          have := hbound (lower third) (hlowerbound third hb (by omega))
          omega
        by_cases hsecondeq : second = site
        · subst second
          rw [hat, hlowerentry first (by omega) hfirsteq] at hlt
          have := hbound (lower first) (hlowerbound first (by omega) hfirsteq)
          omega
        rw [hlowerentry second (by omega) hsecondeq,
          hlowerentry first (by omega) hfirsteq] at hlt
        rw [hlowerentry third hb (by omega), hlowerentry first (by omega) hfirsteq]
        apply hparentcross (lower first) (lower second) (lower third)
          (hlowermono first second hfs hfirsteq hsecondeq)
        · dsimp [lower]; split_ifs <;> omega
        · dsimp [lower]; split_ifs <;> omega
        · have := hlowerbound third hb (by omega)
          omega
        · exact hlt
  change child.insertIdx gap (n + 2) ∈ _ ↔ _
  constructor
  · intro hchild
    obtain ⟨hchildright, hchildleft, _⟩ :=
      (hcriteria (n + 1) child hactive gap (by omega)).mp hchild
    have haftergap : site < gap := by
      by_contra hnot
      have hh := hchildright site (site + 1) (by omega) (by omega) (by omega)
      rw [hat, hlowerentry (site + 1) (by omega) (by omega)] at hh
      have hlow : lower (site + 1) = site := by simp [lower]
      rw [hlow] at hh
      have := hbound site hsite
      omega
    have hgapupper : gap ≤ site + 2 := by
      by_contra hnot
      have hsecondbound : site + 1 < n := by omega
      have hlt : p.getD site 0 < p.getD (site + 1) 0 := by
        have := hright site (site + 1) le_rfl (by omega) (by omega)
        have := hne site (site + 1) hsite hsecondbound (by omega)
        omega
      have hh := hchildleft site (site + 1) (site + 2) (by omega) (by omega) (by omega)
      rw [hat, hlowerentry (site + 1) (by omega) (by omega),
        hlowerentry (site + 2) (by omega) (by omega)] at hh
      have hlow1 : lower (site + 1) = site := by simp [lower]
      have hlow2 : lower (site + 2) = site + 1 := by simp [lower]
      rw [hlow1, hlow2] at hh
      have := hh hlt
      have := hbound (site + 1) hsecondbound
      omega
    by_cases hfirstgap : gap = site + 1
    · exact Or.inl hfirstgap
    · have hsecondgap : gap = site + 2 := by omega
      refine Or.inr ⟨hsecondgap, ?_⟩
      apply hsecond.mp
      simpa only [hsecondgap] using hchild
  · rintro (hfirstgap | ⟨hsecondgap, hparent⟩)
    · simpa only [hfirstgap] using hfirst
    · simpa only [hsecondgap] using hsecond.mpr hparent

theorem b_append_transition (n : ℕ) (p : List ℕ)
    (hmember : p ∈ classicalAvoiders n [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]])
    (hactive : p.insertIdx n (n + 1) ∈
      classicalAvoiders (n + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]])
    (gap : ℕ) (hgap : gap ≤ n + 1) :
    (p.insertIdx n (n + 1)).insertIdx gap (n + 2) ∈
        classicalAvoiders (n + 2) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] ↔
      gap = n + 1 ∨ gap ≤ n ∧
        (∀ first second, first < second → second < gap →
          p.getD first 0 < p.getD second 0) ∧
        (∀ first second, gap ≤ first → first < second → second < n →
          p.getD first 0 < p.getD second 0) := by
  have hlen : p.length = n := by simpa using hmember.1.length_eq
  let child := p.insertIdx n (n + 1)
  have hchildlen : child.length = n + 1 := by
    rw [List.length_insertIdx_of_le_length (by omega), hlen]
  have hbound (index : ℕ) (hi : index < n) : p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 (by omega)]
      exact List.getElem_mem _
    have hrange := hmember.1.mem_iff.mp hm
    simp only [List.mem_range'_1] at hrange
    omega
  have hne (first second : ℕ) (hf : first < n) (hs : second < n)
      (hneq : first ≠ second) : p.getD first 0 ≠ p.getD second 0 := by
    intro heq
    exact hneq ((List.getD_inj (by omega) (by omega)
      (hmember.1.nodup_iff.mpr (List.nodup_range' 1))).mp heq)
  have hbefore (index : ℕ) (hi : index < n) :
      child.getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
      List.getD_eq_getElem p 0 (by omega)]
  have hat : child.getD n 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  have hparent312 (first second third : ℕ) (hfs : first < second)
      (hst : second < third) (ht : third < n) (hlt : p.getD second 0 < p.getD third 0) :
      p.getD first 0 ≤ p.getD third 0 := by
    by_contra hnot
    apply hactive.2 [3, 1, 2, 4] (by simp)
    exact (maximum_pattern_tests n p hmember.1 n (by omega)).2.1.mpr
      (Or.inr ⟨first, second, third, hfs, hst, ht, hlt, by omega⟩)
  have hchild312 (first second third : ℕ) (hfs : first < second)
      (hst : second < third) (ht : third < child.length)
      (hlt : child.getD second 0 < child.getD third 0) :
      child.getD first 0 ≤ child.getD third 0 := by
    by_cases heq : third = n
    · subst third
      rw [hat, hbefore first (by omega)]
      have := hbound first (by omega)
      omega
    · have hb : third < n := by omega
      rw [hbefore second (by omega), hbefore third hb] at hlt
      rw [hbefore first (by omega), hbefore third hb]
      exact hparent312 first second third hfs hst hb hlt
  have h321 := (maximum_classical_pattern_tests (n + 1) child hactive.1 gap (by omega)).1
  have h2143 := maximum_2143_test (n + 1) child hactive.1 gap (by omega)
  have h3124 := (maximum_pattern_tests (n + 1) child hactive.1 gap (by omega)).2.1
  change child.insertIdx gap (n + 2) ∈ _ ↔ _
  constructor
  · intro hchild
    by_cases hlast : gap = n + 1
    · exact Or.inl hlast
    have hgapold : gap ≤ n := by omega
    refine Or.inr ⟨hgapold, ?_, ?_⟩
    · intro first second hfs hs
      have hneq := hne first second (by omega) (by omega) (by omega)
      by_contra hnot
      have hlt : p.getD second 0 < p.getD first 0 := by omega
      apply hchild.2 [2, 1, 4, 3] (by simp)
      apply h2143.mpr
      right
      refine ⟨first, second, n, hfs, hs, hgapold, by omega, ?_, ?_⟩
      · rwa [hbefore second (by omega), hbefore first (by omega)]
      · rw [hbefore first (by omega), hat]
        have := hbound first (by omega)
        omega
    · intro first second hf hfs hs
      have hneq := hne first second (by omega) hs (by omega)
      by_contra hnot
      have hlt : p.getD second 0 < p.getD first 0 := by omega
      apply hchild.2 [3, 2, 1] (by simp)
      apply h321.mpr
      right
      refine ⟨first, second, hf, hfs, by omega, ?_⟩
      rwa [hbefore second hs, hbefore first (by omega)]
  · intro hcuts
    refine ⟨?_, ?_⟩
    · apply (List.perm_insertIdx (n + 2) child (by omega)).trans
      apply (hactive.1.cons (n + 2)).trans
      have hrange : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
        have hsucc : n + 1 + 1 = n + 2 := by omega
        have hvalue : 1 + 1 * (n + 1) = n + 2 := by omega
        simpa only [hsucc, hvalue] using
          (List.range'_concat (s := 1) (n := n + 1) (step := 1))
      rw [hrange]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
    · intro pattern hpattern hocc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl
      · rcases h321.mp hocc with hocc | ⟨first, second, hf, hfs, hb, hlt⟩
        · exact hactive.2 [3, 2, 1] (by simp) hocc
        rcases hcuts with hlast | ⟨_, _, hright⟩
        · omega
        by_cases heq : second = n
        · subst second
          rw [hat, hbefore first hfs] at hlt
          have := hbound first hfs
          omega
        · have hs : second < n := by omega
          rw [hbefore second hs, hbefore first (by omega)] at hlt
          have := hright first second hf hfs hs
          omega
      · rcases h2143.mp hocc with hocc |
          ⟨first, second, third, hfs, hs, ht, hb, hlt, hgt⟩
        · exact hactive.2 [2, 1, 4, 3] (by simp) hocc
        rcases hcuts with hlast | ⟨hg, hleft, _⟩
        · omega
        · rw [hbefore second (by omega), hbefore first (by omega)] at hlt
          have := hleft first second hfs hs
          omega
      · rcases h3124.mp hocc with hocc |
          ⟨first, second, third, hfs, hst, ht, hlt, hgt⟩
        · exact hactive.2 [3, 1, 2, 4] (by simp) hocc
        · have := hchild312 first second third hfs hst (by omega) hlt
          omega

end D5.S3.Combinatorics.Fishburn.FishburnTenTenBTransitions
