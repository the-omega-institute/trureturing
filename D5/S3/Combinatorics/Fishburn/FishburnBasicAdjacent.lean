/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicAdjacent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicAdjacent
   mirror-E: none(waiver:neighboring-maximum-gap-rules)
   anchors: []
   utility: none
   digest: The gaps neighboring an inserted maximum are governed by its predecessor position. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicGaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicAdjacent

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion FishburnBasicPatterns

set_option maxHeartbeats 1000000 in
theorem neighboring_gap_rules (n : ℕ) (p : List ℕ) (patterns : List (List ℕ))
    (hpatterns : ∀ pattern ∈ patterns,
      pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨ pattern = [1, 4, 2, 3])
    (hparent : p ∈ avoiders n patterns) (site : ℕ)
    (hpositive : 0 < site) (hsite : site ≤ p.length)
    (hactive : p.insertIdx site (n + 1) ∈ avoiders (n + 1) patterns) :
    (p.insertIdx site (n + 1)).insertIdx site (n + 2) ∈ avoiders (n + 2) patterns ∧
    ((p.insertIdx site (n + 1)).insertIdx (site + 1) (n + 2) ∈
      avoiders (n + 2) patterns ↔
      ∃ earlier < site, p.getD earlier 0 = n) := by
  let child := p.insertIdx site (n + 1)
  have hlength : child.length = p.length + 1 := by
    simp [child, List.length_insertIdx_of_le_length hsite]
  have hmaxp : ∀ value ∈ p, value < n + 1 := by
    intro value hvalue
    have hm := hparent.1.mem_iff.mp hvalue
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨offset, hoffset, heq⟩ := hm
    omega
  have hmaxchild : ∀ value ∈ child, value < n + 2 := by
    intro value hvalue
    have hm := hactive.1.mem_iff.mp hvalue
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨offset, hoffset, heq⟩ := hm
    omega
  have hbound : ∀ index, index < child.length → child.getD index 0 ≤ n + 1 := by
    intro index hindex
    rw [List.getD_eq_getElem child 0 hindex]
    have := hmaxchild _ (List.getElem_mem hindex)
    omega
  have hbefore : ∀ index, index < site →
      child.getD index 0 = p.getD index 0 := by
    intro index hindex
    rw [List.getD_eq_getElem child 0 (by omega),
      List.getElem_insertIdx_of_lt hindex, List.getD_eq_getElem p 0 (by omega)]
  have hat : child.getD site 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  have hafter : ∀ index, site < index → index < child.length →
      child.getD index 0 = p.getD (index - 1) 0 := by
    intro index hindex hbound
    rw [List.getD_eq_getElem child 0 hbound, List.getElem_insertIdx_of_gt hindex,
      List.getD_eq_getElem p 0 (by omega)]
  have hperm : ∀ gap, gap ≤ child.length →
      (child.insertIdx gap (n + 2)).Perm (List.range' 1 (n + 2)) := by
    intro gap hgap
    apply (List.perm_insertIdx (n + 2) child hgap).trans
    apply (hactive.1.cons (n + 2)).trans
    have hrange : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
      simpa only [Nat.one_mul, Nat.add_assoc, Nat.reduceAdd,
        show 1 + (n + 1) = n + 2 by omega] using
        (List.range'_concat (s := 1) (n := n + 1) (step := 1))
    rw [hrange]
    simpa using (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
  have hold := maximum_pattern_tests n p hparent.1 site hsite
  have havoids : ∀ gap, gap = site ∨ gap = site + 1 →
      ∀ pattern ∈ patterns, ¬ NonnestingDefs.Occurs pattern (child.insertIdx gap (n + 2)) := by
    intro gap hgap pattern hpattern hocc
    have hgapbound : site ≤ gap ∧ gap ≤ site + 1 := by rcases hgap with rfl | rfl <;> omega
    have hnew := maximum_pattern_tests (n + 1) child hactive.1 gap (by omega)
    rcases hpatterns pattern hpattern with rfl | rfl | rfl
    · rcases hnew.1.mp hocc with hprevious | hwitness
      · exact hactive.2.2 _ hpattern hprevious
      · obtain ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ := hwitness
        have hthird : third < site := by
          by_contra hnot
          have heq : third = site := by omega
          rw [heq, hat] at hhigh
          have := hbound second (by omega)
          omega
        rw [hbefore first (by omega), hbefore third hthird] at hlow
        rw [hbefore third hthird, hbefore second (by omega)] at hhigh
        exact hactive.2.2 _ hpattern
          (hold.1.mpr (Or.inr ⟨first, second, third, hfs, hst, hthird, hlow, hhigh⟩))
    · rcases hnew.2.1.mp hocc with hprevious | hwitness
      · exact hactive.2.2 _ hpattern hprevious
      · obtain ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ := hwitness
        have hthird : third < site := by
          by_contra hnot
          have heq : third = site := by omega
          rw [heq, hat] at hhigh
          have := hbound first (by omega)
          omega
        rw [hbefore second (by omega), hbefore third hthird] at hlow
        rw [hbefore third hthird, hbefore first (by omega)] at hhigh
        exact hactive.2.2 _ hpattern
          (hold.2.1.mpr (Or.inr ⟨first, second, third, hfs, hst, hthird, hlow, hhigh⟩))
    · rcases hnew.2.2.mp hocc with hprevious | hwitness
      · exact hactive.2.2 _ hpattern hprevious
      · obtain ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩ := hwitness
        have hfirst : first < site := by
          by_contra hnot
          have heq : first = site := by omega
          rw [heq, hat] at hlow
          have := hbound second (by omega)
          omega
        have hsecond : site < second := by
          by_contra hnot
          have heq : second = site := by omega
          rw [heq, hat] at hhigh
          have := hbound third ht
          omega
        rw [hbefore first hfirst, hafter second hsecond (by omega)] at hlow
        rw [hafter second hsecond (by omega), hafter third (by omega) ht] at hhigh
        exact hactive.2.2 _ hpattern
          (hold.2.2.mpr (Or.inr ⟨first, second - 1, third - 1, hfirst, by omega,
            by omega, by omega, hlow, hhigh⟩))
  have hsafe :=
    (isFishburn_insertIdx_max_iff p (n + 1) site hsite hmaxp).mp hactive.2.1
  constructor
  · refine ⟨hperm site (by omega), ?_, havoids site (Or.inl rfl)⟩
    apply (isFishburn_insertIdx_max_iff child (n + 2) site (by omega) hmaxchild).mpr
    refine ⟨hactive.2.1, ?_⟩
    intro before later hcross hlater hboundlater heq
    rw [hbefore before (by omega)] at heq
    by_cases hequal : later = site
    · subst later
      rw [hat] at heq
      have hb : p.getD before 0 < n + 1 := by
        rw [List.getD_eq_getElem p 0 (by omega)]
        exact hmaxp _ (List.getElem_mem _)
      omega
    · rw [hafter later (by omega) hboundlater] at heq
      exact hsafe.2 before (later - 1) hcross (by omega) (by omega) heq
  · constructor
    · intro hmember
      have hnew :=
        (isFishburn_insertIdx_max_iff child (n + 2) (site + 1) (by omega) hmaxchild).mp
          hmember.2.1
      have hn : 1 ≤ n := by
        have hlen := hparent.1.length_eq
        simp only [List.length_range'] at hlen
        omega
      have hnmem : n ∈ p := by
        apply hparent.1.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨n - 1, by omega, by omega⟩
      obtain ⟨earlier, hearlier, hvalue⟩ := List.mem_iff_getElem.mp hnmem
      have hentry : p.getD earlier 0 = n := by
        rwa [List.getD_eq_getElem p 0 hearlier]
      refine ⟨earlier, ?_, hentry⟩
      by_contra hnot
      apply hnew.2 site (earlier + 1) rfl (by omega) (by omega)
      rw [hat, hafter (earlier + 1) (by omega) (by omega), Nat.add_sub_cancel, hentry]
    · rintro ⟨earlier, hearlier, hvalue⟩
      refine ⟨hperm (site + 1) (by omega), ?_, havoids (site + 1) (Or.inr rfl)⟩
      apply (isFishburn_insertIdx_max_iff child (n + 2) (site + 1) (by omega) hmaxchild).mpr
      refine ⟨hactive.2.1, ?_⟩
      intro before later hbefore hlater hboundlater heq
      have heqbefore : before = site := by omega
      subst before
      rw [hat, hafter later (by omega) hboundlater] at heq
      have hsame : p.getD earlier 0 = p.getD (later - 1) 0 := by omega
      have hindex := (List.getD_inj (by omega) (by omega)
        (hparent.1.nodup_iff.mpr (List.nodup_range' 1))).mp hsame
      omega

end D5.S3.Combinatorics.Fishburn.FishburnBasicAdjacent
