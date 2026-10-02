/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveBSites
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveBSites
   mirror-E: none(waiver:positive-b-site-update)
   anchors: []
   utility: none
   digest: Positive B insertion truncates the active interval and tests the old maximum. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicAdjacent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveBSites

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion FishburnBasicPatterns
open FishburnBasicGaps FishburnBasicAdjacent

set_option maxHeartbeats 1600000 in
theorem positive_B_site_update (n : ℕ) (p : List ℕ)
    (hparent : p ∈ avoiders n [[1, 3, 2, 4], [3, 1, 2, 4]])
    (start finish : ℕ) (hstart : 1 ≤ start) (hfinish : finish ≤ p.length)
    (hshape : ∀ gap, gap ≤ p.length →
      (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] ↔
        gap = 0 ∨ start ≤ gap ∧ gap ≤ finish))
    (hascent : ∀ edge, start ≤ edge → edge < finish →
      p.getD (edge - 1) 0 < p.getD edge 0)
    (site : ℕ) (hpositive : 0 < site) (hsite : site ≤ p.length)
    (hactive : p.insertIdx site (n + 1) ∈
      avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]]) :
    ∀ gap, gap ≤ (p.insertIdx site (n + 1)).length →
      ((p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈
        avoiders (n + 2) [[1, 3, 2, 4], [3, 1, 2, 4]] ↔
      gap = 0 ∨ start ≤ gap ∧ gap ≤ site ∨ gap = site + 1 ∧
        ∃ earlier < site, p.getD earlier 0 = n) := by
  let child := p.insertIdx site (n + 1)
  have hlength : child.length = p.length + 1 := by
    simp [child, List.length_insertIdx_of_le_length hsite]
  have hpatterns : ∀ pattern ∈ [[1, 3, 2, 4], [3, 1, 2, 4]],
      pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨ pattern = [1, 4, 2, 3] := by
    intro pattern hpattern
    have hc : pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] := by
      simpa using hpattern
    rcases hc with rfl | rfl <;> simp
  have hadjacent := neighboring_gap_rules n p _ hpatterns hparent site hpositive hsite hactive
  have hsrange : start ≤ site ∧ site ≤ finish := by
    rcases (hshape site hsite).mp hactive with hz | hr
    · omega
    · exact hr
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
  have hbound : ∀ index, index < p.length → p.getD index 0 < n + 1 := by
    intro index hindex
    rw [List.getD_eq_getElem p 0 hindex]
    exact hmaxp _ (List.getElem_mem _)
  have hbefore : ∀ index, index < site → child.getD index 0 = p.getD index 0 := by
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
  have hretain : ∀ gap, gap < site →
      p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] →
      child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[1, 3, 2, 4], [3, 1, 2, 4]] := by
    intro gap hgap holdactive
    have hold := maximum_pattern_tests n p hparent.1 gap (by omega)
    have hnew := maximum_pattern_tests (n + 1) child hactive.1 gap (by omega)
    refine ⟨hperm gap (by omega), ?_, ?_⟩
    · apply (isFishburn_insertIdx_max_iff child (n + 2) gap (by omega) hmaxchild).mpr
      refine ⟨hactive.2.1, ?_⟩
      have hsafe :=
        (isFishburn_insertIdx_max_iff p (n + 1) gap (by omega) hmaxp).mp holdactive.2.1
      intro before later hcross hlater hlaterbound heq
      rw [hbefore before (by omega)] at heq
      by_cases hlt : later < site
      · rw [hbefore later hlt] at heq
        exact hsafe.2 before later hcross hlater (by omega) heq
      · by_cases hequal : later = site
        · rw [hequal, hat] at heq
          have := hbound before (by omega)
          omega
        · rw [hafter later (by omega) hlaterbound] at heq
          exact hsafe.2 before (later - 1) hcross (by omega) (by omega) heq
    · intro pattern hpattern hocc
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] := by
        simpa using hpattern
      rcases hc with rfl | rfl
      · rcases hnew.1.mp hocc with hprevious | hwitness
        · exact hactive.2.2 _ (by simp) hprevious
        · obtain ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ := hwitness
          rw [hbefore first (by omega), hbefore third (by omega)] at hlow
          rw [hbefore third (by omega), hbefore second (by omega)] at hhigh
          exact holdactive.2.2 _ (by simp)
            (hold.1.mpr (Or.inr ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩))
      · rcases hnew.2.1.mp hocc with hprevious | hwitness
        · exact hactive.2.2 _ (by simp) hprevious
        · obtain ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ := hwitness
          rw [hbefore second (by omega), hbefore third (by omega)] at hlow
          rw [hbefore third (by omega), hbefore first (by omega)] at hhigh
          exact holdactive.2.2 _ (by simp)
            (hold.2.1.mpr (Or.inr ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩))
  have hzero : child.insertIdx 0 (n + 2) ∈
      avoiders (n + 2) [[1, 3, 2, 4], [3, 1, 2, 4]] := by
    refine ⟨hperm 0 (by omega), ?_, ?_⟩
    · apply (isFishburn_insertIdx_max_iff child (n + 2) 0 (by omega) hmaxchild).mpr
      exact ⟨hactive.2.1, by intro before later hcross; omega⟩
    · intro pattern hpattern hocc
      have ht := maximum_pattern_tests (n + 1) child hactive.1 0 (by omega)
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] := by
        simpa using hpattern
      rcases hc with rfl | rfl
      · rcases ht.1.mp hocc with hprevious | ⟨first, second, third, _, _, hthird, _, _⟩
        · exact hactive.2.2 _ (by simp) hprevious
        · omega
      · rcases ht.2.1.mp hocc with hprevious | ⟨first, second, third, _, _, hthird, _, _⟩
        · exact hactive.2.2 _ (by simp) hprevious
        · omega
  have hkill : site < finish → ∀ gap, site + 1 < gap → gap ≤ child.length →
      child.insertIdx gap (n + 2) ∉
        avoiders (n + 2) [[1, 3, 2, 4], [3, 1, 2, 4]] := by
    intro hsf gap hgap hgapbound hmember
    have ha := hascent site hsrange.1 hsf
    have ht := maximum_pattern_tests (n + 1) child hactive.1 gap hgapbound
    apply hmember.2.2 [1, 3, 2, 4] (by simp)
    apply ht.1.mpr
    right
    refine ⟨site - 1, site, site + 1, by omega, by omega, hgap, ?_, ?_⟩
    · rw [hbefore (site - 1) (by omega), hafter (site + 1) (by omega) (by omega)]
      simpa using ha
    · rw [hafter (site + 1) (by omega) (by omega), hat, Nat.add_sub_cancel]
      exact hbound site (by omega)
  intro gap hgap
  change gap ≤ child.length at hgap
  constructor
  · intro hmember
    by_cases hzero : gap = 0
    · exact Or.inl hzero
    by_cases hequal : gap = site
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    by_cases hnext : gap = site + 1
    · right
      right
      refine ⟨hnext, ?_⟩
      apply hadjacent.2.mp
      simpa only [hnext] using hmember
    let oldgap := if gap < site then gap else gap - 1
    have holdgap : oldgap ≤ p.length := by dsimp [oldgap]; split_ifs <;> omega
    have holdne : oldgap ≠ site := by dsimp [oldgap]; split_ifs <;> omega
    have hmap : (if oldgap < site then oldgap else oldgap + 1) = gap := by
      dsimp [oldgap]
      split_ifs <;> omega
    have hrelation : gap < site ∧ oldgap = gap ∨ site + 1 < gap ∧ oldgap = gap - 1 := by
      dsimp [oldgap]
      split_ifs <;> omega
    have holdactive : p.insertIdx oldgap (n + 1) ∈
        avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] := by
      by_contra hinactive
      have hi := inactive_gap_transport n p _ hpatterns hparent site oldgap hsite holdgap
        holdne hactive hinactive
      apply hi
      simpa only [hmap] using hmember
    have holdrange : start ≤ oldgap ∧ oldgap ≤ finish := by
      rcases (hshape oldgap holdgap).mp holdactive with hz | hr
      · rcases hrelation with ⟨_, heq⟩ | ⟨_, heq⟩ <;> omega
      · exact hr
    rcases hrelation with ⟨hlt, heq⟩ | ⟨hgt, heq⟩
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact False.elim (hkill (by omega) gap hgt hgap hmember)
  · rintro (rfl | ⟨hlow, hhigh⟩ | ⟨rfl, hprefix⟩)
    · exact hzero
    · by_cases hequal : gap = site
      · simpa only [hequal] using hadjacent.1
      · apply hretain gap (by omega)
        exact (hshape gap (by omega)).mpr (Or.inr ⟨hlow, by omega⟩)
    · exact hadjacent.2.mpr hprefix

end D5.S3.Combinatorics.Fishburn.FishburnTenFiveBSites
