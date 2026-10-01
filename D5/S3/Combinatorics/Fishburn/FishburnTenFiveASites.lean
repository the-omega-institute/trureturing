/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveASites
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveASites
   mirror-E: none(waiver:positive-a-site-update)
   anchors: []
   utility: none
   digest: A positive A insertion leaves only zero and the two neighboring candidate gaps. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicAdjacent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveASites

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion FishburnBasicPatterns
open FishburnBasicGaps FishburnBasicAdjacent

set_option maxHeartbeats 1200000 in
theorem positive_A_site_update (n : ℕ) (p : List ℕ)
    (hparent : p ∈ avoiders n [[1, 3, 2, 4], [1, 4, 2, 3]])
    (start : ℕ) (hstart : 1 ≤ start) (three : Prop)
    (hshape : ∀ gap, gap ≤ p.length →
      (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]] ↔
        gap = 0 ∨ gap = start ∨ three ∧ gap = start + 1))
    (hascent : three → start < p.length ∧
      p.getD (start - 1) 0 < p.getD start 0)
    (site : ℕ) (hpositive : 0 < site) (hsite : site ≤ p.length)
    (hactive : p.insertIdx site (n + 1) ∈
      avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]]) :
    ∀ gap, gap ≤ (p.insertIdx site (n + 1)).length →
      ((p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈
        avoiders (n + 2) [[1, 3, 2, 4], [1, 4, 2, 3]] ↔
      gap = 0 ∨ gap = site ∨ gap = site + 1 ∧
        ∃ earlier < site, p.getD earlier 0 = n) := by
  let child := p.insertIdx site (n + 1)
  have hlength : child.length = p.length + 1 := by
    simp [child, List.length_insertIdx_of_le_length hsite]
  have hpatterns : ∀ pattern ∈ [[1, 3, 2, 4], [1, 4, 2, 3]],
      pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨ pattern = [1, 4, 2, 3] := by
    intro pattern hpattern
    have hc : pattern = [1, 3, 2, 4] ∨ pattern = [1, 4, 2, 3] := by simpa using hpattern
    rcases hc with rfl | rfl <;> simp
  have hadjacent := neighboring_gap_rules n p _ hpatterns hparent site hpositive hsite hactive
  have hmax : ∀ value ∈ child, value < n + 2 := by
    intro value hvalue
    have hm := hactive.1.mem_iff.mp hvalue
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨offset, hoffset, heq⟩ := hm
    omega
  have hbound : ∀ index, index < p.length → p.getD index 0 < n + 1 := by
    intro index hindex
    have hm := hparent.1.mem_iff.mp (List.getElem_mem hindex)
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨offset, hoffset, heq⟩ := hm
    rw [List.getD_eq_getElem p 0 hindex]
    omega
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
  have hzero : child.insertIdx 0 (n + 2) ∈
      avoiders (n + 2) [[1, 3, 2, 4], [1, 4, 2, 3]] := by
    refine ⟨?_, ?_, ?_⟩
    · apply (List.perm_insertIdx (n + 2) child (by omega)).trans
      apply (hactive.1.cons (n + 2)).trans
      have hrange : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
        simpa only [Nat.one_mul, Nat.add_assoc, Nat.reduceAdd,
          show 1 + (n + 1) = n + 2 by omega] using
          (List.range'_concat (s := 1) (n := n + 1) (step := 1))
      rw [hrange]
      simpa using (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
    · apply (isFishburn_insertIdx_max_iff child (n + 2) 0 (by omega) hmax).mpr
      exact ⟨hactive.2.1, by intro before later hcross; omega⟩
    · intro pattern hpattern hocc
      have ht := maximum_pattern_tests (n + 1) child hactive.1 0 (by omega)
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [1, 4, 2, 3] := by
        simpa using hpattern
      rcases hc with rfl | rfl
      · rcases ht.1.mp hocc with hprevious | ⟨first, second, third, _, _, hthird, _, _⟩
        · exact hactive.2.2 _ (by simp) hprevious
        · omega
      · rcases ht.2.2.mp hocc with hprevious | ⟨first, second, third, hfirst, _, _, _, _, _⟩
        · exact hactive.2.2 _ (by simp) hprevious
        · omega
  have hkill132 : three → site = start →
      child.insertIdx (start + 2) (n + 2) ∉
        avoiders (n + 2) [[1, 3, 2, 4], [1, 4, 2, 3]] := by
    intro hthree heq hmember
    have ha := hascent hthree
    have ht := maximum_pattern_tests (n + 1) child hactive.1 (start + 2) (by omega)
    apply hmember.2.2 [1, 3, 2, 4] (by simp)
    apply ht.1.mpr
    right
    refine ⟨start - 1, start, start + 1, by omega, by omega, by omega, ?_, ?_⟩
    · rw [hbefore (start - 1) (by omega), hafter (start + 1) (by omega) (by omega)]
      simpa using ha.2
    · rw [hafter (start + 1) (by omega) (by omega), ← heq, hat]
      simpa only [heq, Nat.add_sub_cancel] using hbound start ha.1
  have hkill142 : three → site = start + 1 →
      child.insertIdx start (n + 2) ∉
        avoiders (n + 2) [[1, 3, 2, 4], [1, 4, 2, 3]] := by
    intro hthree heq hmember
    have ha := hascent hthree
    have ht := maximum_pattern_tests (n + 1) child hactive.1 start (by omega)
    apply hmember.2.2 [1, 4, 2, 3] (by simp)
    apply ht.2.2.mpr
    right
    refine ⟨start - 1, start, start + 1, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · rw [hbefore (start - 1) (by omega), hbefore start (by omega)]
      exact ha.2
    · rw [hbefore start (by omega), ← heq, hat]
      exact hbound start ha.1
  intro gap hgap
  change gap ≤ child.length at hgap
  constructor
  · intro hmember
    by_cases hzero : gap = 0
    · exact Or.inl hzero
    by_cases hequal : gap = site
    · exact Or.inr (Or.inl hequal)
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
        avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]] := by
      by_contra hinactive
      have hi := inactive_gap_transport n p _ hpatterns hparent site oldgap hsite holdgap
        holdne hactive hinactive
      apply hi
      simpa only [hmap] using hmember
    have hsitechoices : site = start ∨ three ∧ site = start + 1 := by
      rcases (hshape site hsite).mp hactive with hz | hs | ht
      · omega
      · exact Or.inl hs
      · exact Or.inr ht
    have holdchoices : oldgap = start ∨ three ∧ oldgap = start + 1 := by
      rcases (hshape oldgap holdgap).mp holdactive with hz | hs | ht
      · rcases hrelation with ⟨_, heq⟩ | ⟨_, heq⟩ <;> omega
      · exact Or.inl hs
      · exact Or.inr ht
    rcases hsitechoices with hs | ⟨hthree, hs⟩
    · rcases holdchoices with ho | ⟨hthree, ho⟩
      · omega
      · have heqgap : gap = start + 2 := by
          rcases hrelation with ⟨_, heq⟩ | ⟨_, heq⟩ <;> omega
        exact False.elim (hkill132 hthree hs (by simpa only [heqgap] using hmember))
    · rcases holdchoices with ho | ⟨_, ho⟩
      · have heqgap : gap = start := by
          rcases hrelation with ⟨_, heq⟩ | ⟨_, heq⟩ <;> omega
        exact False.elim (hkill142 hthree hs (by simpa only [heqgap] using hmember))
      · omega
  · rintro (rfl | rfl | ⟨rfl, hprefix⟩)
    · exact hzero
    · exact hadjacent.1
    · exact hadjacent.2.mpr hprefix

end D5.S3.Combinatorics.Fishburn.FishburnTenFiveASites
