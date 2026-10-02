/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicGaps
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicGaps
   mirror-E: none(waiver:persistent-inactive-maximum-gaps)
   anchors: []
   utility: none
   digest: An inactive old gap stays inactive after a maximum is inserted at another gap. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicPatterns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicGaps

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion FishburnBasicPatterns

set_option maxHeartbeats 800000 in
theorem inactive_gap_transport (n : ℕ) (p : List ℕ) (patterns : List (List ℕ))
    (hpatterns : ∀ pattern ∈ patterns,
      pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨ pattern = [1, 4, 2, 3])
    (hparent : p ∈ avoiders n patterns) (site gap : ℕ)
    (hsite : site ≤ p.length) (hgap : gap ≤ p.length) (hne : gap ≠ site)
    (hactive : p.insertIdx site (n + 1) ∈ avoiders (n + 1) patterns)
    (hinactive : p.insertIdx gap (n + 1) ∉ avoiders (n + 1) patterns) :
    (p.insertIdx site (n + 1)).insertIdx (if gap < site then gap else gap + 1) (n + 2)
      ∉ avoiders (n + 2) patterns := by
  let child := p.insertIdx site (n + 1)
  let nextgap := if gap < site then gap else gap + 1
  let lift := fun index : ℕ => if index < site then index else index + 1
  have hlength : child.length = p.length + 1 := by
    simp [child, List.length_insertIdx_of_le_length hsite]
  have hnext : nextgap ≤ child.length := by
    dsimp [nextgap]
    split_ifs <;> omega
  have hmono : StrictMono lift := by
    intro first second hlt
    dsimp [lift]
    split_ifs <;> omega
  have hliftbound : ∀ index, index < p.length → lift index < child.length := by
    intro index hindex
    dsimp [lift]
    split_ifs <;> omega
  have hliftentry : ∀ index, index < p.length →
      child.getD (lift index) 0 = p.getD index 0 := by
    intro index hindex
    dsimp [lift]
    split_ifs with hleft
    · rw [List.getD_eq_getElem child 0 (by omega),
        List.getElem_insertIdx_of_lt hleft, List.getD_eq_getElem p 0 hindex]
    · rw [List.getD_eq_getElem child 0 (by omega),
        List.getElem_insertIdx_of_gt (by omega), List.getD_eq_getElem p 0 (by omega)]
      simp only [Nat.add_sub_cancel]
  have hprefix : ∀ index, index < gap → lift index < nextgap := by
    intro index hindex
    dsimp [lift, nextgap]
    split_ifs <;> omega
  have hsuffix : ∀ index, gap ≤ index → nextgap ≤ lift index := by
    intro index hindex
    dsimp [lift, nextgap]
    split_ifs <;> omega
  have hboundary : ∀ before, before + 1 = gap → lift before + 1 = nextgap := by
    intro before hbefore
    dsimp [lift, nextgap]
    split_ifs <;> omega
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
  have holdtests := maximum_pattern_tests n p hparent.1 gap hgap
  have hnewtests := maximum_pattern_tests (n + 1) child hactive.1 nextgap hnext
  intro hnew
  apply hinactive
  refine ⟨?_, ?_, ?_⟩
  · apply (List.perm_insertIdx (n + 1) p hgap).trans
    apply (hparent.1.cons (n + 1)).trans
    rw [List.range'_concat]
    simpa [Nat.add_comm] using
      (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
  · apply (isFishburn_insertIdx_max_iff p (n + 1) gap hgap hmaxp).mpr
    refine ⟨hparent.2.1, ?_⟩
    intro before later hbefore hlater hbound heq
    have hconditions :=
      (isFishburn_insertIdx_max_iff child (n + 2) nextgap hnext hmaxchild).mp hnew.2.1
    apply hconditions.2 (lift before) (lift later) (hboundary before hbefore)
      (hsuffix later hlater) (hliftbound later hbound)
    rwa [hliftentry before (by omega), hliftentry later hbound]
  · intro pattern hpattern hold
    rcases hpatterns pattern hpattern with rfl | rfl | rfl
    · rcases holdtests.1.mp hold with hprevious | hwitness
      · exact hparent.2.2 _ hpattern hprevious
      · obtain ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ := hwitness
        apply hnew.2.2 [1, 3, 2, 4] hpattern
        apply hnewtests.1.mpr
        right
        refine ⟨lift first, lift second, lift third, hmono hfs, hmono hst,
          hprefix third ht, ?_, ?_⟩
        · rwa [hliftentry first (by omega), hliftentry third (by omega)]
        · rwa [hliftentry third (by omega), hliftentry second (by omega)]
    · rcases holdtests.2.1.mp hold with hprevious | hwitness
      · exact hparent.2.2 _ hpattern hprevious
      · obtain ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ := hwitness
        apply hnew.2.2 [3, 1, 2, 4] hpattern
        apply hnewtests.2.1.mpr
        right
        refine ⟨lift first, lift second, lift third, hmono hfs, hmono hst,
          hprefix third ht, ?_, ?_⟩
        · rwa [hliftentry second (by omega), hliftentry third (by omega)]
        · rwa [hliftentry third (by omega), hliftentry first (by omega)]
    · rcases holdtests.2.2.mp hold with hprevious | hwitness
      · exact hparent.2.2 _ hpattern hprevious
      · obtain ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩ := hwitness
        apply hnew.2.2 [1, 4, 2, 3] hpattern
        apply hnewtests.2.2.mpr
        right
        refine ⟨lift first, lift second, lift third, hprefix first hf,
          hsuffix second hs, hmono hst, hliftbound third ht, ?_, ?_⟩
        · rwa [hliftentry first (by omega), hliftentry second (by omega)]
        · rwa [hliftentry second (by omega), hliftentry third ht]

end D5.S3.Combinatorics.Fishburn.FishburnBasicGaps
