/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicAscents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicAscents
   mirror-E: none(waiver:ascent-predecessor-witnesses)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The Fishburn condition forces ascent predecessors into earlier positions. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicAscents

open D5.S3.Combinatorics.Fishburn.FishburnDefs

theorem isFishburn_iff_ascent_predecessor (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) :
    IsFishburn p ↔
      ∀ index, index + 1 < p.length → p.getD index 0 < p.getD (index + 1) 0 →
        p.getD index 0 = 1 ∨
          ∃ earlier, earlier < index ∧ p.getD earlier 0 + 1 = p.getD index 0 := by
  have hvalues (index : ℕ) (hi : index < p.length) :
      1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 hi]
      exact List.getElem_mem hi
    have hrange := hperm.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, hoffset, hvalue⟩ := hrange
    omega
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  constructor
  · intro h index hi hascent
    by_cases hone : p.getD index 0 = 1
    · exact Or.inl hone
    · right
      have hbottom := hvalues index (by omega)
      have hpredmem : p.getD index 0 - 1 ∈ p := by
        apply hperm.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        refine ⟨p.getD index 0 - 2, by omega, by omega⟩
      obtain ⟨earlier, hearlier, hvalue⟩ := List.mem_iff_getElem.mp hpredmem
      have hpred : p.getD earlier 0 + 1 = p.getD index 0 := by
        rw [List.getD_eq_getElem p 0 hearlier, hvalue]
        omega
      have hleft : earlier < index := by
        by_contra hnot
        by_cases heq : earlier = index
        · subst earlier
          omega
        by_cases hnext : earlier = index + 1
        · subst earlier
          omega
        exact h index earlier (by omega) hearlier ⟨hpred.symm, by omega⟩
      exact ⟨earlier, hleft, hpred⟩
  · intro h before later hgap hlater hbad
    have ha := h before (by omega) (by omega)
    rcases ha with hone | ⟨earlier, hearlier, hpred⟩
    · have hpositive := (hvalues later hlater).1
      omega
    · have heq : p.getD earlier 0 = p.getD later 0 := by omega
      have hindex := (List.getD_inj (by omega) hlater hnodup).mp heq
      omega

end D5.S3.Combinatorics.Fishburn.FishburnBasicAscents
