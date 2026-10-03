/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicPrefixes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicPrefixes
   mirror-E: none(waiver:first-ascent-and-predecessor-induction)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Eligible Fishburn prefixes contain one and constrain increasing initial segments. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicPrefixes

open D5.S3.Combinatorics.Fishburn.FishburnDefs

theorem eligible_prefix_structure (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (hfish : IsFishburn p)
    (cut : ℕ) (hcut : cut ≤ p.length) (hpositive : 0 < cut)
    (heligible : ∀ before later, before + 1 = cut → cut ≤ later → later < p.length →
      p.getD before 0 ≠ p.getD later 0 + 1) :
    1 ∈ p.take cut ∧
      ((p.take cut).Pairwise (· < ·) → p.take cut = List.range' 1 cut) := by
  have isFishburn_iff_ascent_predecessor (n : ℕ) (p : List ℕ)
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
  have prefix_through_one_decreasing (n : ℕ) (p : List ℕ)
      (hperm : p.Perm (List.range' 1 n)) (hfish : IsFishburn p)
      (one : ℕ) (honebound : one < p.length) (hone : p.getD one 0 = 1) :
      ∀ earlier later, earlier < later → later ≤ one →
        p.getD later 0 < p.getD earlier 0 := by
    have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hascents := (isFishburn_iff_ascent_predecessor n p hperm).mp hfish
    have hdec : ∀ later, later ≤ one → ∀ earlier, earlier < later →
        p.getD later 0 < p.getD earlier 0 := by
      intro later
      induction later using Nat.strong_induction_on with
      | h later ih =>
        intro hlater earlier hearlier
        cases later with
        | zero => omega
        | succ previous =>
          have hstep : p.getD (previous + 1) 0 < p.getD previous 0 := by
            rcases lt_trichotomy (p.getD (previous + 1) 0) (p.getD previous 0) with
              hlt | heq | hascent
            · exact hlt
            · have hindex := (List.getD_inj (by omega) (by omega) hnodup).mp heq
              omega
            · rcases hascents previous (by omega) hascent with hbottom | hpred
              · have hindex : previous = one :=
                  (List.getD_inj (by omega) honebound hnodup).mp (hbottom.trans hone.symm)
                omega
              · obtain ⟨pred, hpred, hvalue⟩ := hpred
                have hdecrease := ih previous (by omega) (by omega) pred hpred
                omega
          by_cases heq : earlier = previous
          · subst earlier
            exact hstep
          · exact lt_trans hstep (ih previous (by omega) (by omega) earlier (by omega))
    intro earlier later hearlier hlater
    exact hdec later hlater earlier hearlier
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hlength : p.length = n := by simpa using hperm.length_eq
  have hvalues (index : ℕ) (hi : index < p.length) :
      1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 hi]
      exact List.getElem_mem hi
    have hrange := hperm.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, hoffset, hvalue⟩ := hrange
    omega
  have hlast : p.getD (cut - 1) 0 = 1 ∨
      ∃ earlier, earlier < cut - 1 ∧
        p.getD earlier 0 + 1 = p.getD (cut - 1) 0 := by
    by_cases hone : p.getD (cut - 1) 0 = 1
    · exact Or.inl hone
    · right
      have hb := hvalues (cut - 1) (by omega)
      have hpredmem : p.getD (cut - 1) 0 - 1 ∈ p := by
        apply hperm.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨p.getD (cut - 1) 0 - 2, by omega, by omega⟩
      obtain ⟨earlier, hearlier, hvalue⟩ := List.mem_iff_getElem.mp hpredmem
      have hpred : p.getD earlier 0 + 1 = p.getD (cut - 1) 0 := by
        rw [List.getD_eq_getElem p 0 hearlier, hvalue]
        omega
      refine ⟨earlier, ?_, hpred⟩
      by_contra hnot
      by_cases heq : earlier = cut - 1
      · rw [heq] at hpred
        omega
      exact heligible (cut - 1) earlier (by omega) (by omega) hearlier hpred.symm
  have honemem : 1 ∈ p := by
    apply hperm.mem_iff.mpr
    simp only [List.mem_range', Nat.one_mul]
    exact ⟨0, by omega, by omega⟩
  obtain ⟨one, honebound, honevalue⟩ := List.mem_iff_getElem.mp honemem
  have hone : p.getD one 0 = 1 := by rw [List.getD_eq_getElem p 0 honebound, honevalue]
  have honecut : one < cut := by
    by_contra hnot
    rcases hlast with hbottom | ⟨earlier, hearlier, hpred⟩
    · have hindex := (List.getD_inj (by omega) honebound hnodup).mp
        (hbottom.trans hone.symm)
      omega
    · have hdec := prefix_through_one_decreasing n p hperm hfish one honebound hone
        earlier (cut - 1) hearlier (by omega)
      omega
  constructor
  · apply List.mem_iff_getElem.mpr
    refine ⟨one, by simp only [List.length_take]; omega, ?_⟩
    simpa only [List.getElem_take] using honevalue
  · intro hincreasing
    have hincrease (earlier later : ℕ) (hearlier : earlier < later) (hlater : later < cut) :
        p.getD earlier 0 < p.getD later 0 := by
      have hp := List.pairwise_iff_getElem.mp hincreasing earlier later
        (by simp only [List.length_take]; omega) (by simp only [List.length_take]; omega)
        hearlier
      rw [List.getD_eq_getElem p 0 (by omega), List.getD_eq_getElem p 0 (by omega)]
      simpa only [List.getElem_take] using hp
    have hpreds (index : ℕ) (hi : index < cut) :
        p.getD index 0 = 1 ∨
          ∃ earlier, earlier < index ∧ p.getD earlier 0 + 1 = p.getD index 0 := by
      by_cases hlastindex : index = cut - 1
      · simpa only [hlastindex] using hlast
      · exact (isFishburn_iff_ascent_predecessor n p hperm).mp hfish index (by omega)
          (hincrease index (index + 1) (by omega) (by omega))
    have hentries : ∀ index, index < cut → p.getD index 0 = index + 1 := by
      intro index
      induction index using Nat.strong_induction_on with
      | h index ih =>
        intro hi
        rcases hpreds index hi with honeindex | ⟨earlier, hearlier, hpred⟩
        · by_cases hzero : index = 0
          · omega
          · have hprevious := ih (index - 1) (by omega) (by omega)
            have hinc := hincrease (index - 1) index (by omega) hi
            omega
        · have hearlierentry := ih earlier hearlier (by omega)
          by_cases hzero : index = 0
          · omega
          · have hprevious := ih (index - 1) (by omega) (by omega)
            have hinc := hincrease (index - 1) index (by omega) hi
            omega
    apply List.ext_getElem
    · simp only [List.length_take, List.length_range']
      omega
    · intro index hleft hright
      have hi : index < cut := by simpa using hright
      rw [List.getElem_take, List.getElem_range']
      have he := hentries index hi
      rw [List.getD_eq_getElem p 0 (by omega)] at he
      omega

end D5.S3.Combinatorics.Fishburn.FishburnBasicPrefixes
