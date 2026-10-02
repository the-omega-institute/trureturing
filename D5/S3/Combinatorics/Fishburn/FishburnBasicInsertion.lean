/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicInsertion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicInsertion
   mirror-E: none(waiver:maximum-cut-witness-analysis)
   anchors: [mathlib/module/Mathlib.Data.List.InsertIdx, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Maximum insertion characterizes eligible cuts and preserves maximum deletion. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import Mathlib.Data.List.InsertIdx
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicInsertion

open D5.S3.Combinatorics.Fishburn.FishburnDefs

theorem isFishburn_insertIdx_max_iff (p : List ℕ) (maximum cut : ℕ)
    (hcut : cut ≤ p.length) (hmax : ∀ value ∈ p, value < maximum) :
    IsFishburn (p.insertIdx cut maximum) ↔
      IsFishburn p ∧
        ∀ before later, before + 1 = cut → cut ≤ later → later < p.length →
          p.getD before 0 ≠ p.getD later 0 + 1 := by
  let child := p.insertIdx cut maximum
  have hlen : child.length = p.length + 1 :=
    List.length_insertIdx_of_le_length hcut maximum
  have hbefore (index : ℕ) (hi : index < cut) :
      child.getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem child 0 (by omega),
      List.getD_eq_getElem p 0 (by omega)]
    exact List.getElem_insertIdx_of_lt hi (by change index < child.length; omega)
  have hat : child.getD cut 0 = maximum := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self (by change cut < child.length; omega)
  have hafter (index : ℕ) (hi : cut < index) (hb : index < child.length) :
      child.getD index 0 = p.getD (index - 1) 0 := by
    rw [List.getD_eq_getElem child 0 hb,
      List.getD_eq_getElem p 0 (by omega)]
    exact List.getElem_insertIdx_of_gt hi hb
  have hold (index : ℕ) (hi : index < p.length) : p.getD index 0 < maximum := by
    rw [List.getD_eq_getElem p 0 hi]
    exact hmax _ (List.getElem_mem _)
  have hbound (index : ℕ) (hi : index < child.length) :
      child.getD index 0 ≤ maximum := by
    rcases lt_trichotomy index cut with hlt | heq | hgt
    · rw [hbefore index hlt]
      exact Nat.le_of_lt (hold index (by omega))
    · subst index
      exact Nat.le_of_eq hat
    · rw [hafter index hgt hi]
      exact Nat.le_of_lt (hold (index - 1) (by omega))
  change IsFishburn child ↔ _
  constructor
  · intro hchild
    constructor
    · intro before later hgap hlater hbad
      by_cases hlcut : later < cut
      · apply hchild before later hgap (by omega)
        simpa only [hbefore before (by omega), hbefore later hlcut,
          hbefore (before + 1) (by omega)] using hbad
      · by_cases hbcut : cut ≤ before
        · apply hchild (before + 1) (later + 1) (by omega) (by omega)
          simpa only [hafter (before + 1) (by omega) (by omega),
            hafter (later + 1) (by omega) (by omega),
            hafter (before + 1 + 1) (by omega) (by omega),
            Nat.add_sub_cancel] using hbad
        · by_cases hcross : before + 1 = cut
          · apply hchild before (later + 1) (by omega) (by omega)
            rw [hbefore before (by omega),
              hafter (later + 1) (by omega) (by omega), Nat.add_sub_cancel,
              hcross, hat]
            exact ⟨hbad.1, hbad.1 ▸ hold before (by omega)⟩
          · apply hchild before (later + 1) (by omega) (by omega)
            simpa only [hbefore before (by omega),
              hafter (later + 1) (by omega) (by omega), Nat.add_sub_cancel,
              hbefore (before + 1) (by omega)] using hbad
    · intro before later hcross hlcut hlater heq
      apply hchild before (later + 1) (by omega) (by omega)
      rw [hbefore before (by omega), hcross, hat,
        hafter (later + 1) (by omega) (by omega), Nat.add_sub_cancel]
      exact ⟨heq, heq ▸ hold before (by omega)⟩
  · rintro ⟨hparent, heligible⟩ before later hgap hlater hbad
    have hbeforebound : before + 1 < child.length := by omega
    by_cases hbmaximum : before = cut
    · subst before
      have hb := hbound (cut + 1) hbeforebound
      rw [hat] at hbad
      omega
    by_cases hlmaximum : later = cut
    · subst later
      have hb := hbound before (by omega)
      rw [hat] at hbad
      omega
    by_cases hbcut : before < cut
    · by_cases hcross : before + 1 = cut
      · have hj : cut < later := by omega
        have heq := hbad.1
        rw [hbefore before hbcut, hafter later hj hlater] at heq
        exact heligible before (later - 1) hcross (by omega) (by omega) heq
      · have hbnext : before + 1 < cut := by omega
        by_cases hlcut : later < cut
        · apply hparent before later hgap (by omega)
          simpa only [hbefore before hbcut, hbefore later hlcut,
            hbefore (before + 1) hbnext] using hbad
        · apply hparent before (later - 1) (by omega) (by omega)
          simpa only [hbefore before hbcut, hafter later (by omega) hlater,
            hbefore (before + 1) hbnext] using hbad
    · have hb : cut < before := by omega
      apply hparent (before - 1) (later - 1) (by omega) (by omega)
      have hnext : before + 1 - 1 = before - 1 + 1 := by omega
      simpa only [hafter before hb (by omega), hafter later (by omega) hlater,
        hafter (before + 1) (by omega) hbeforebound, hnext] using hbad

end D5.S3.Combinatorics.Fishburn.FishburnBasicInsertion
