/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenShape
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenShape
   mirror-E: none(waiver:block-predecessor-analysis)
   anchors: []
   utility: none
   digest: In a decreasing-increasing-decreasing shape only a trailing predecessor is forbidden. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenMinimum
import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenUnimodal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenShape

open D5.S3.Combinatorics
open Fishburn.FishburnDefs

theorem shape_fishburn_iff (n : ℕ) (decreasing increasing trailing : List ℕ) (peak : ℕ)
    (hperm : (decreasing ++ 1 :: (increasing ++ peak :: trailing)).Perm (List.range' 1 n))
    (hdecreasing : decreasing.Pairwise (· > ·))
    (hincreasing : increasing.Pairwise (· < ·)) (htrailing : trailing.Pairwise (· > ·))
    (hmax : ∀ value ∈ increasing ++ trailing, value < peak) :
    IsFishburn (decreasing ++ 1 :: (increasing ++ peak :: trailing)) ↔
      ∀ value ∈ trailing, value + 1 ∉ increasing := by
  let word := decreasing ++ 1 :: (increasing ++ peak :: trailing)
  let start := decreasing.length + 1
  let top := start + increasing.length
  let finish := top + 1
  have hlength : word.length = finish + trailing.length := by
    simp only [word, finish, top, start, List.length_append, List.length_cons]
    omega
  have hnodup : word.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hbefore (index : ℕ) (hindex : index < decreasing.length) :
      word.getD index 0 = decreasing.getD index 0 := List.getD_append _ _ _ _ hindex
  have hone : word.getD decreasing.length 0 = 1 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp
  have htail (index : ℕ) (hindex : start ≤ index) :
      word.getD index 0 = (increasing ++ peak :: trailing).getD (index - start) 0 := by
    rw [List.getD_append_right _ _ _ _ (by dsimp [start] at hindex; omega)]
    have hdiff : index - decreasing.length = (index - start) + 1 := by
      dsimp [start] at *
      omega
    rw [hdiff]
    rfl
  have hinc (index : ℕ) (hlo : start ≤ index) (hhi : index < top) :
      word.getD index 0 = increasing.getD (index - start) 0 := by
    rw [htail index hlo, List.getD_append _ _ _ _ (by dsimp [top] at hhi; omega)]
  have hpeak : word.getD top 0 = peak := by
    rw [htail top (by dsimp [top]; omega)]
    have hdiff : top - start = increasing.length := by dsimp [top]; omega
    rw [hdiff, List.getD_append_right _ _ _ _ (by omega)]
    simp
  have htrail (index : ℕ) (hindex : finish ≤ index) :
      word.getD index 0 = trailing.getD (index - finish) 0 := by
    rw [htail index (by dsimp [finish, top] at hindex; omega)]
    rw [List.getD_append_right _ _ _ _ (by dsimp [finish, top] at hindex; omega)]
    have hdiff : index - start - increasing.length = (index - finish) + 1 := by
      dsimp [finish, top] at hindex ⊢
      omega
    rw [hdiff]
    rfl
  have hpositive (index : ℕ) (hindex : index < word.length) : 1 ≤ word.getD index 0 := by
    have hmem : word.getD index 0 ∈ word := by
      rw [List.getD_eq_getElem word 0 hindex]
      exact List.getElem_mem hindex
    have hrange := hperm.mem_iff.mp hmem
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, _, hvalue⟩ := hrange
    omega
  have hnotone (index : ℕ) (hindex : index < word.length)
      (hne : index ≠ decreasing.length) : 1 < word.getD index 0 := by
    have hpos := hpositive index hindex
    have hvalue : word.getD index 0 ≠ 1 := by
      intro heq
      apply hne
      exact (List.getD_inj hindex (by dsimp [word]; simp) hnodup).mp
        (heq.trans hone.symm)
    omega
  have hincmem (index : ℕ) (hlo : start ≤ index) (hhi : index < top) :
      word.getD index 0 ∈ increasing := by
    rw [hinc index hlo hhi, List.getD_eq_getElem increasing 0 (by dsimp [top] at hhi; omega)]
    exact List.getElem_mem (by dsimp [top] at hhi; omega)
  have htrailmem (index : ℕ) (hlo : finish ≤ index) (hhi : index < word.length) :
      word.getD index 0 ∈ trailing := by
    rw [htrail index hlo, List.getD_eq_getElem trailing 0 (by omega)]
    exact List.getElem_mem (by omega)
  have hincpair (first second : ℕ) (hlo : start ≤ first) (horder : first < second)
      (hhi : second < top) : word.getD first 0 < word.getD second 0 := by
    rw [hinc first hlo (by omega), hinc second (by omega) hhi]
    rw [List.getD_eq_getElem increasing 0 (by dsimp [top] at hhi; omega),
      List.getD_eq_getElem increasing 0 (by dsimp [top] at hhi; omega)]
    exact List.pairwise_iff_getElem.mp hincreasing _ _ _ _ (by omega)
  have htrailpair (first second : ℕ) (hlo : finish ≤ first) (horder : first < second)
      (hhi : second < word.length) : word.getD second 0 < word.getD first 0 := by
    rw [htrail first hlo, htrail second (by omega)]
    rw [List.getD_eq_getElem trailing 0 (by omega),
      List.getD_eq_getElem trailing 0 (by omega)]
    exact List.pairwise_iff_getElem.mp htrailing _ _ _ _ (by omega)
  have hincnext (index : ℕ) (hlo : start ≤ index) (hhi : index < top) :
      word.getD index 0 < word.getD (index + 1) 0 := by
    by_cases hnext : index + 1 < top
    · exact hincpair index (index + 1) hlo (by omega) hnext
    · have heq : index + 1 = top := by omega
      rw [heq, hpeak]
      exact hmax _ (List.mem_append_left _ (hincmem index hlo hhi))
  change IsFishburn word ↔ _
  constructor
  · intro hfish value hvalue hsuccessor
    obtain ⟨before, hbeforebound, hbeforevalue⟩ := List.mem_iff_getElem.mp hsuccessor
    obtain ⟨after, hafterbound, haftervalue⟩ := List.mem_iff_getElem.mp hvalue
    have hbeforepos : word.getD (start + before) 0 = value + 1 := by
      rw [hinc _ (by omega) (by dsimp [top]; omega)]
      simp only [Nat.add_sub_cancel_left, List.getD_eq_getElem increasing 0 hbeforebound,
        hbeforevalue]
    have hafterpos : word.getD (finish + after) 0 = value := by
      rw [htrail _ (by omega)]
      simp only [Nat.add_sub_cancel_left, List.getD_eq_getElem trailing 0 hafterbound,
        haftervalue]
    have hascent := hincnext (start + before) (by omega) (by dsimp [top]; omega)
    exact hfish (start + before) (finish + after)
      (by dsimp [finish, top]; omega) (by omega)
      ⟨by omega, by omega⟩
  · intro hcondition before after hgap hafterbound hbad
    have hbeforebound : before < word.length := by omega
    have hnextbound : before + 1 < word.length := by omega
    rcases lt_trichotomy before decreasing.length with hleft | honepos | hright
    · by_cases hnext : before + 1 < decreasing.length
      · have hdec := List.pairwise_iff_getElem.mp hdecreasing before (before + 1)
          hleft hnext (by omega)
        have hb := hbefore before hleft
        have hn := hbefore (before + 1) hnext
        rw [List.getD_eq_getElem decreasing 0 hleft] at hb
        rw [List.getD_eq_getElem decreasing 0 hnext] at hn
        omega
      · have hnextone : before + 1 = decreasing.length := by omega
        have hn : word.getD (before + 1) 0 = 1 := hnextone ▸ hone
        have hb := hpositive before hbeforebound
        omega
    · have hv : word.getD before 0 = 1 := honepos ▸ hone
      have hp := hpositive after hafterbound
      omega
    · have hstart : start ≤ before := by dsimp [start]; omega
      rcases lt_trichotomy before top with hin | hat | hout
      · by_cases hafterinc : after < top
        · have hlt := hincpair before after hstart (by omega) hafterinc
          omega
        · by_cases hafterpeak : after = top
          · have hb := hmax _ (List.mem_append_left _ (hincmem before hstart hin))
            have ha : word.getD after 0 = peak := hafterpeak ▸ hpeak
            omega
          · have haftertrail : finish ≤ after := by dsimp [finish]; omega
            have hpred := htrailmem after haftertrail hafterbound
            have hsucc := hincmem before hstart hin
            apply hcondition _ hpred
            simpa only [hbad.1] using hsucc
      · have hv : word.getD before 0 = peak := hat ▸ hpeak
        have haftertrail : finish ≤ before + 1 := by dsimp [finish]; omega
        have hnext := hmax _ (List.mem_append_right _
          (htrailmem (before + 1) haftertrail hnextbound))
        omega
      · have hfinish : finish ≤ before := by dsimp [finish]; omega
        have hnext := htrailpair before (before + 1) hfinish (by omega) hnextbound
        omega

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenShape
