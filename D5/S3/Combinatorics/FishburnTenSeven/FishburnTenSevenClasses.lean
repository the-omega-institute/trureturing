/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenClasses
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenClasses
   mirror-E: none(waiver:crossing-block-pattern-analysis)
   anchors: []
   utility: none
   digest: Crossing witnesses characterize the first and third classes on their common shape. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenClasses

open D5.S3.Combinatorics Nonnesting Fishburn.FishburnDefs
open FishburnTenSevenMinimum FishburnTenSevenShape

theorem shape_classes_iff (n : ℕ) (decreasing increasing trailing : List ℕ) (peak : ℕ)
    (hperm : (decreasing ++ 1 :: (increasing ++ peak :: trailing)).Perm (List.range' 1 n))
    (hdecreasing : decreasing.Pairwise (· > ·))
    (hincreasing : increasing.Pairwise (· < ·)) (htrailing : trailing.Pairwise (· > ·))
    (hmax : ∀ value ∈ increasing ++ trailing, value < peak) :
    ((decreasing ++ 1 :: (increasing ++ peak :: trailing)) ∈
        avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [1, 4, 2, 3]] ↔
      (∀ value ∈ trailing, value + 1 ∉ increasing) ∧
        ∀ value ∈ trailing, ∀ earlier ∈ decreasing, value < earlier) ∧
    ((decreasing ++ 1 :: (increasing ++ peak :: trailing)) ∈
        avoiders n [[1, 3, 2, 4], [1, 4, 2, 3], [3, 1, 2, 4]] ↔
      (∀ value ∈ trailing, value + 1 ∉ increasing) ∧
        ∀ value ∈ decreasing, value < peak → ∀ later ∈ increasing, value < later) := by
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
  have hbeforemem (index : ℕ) (hi : index < decreasing.length) :
      word.getD index 0 ∈ decreasing := by
    rw [hbefore index hi, List.getD_eq_getElem decreasing 0 hi]
    exact List.getElem_mem hi
  have hincmem (index : ℕ) (hlo : start ≤ index) (hhi : index < top) :
      word.getD index 0 ∈ increasing := by
    rw [hinc index hlo hhi, List.getD_eq_getElem increasing 0 (by dsimp [top] at hhi; omega)]
    exact List.getElem_mem (by dsimp [top] at hhi; omega)
  have htrailmem (index : ℕ) (hlo : finish ≤ index) (hhi : index < word.length) :
      word.getD index 0 ∈ trailing := by
    rw [htrail index hlo, List.getD_eq_getElem trailing 0 (by omega)]
    exact List.getElem_mem (by omega)
  have hprefixpair (first second : ℕ) (hlo : start ≤ first) (horder : first < second)
      (hhi : second ≤ top) : word.getD first 0 < word.getD second 0 := by
    by_cases hsecond : second < top
    · rw [hinc first hlo (by omega), hinc second (by omega) hsecond]
      rw [List.getD_eq_getElem increasing 0 (by dsimp [top] at hsecond; omega),
        List.getD_eq_getElem increasing 0 (by dsimp [top] at hsecond; omega)]
      exact List.pairwise_iff_getElem.mp hincreasing _ _ _ _ (by omega)
    · have heq : second = top := by omega
      rw [heq, hpeak]
      exact hmax _ (List.mem_append_left _ (hincmem first hlo (by omega)))
  have htrailpair (first second : ℕ) (hlo : finish ≤ first) (horder : first < second)
      (hhi : second < word.length) : word.getD second 0 < word.getD first 0 := by
    rw [htrail first hlo, htrail second (by omega)]
    rw [List.getD_eq_getElem trailing 0 (by omega),
      List.getD_eq_getElem trailing 0 (by omega)]
    exact List.pairwise_iff_getElem.mp htrailing _ _ _ _ (by omega)
  have hsuffixmax (index : ℕ) (hlo : start ≤ index) (hhi : index < word.length) :
      word.getD index 0 ≤ peak := by
    rcases lt_trichotomy index top with hlt | heq | hgt
    · exact (hmax _ (List.mem_append_left _ (hincmem index hlo hlt))).le
    · exact (heq ▸ hpeak).le
    · exact (hmax _ (List.mem_append_right _
        (htrailmem index (by dsimp [finish]; omega) hhi))).le
  have hdistinct (value : ℕ) (hvalue : value ∈ decreasing)
      (other : ℕ) (hother : other ∈ increasing ++ trailing) : value ≠ other := by
    have hdisjoint := (List.nodup_append.mp hnodup).2.2
    intro heq
    apply hdisjoint value hvalue other ?_ heq
    simp only [List.mem_cons, List.mem_append]
    rcases List.mem_append.mp hother with hi | hj
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inr hj))
  have htests (hfish : IsFishburn word) :=
    minimum_pattern_tests n word hperm hfish decreasing.length
      (by dsimp [word]; simp) hone
  have hcommon (hfish : IsFishburn word) :
      ¬ NonnestingDefs.Occurs [1, 3, 2, 4] word ∧
        ¬ NonnestingDefs.Occurs [1, 4, 2, 3] word := by
    have htest := htests hfish
    constructor
    · intro hoccurs
      obtain ⟨first, second, third, hf, hs, ht, hb, hl, hu⟩ := htest.1.mp hoccurs
      by_cases hsecond : second ≤ top
      · have hincpair := hprefixpair first second (by dsimp [start]; omega) hs hsecond
        omega
      · have hdec := htrailpair second third (by dsimp [finish]; omega) ht hb
        omega
    · intro hoccurs
      obtain ⟨first, second, third, hf, hs, ht, hb, hl, hu⟩ := htest.2.1.mp hoccurs
      by_cases hsecond : second ≤ top
      · have hincpair := hprefixpair first second (by dsimp [start]; omega) hs hsecond
        omega
      · have hdec := htrailpair second third (by dsimp [finish]; omega) ht hb
        omega
  have hcross214 (hfish : IsFishburn word) :
      NonnestingDefs.Occurs [2, 1, 4, 3] word ↔
        ∃ value ∈ decreasing, ∃ later ∈ trailing, value < later := by
    have htest := ((htests hfish).2.2 (hcommon hfish).1).1
    constructor
    · intro hoccurs
      obtain ⟨first, second, third, hf, hs, ht, hb, hl, hu⟩ := htest.mp hoccurs
      have hthird : finish ≤ third := by
        by_contra hnot
        have hlt := hprefixpair second third (by dsimp [start]; omega) ht
          (by dsimp [finish] at hnot; omega)
        omega
      exact ⟨_, hbeforemem first hf, _, htrailmem third hthird hb, hl⟩
    · rintro ⟨value, hv, later, hl, horder⟩
      obtain ⟨first, hf, hfv⟩ := List.mem_iff_getElem.mp hv
      obtain ⟨last, ht, htv⟩ := List.mem_iff_getElem.mp hl
      have hfirstval : word.getD first 0 = value := by
        rw [hbefore first hf, List.getD_eq_getElem decreasing 0 hf, hfv]
      have hlastval : word.getD (finish + last) 0 = later := by
        rw [htrail _ (by omega)]
        simp only [Nat.add_sub_cancel_left, List.getD_eq_getElem trailing 0 ht, htv]
      have hlastbound := hmax later (List.mem_append_right _ hl)
      apply htest.mpr
      refine ⟨first, top, finish + last, hf, ?_, ?_, by omega, ?_, ?_⟩
      · dsimp [top, start]; omega
      · dsimp [finish]; omega
      · omega
      · omega
  have hcross312 (hfish : IsFishburn word) :
      NonnestingDefs.Occurs [3, 1, 2, 4] word ↔
        ∃ value ∈ decreasing, value < peak ∧ ∃ later ∈ increasing, later < value := by
    have htest := ((htests hfish).2.2 (hcommon hfish).1).2
    constructor
    · intro hoccurs
      obtain ⟨first, second, third, hf, hs, ht, hb, hl, hu⟩ := htest.mp hoccurs
      have hsecond : second < top := by
        by_contra hnot
        by_cases heq : second = top
        · have hsecondpeak := heq ▸ hpeak
          have hlastmax := hsuffixmax third (by dsimp [start]; omega) hb
          omega
        · have hdec := htrailpair second third (by dsimp [finish]; omega) ht hb
          omega
      have hlastmax := hsuffixmax third (by dsimp [start]; omega) hb
      exact ⟨_, hbeforemem first hf, by omega,
        _, hincmem second (by dsimp [start]; omega) hsecond, hl⟩
    · rintro ⟨value, hv, hbound, later, hl, horder⟩
      obtain ⟨first, hf, hfv⟩ := List.mem_iff_getElem.mp hv
      obtain ⟨second, hs, hsv⟩ := List.mem_iff_getElem.mp hl
      have hfirstval : word.getD first 0 = value := by
        rw [hbefore first hf, List.getD_eq_getElem decreasing 0 hf, hfv]
      have hsecondval : word.getD (start + second) 0 = later := by
        rw [hinc _ (by omega) (by dsimp [top]; omega)]
        simp only [Nat.add_sub_cancel_left, List.getD_eq_getElem increasing 0 hs, hsv]
      apply htest.mpr
      refine ⟨first, start + second, top, hf, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp [start]; omega
      · dsimp [top]; omega
      · dsimp [finish] at hlength; omega
      · omega
      · omega
  have hfishiff := shape_fishburn_iff n decreasing increasing trailing peak
    hperm hdecreasing hincreasing htrailing hmax
  have h214iff (hfish : IsFishburn word) :
      ¬ NonnestingDefs.Occurs [2, 1, 4, 3] word ↔
        ∀ value ∈ trailing, ∀ earlier ∈ decreasing, value < earlier := by
    constructor
    · intro hav value hv earlier he
      have hne := hdistinct earlier he value (List.mem_append_right _ hv)
      by_contra hnot
      exact hav ((hcross214 hfish).mpr ⟨earlier, he, value, hv, by omega⟩)
    · intro horder hoccurs
      obtain ⟨earlier, he, value, hv, hlt⟩ := (hcross214 hfish).mp hoccurs
      have := horder value hv earlier he
      omega
  have h312iff (hfish : IsFishburn word) :
      ¬ NonnestingDefs.Occurs [3, 1, 2, 4] word ↔
        ∀ value ∈ decreasing, value < peak → ∀ later ∈ increasing, value < later := by
    constructor
    · intro hav value hv hb later hl
      have hne := hdistinct value hv later (List.mem_append_left _ hl)
      by_contra hnot
      exact hav ((hcross312 hfish).mpr ⟨value, hv, hb, later, hl, by omega⟩)
    · intro horder hoccurs
      obtain ⟨value, hv, hb, later, hl, hlt⟩ := (hcross312 hfish).mp hoccurs
      have := horder value hv hb later hl
      omega
  change (word ∈ _ ↔ _) ∧ (word ∈ _ ↔ _)
  constructor
  · constructor
    · rintro ⟨_, hfish, hav⟩
      refine ⟨hfishiff.mp hfish, (h214iff hfish).mp (hav _ (by simp))⟩
    · rintro ⟨hcondition, horder⟩
      have hfish := hfishiff.mpr hcondition
      have hcommonavoid := hcommon hfish
      refine ⟨hperm, hfish, ?_⟩
      intro pattern hpattern
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl
      · exact hcommonavoid.1
      · exact (h214iff hfish).mpr horder
      · exact hcommonavoid.2
  · constructor
    · rintro ⟨_, hfish, hav⟩
      refine ⟨hfishiff.mp hfish, (h312iff hfish).mp (hav _ (by simp))⟩
    · rintro ⟨hcondition, horder⟩
      have hfish := hfishiff.mpr hcondition
      have hcommonavoid := hcommon hfish
      refine ⟨hperm, hfish, ?_⟩
      intro pattern hpattern
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl
      · exact hcommonavoid.1
      · exact hcommonavoid.2
      · exact (h312iff hfish).mpr horder

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenClasses
