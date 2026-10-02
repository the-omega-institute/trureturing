/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenNineAuxiliary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenNineAuxiliary
   mirror-E: none(waiver:auxiliary-decreasing-block-decomposition)
   anchors: []
   utility: none
   digest: A noninitial maximum in the auxiliary class separates two decreasing blocks. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenNineAuxiliary

open D5.S3.Combinatorics Nonnesting FishburnTenNineClassicalSplit

theorem auxiliary_noninitial_maxSplit_iff (left right : List ℕ) (maximum : ℕ)
    (hmax : ∀ value ∈ left ++ right, value < maximum)
    (hnodup : (left ++ maximum :: right).Nodup) (hnonempty : left ≠ []) :
    (¬ NonnestingDefs.Occurs [2, 3, 1] (left ++ maximum :: right) ∧
      ¬ NonnestingDefs.Occurs [1, 2, 3] (left ++ maximum :: right)) ↔
      left.Pairwise (· > ·) ∧ right.Pairwise (· > ·) ∧
        ∀ lower ∈ left, ∀ upper ∈ right, lower < upper := by
  have hleftnodup : left.Nodup := (List.nodup_append.mp hnodup).1
  have hrightnodup : right.Nodup :=
    (List.nodup_cons.mp (List.nodup_append.mp hnodup).2.1).2
  have hmake123 (first second last : ℕ) (h12 : first < second) (h23 : second < last)
      (hsub : [first, second, last].Sublist (left ++ maximum :: right)) :
      NonnestingDefs.Occurs [1, 2, 3] (left ++ maximum :: right) := by
    let values : ℕ → ℕ := fun rank => if rank = 1 then first
      else if rank = 2 then second else last
    refine ⟨values, ?_, ?_, by simpa [values] using hsub, by simp⟩
    · intro rank hlo hhi
      have hc : rank = 1 ∨ rank = 2 := by change rank < 3 at hhi; omega
      rcases hc with rfl | rfl <;> simpa [values]
    · intro rank hlo hhi
      have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by change rank ≤ 3 at hhi; omega
      apply hsub.subset
      rcases hc with rfl | rfl | rfl <;> simp [values]
  constructor
  · rintro ⟨h231, h123⟩
    have hseparate := (avoids231_maxSplit_iff left right maximum hmax hnodup).mp h231 |>.2.2
    refine ⟨?_, ?_, hseparate⟩
    · apply List.pairwise_iff_forall_sublist.mpr
      intro first second hpair
      have hne : first ≠ second := by
        have hp := hleftnodup.sublist hpair
        simpa using hp
      by_contra hnot
      have hsecond := hpair.subset (show second ∈ [first, second] by simp)
      have hbound := hmax second (by simp [hsecond])
      have hs : [first, second, maximum].Sublist (left ++ maximum :: right) :=
        hpair.append ((List.Sublist.refl [maximum]).trans
          (by simp : [maximum].Sublist (maximum :: right)))
      exact h123 (hmake123 first second maximum (by omega) hbound hs)
    · apply List.pairwise_iff_forall_sublist.mpr
      intro lower upper hpair
      have hne : lower ≠ upper := by
        have hp := hrightnodup.sublist hpair
        simpa using hp
      by_contra hnot
      obtain ⟨first, hfirst⟩ := List.exists_mem_of_ne_nil left hnonempty
      have hlower := hpair.subset (show lower ∈ [lower, upper] by simp)
      have hless := hseparate first hfirst lower hlower
      have hs : [first, lower, upper].Sublist (left ++ maximum :: right) :=
        (List.singleton_sublist.mpr hfirst).append (hpair.cons maximum)
      exact h123 (hmake123 first lower upper hless (by omega) hs)
  · rintro ⟨hleft, hright, hseparate⟩
    have hdecreasing231 (word : List ℕ) (hdesc : word.Pairwise (· > ·)) :
        ¬ NonnestingDefs.Occurs [2, 3, 1] word := by
      rintro ⟨values, hstep, _, hsub, _⟩
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by decide)
      have hd := List.Pairwise.sublist hsub hdesc
      simp only [List.map_cons, List.map_nil, List.pairwise_cons,
        List.mem_cons, List.not_mem_nil, or_false] at hd
      have hgt := hd.1 (values 3) (by simp)
      omega
    constructor
    · exact (avoids231_maxSplit_iff left right maximum hmax hnodup).mpr
        ⟨hdecreasing231 left hleft, hdecreasing231 right hright, hseparate⟩
    · rintro ⟨values, hstep, _, hsub, _⟩
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by decide)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by decide)
      have hincreasing : ([1, 2, 3].map values).Pairwise (· < ·) := by
        simp only [List.map_cons, List.map_nil, List.pairwise_cons,
          List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · intro value hvalue
          rcases hvalue with rfl | rfl <;> omega
        · refine ⟨?_, ?_⟩
          · intro value hvalue
            have heq : value = values 3 := by simpa using hvalue
            simpa [heq] using h23
          · simp
      have hmaximumRight : (maximum :: right).Pairwise (· > ·) := by
        apply List.pairwise_cons.mpr
        exact ⟨fun value hvalue => hmax value (by simp [hvalue]), hright⟩
      obtain ⟨selectedLeft, selectedRight, heq, hselectedLeft, hselectedRight⟩ :=
        List.sublist_append_iff.mp hsub
      have hshort (word : List ℕ) (hinc : word.Pairwise (· < ·))
          (hdec : word.Pairwise (· > ·)) : word.length ≤ 1 := by
        cases word with
        | nil => simp
        | cons head tail =>
          cases tail with
          | nil => simp
          | cons second rest =>
            have hless := (List.pairwise_cons.mp hinc).1 second (by simp)
            have hgreater := (List.pairwise_cons.mp hdec).1 second (by simp)
            omega
      have hincLeft : selectedLeft.Pairwise (· < ·) := by
        apply List.Pairwise.sublist _ hincreasing
        rw [heq]
        exact List.sublist_append_left _ _
      have hincRight : selectedRight.Pairwise (· < ·) := by
        apply List.Pairwise.sublist _ hincreasing
        rw [heq]
        exact List.sublist_append_right _ _
      have hl := hshort selectedLeft hincLeft (List.Pairwise.sublist hselectedLeft hleft)
      have hr := hshort selectedRight hincRight
        (List.Pairwise.sublist hselectedRight hmaximumRight)
      have hlength := congrArg List.length heq
      simp only [List.length_map, List.length_cons, List.length_nil,
        List.length_append] at hlength
      omega

end D5.S3.Combinatorics.Fishburn.FishburnTenNineAuxiliary
