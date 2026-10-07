/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingOutside
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingOutside
   mirror-E: none(waiver:non-extreme-ascending-endpoint-normal-form)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: An ascending middle pair encloses the decreasing lower and upper blocks. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscendingOutside

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

set_option maxHeartbeats 1200000 in
theorem ascending_nonextreme_normal_form (size first last : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size) (hfirst : 1 ≤ first) (horder : first < last)
    (houtside : 1 < first ∨ last < size)
    (hperm : (first :: interior ++ [last]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [1, 2, 3, 4] ((first :: interior ++ [last]).rotate cut) ↔ cut = 0) :
    first + 2 < last ∧ ∃ before after : List ℕ,
      interior = before ++ (List.range' 1 (first - 1)).reverse ++
        (List.range' (last + 1) (size - last)).reverse ++ after ∧
      (before ++ after).Perm (List.range' (first + 1) (last - first - 1)) ∧
      before.Pairwise (· > ·) ∧ after.Pairwise (· > ·) ∧
      ∃ low ∈ before, ∃ high ∈ after, low < high := by
  classical
  let word := first :: interior ++ [last]
  let isOutside := fun value : ℕ => decide (value < first ∨ last < value)
  let isLower := fun value : ℕ => decide (value < first)
  let isUpper := fun value : ℕ => decide (last < value)
  have criterion := (unique_bad_cut_iff size hsize [1, 2, 3, 4] word
    (by decide) hperm).mp hcuts
  have dropWord : word.dropLast = first :: interior := by
    change ((first :: interior) ++ [last]).dropLast = _
    rw [List.dropLast_append_cons]; simp
  have wordNodup := hperm.nodup_iff.mpr List.nodup_range'
  have interiorNodup := (List.nodup_cons.mp wordNodup).2.sublist
    (List.sublist_append_left interior [last])
  have notFirst : first ∉ interior := fun hv =>
    (List.nodup_cons.mp wordNodup).1 (List.mem_append_left _ hv)
  have notLast : last ∉ interior := fun hv =>
    (List.nodup_append.mp (List.nodup_cons.mp wordNodup).2).2.2
      last hv last (by simp) rfl
  have bounds (value : ℕ) (hv : value ∈ word) : 1 ≤ value ∧ value ≤ size := by
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hv)
    omega
  have lastBound := bounds last (by simp [word])
  have colors (value : ℕ) (hv : value ∈ interior) :
      value < first ∨ (first < value ∧ value < last) ∨ last < value := by
    have hn : value ≠ first := fun he => notFirst (he ▸ hv)
    have hn' : value ≠ last := fun he => notLast (he ▸ hv)
    omega
  have build (pattern container : List ℕ) (chosen : ℕ → ℕ)
      (hp : pattern.Perm [1, 2, 3, 4]) (hl : letters pattern = 4)
      (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1))
      (hs : (pattern.map chosen).Sublist container) : Occurs pattern container := by
    refine ⟨chosen, ?_, ?_, hs, by simp⟩
    · simpa only [hl] using hi
    · intro rank hlo hhi
      rw [hl] at hhi
      apply hs.subset
      apply List.mem_map_of_mem
      apply hp.mem_iff.mpr
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
      rcases hh with rfl | rfl | rfl | rfl <;> simp
  have noOutsideAscent (extra low high : ℕ)
      (hs : [extra, low, high].Sublist interior)
      (he : extra < first ∨ last < extra)
      (hl : first < low) (hh : high < last) (ha : low < high) : False := by
    rcases he with he | he
    · let chosen := fun rank : ℕ => if rank = 1 then extra else if rank = 2 then low
        else if rank = 3 then high else last
      apply criterion.2.2.1
      change Occurs [1, 2, 3, 4] (interior ++ [last])
      refine build _ _ chosen (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · simpa [chosen] using hs.append (List.Sublist.refl [last])
    · let chosen := fun rank : ℕ => if rank = 1 then low else if rank = 2 then high
        else if rank = 3 then last else extra
      apply criterion.2.1 3 (by omega) (by omega)
      change Occurs [4, 1, 2, 3] word
      refine build _ _ chosen (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · simpa [word, chosen] using (hs.append (List.Sublist.refl [last])).cons first
  have noAscentOutside (low high extra : ℕ)
      (hs : [low, high, extra].Sublist interior)
      (hl : first < low) (hh : high < last) (ha : low < high)
      (he : extra < first ∨ last < extra) : False := by
    rcases he with he | he
    · let chosen := fun rank : ℕ => if rank = 1 then extra else if rank = 2 then first
        else if rank = 3 then low else high
      apply criterion.2.1 1 (by omega) (by omega)
      change Occurs [2, 3, 4, 1] word
      refine build _ _ chosen (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · simpa [word, chosen] using (hs.cons_cons first).trans
          (List.sublist_append_left (first :: interior) [last])
    · let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then low
        else if rank = 3 then high else extra
      apply criterion.2.2.2
      rw [dropWord]
      refine build _ _ chosen (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · simpa [chosen] using hs.cons_cons first
  obtain ⟨chosen, hi, _, selected, _⟩ := criterion.1
  have chosen12 : chosen 1 < chosen 2 := by simpa using hi 1 (by omega) (by decide)
  have chosen23 : chosen 2 < chosen 3 := by simpa using hi 2 (by omega) (by decide)
  have chosen34 : chosen 3 < chosen 4 := by simpa using hi 3 (by omega) (by decide)
  have chosenFirst : chosen 1 = first := by
    by_contra hne
    exact criterion.2.2.1
      (build _ word.tail chosen (by decide) rfl hi (List.Sublist.of_cons_of_ne hne selected))
  have chosenLast : chosen 4 = last := by
    by_contra hne
    have hs : [chosen 4, chosen 3, chosen 2, chosen 1].Sublist
        (last :: interior.reverse ++ [first]) := by
      simpa [word] using selected.reverse
    have hs := List.Sublist.of_cons_of_ne hne hs
    have ht : ([1, 2, 3, 4].map chosen).Sublist (first :: interior) := by
      simpa using hs.reverse
    exact criterion.2.2.2 (build _ word.dropLast chosen (by decide) rfl hi (dropWord.symm ▸ ht))
  let low := chosen 2
  let high := chosen 3
  have lowBound : first < low := by dsimp [low]; omega
  have highBound : high < last := by dsimp [high]; omega
  have ascent : low < high := chosen23
  have pair : [low, high].Sublist interior := by
    have hs : [low, high, last].Sublist (interior ++ [last]) := by
      apply (List.cons_sublist_cons (a := first)).mp
      simpa [word, chosenFirst, chosenLast, low, high] using selected
    have hr : (last :: [high, low]).Sublist (last :: interior.reverse) := by
      simpa using hs.reverse
    simpa using (List.cons_sublist_cons.mp hr).reverse
  have pairOrder (container : List ℕ) (left right : ℕ)
      (hl : left ∈ container) (hr : right ∈ container) (hne : left ≠ right) :
      [left, right].Sublist container ∨ [right, left].Sublist container := by
    induction container with
    | nil => simp at hl
    | cons head tail ih =>
      by_cases hheadLeft : head = left
      · subst head
        have hh : right ∈ tail := (List.mem_cons.mp hr).resolve_left (Ne.symm hne)
        exact Or.inl ((List.singleton_sublist.mpr hh).cons_cons left)
      · by_cases hheadRight : head = right
        · subst head
          have hh : left ∈ tail := (List.mem_cons.mp hl).resolve_left hne
          exact Or.inr ((List.singleton_sublist.mpr hh).cons_cons right)
        · rcases ih ((List.mem_cons.mp hl).resolve_left (Ne.symm hheadLeft))
            ((List.mem_cons.mp hr).resolve_left (Ne.symm hheadRight)) with hh | hh
          · exact Or.inl (hh.cons head)
          · exact Or.inr (hh.cons head)
  have insertThird (container : List ℕ) (left right extra : ℕ)
      (hs : [left, right].Sublist container) (hm : extra ∈ container)
      (hneLeft : extra ≠ left) (hneRight : extra ≠ right) :
      [extra, left, right].Sublist container ∨ [left, extra, right].Sublist container ∨
        [left, right, extra].Sublist container := by
    induction container with
    | nil => simp at hm
    | cons head tail ih =>
      by_cases hheadLeft : head = left
      · subst head
        have ht : right ∈ tail := List.singleton_sublist.mp (List.cons_sublist_cons.mp hs)
        have he : extra ∈ tail := (List.mem_cons.mp hm).resolve_left hneLeft
        rcases pairOrder tail extra right he ht hneRight with hh | hh
        · exact Or.inr (Or.inl (hh.cons_cons left))
        · exact Or.inr (Or.inr (hh.cons_cons left))
      · have ht := List.Sublist.of_cons_of_ne (Ne.symm hheadLeft) hs
        by_cases hheadExtra : head = extra
        · subst head
          exact Or.inl (ht.cons_cons extra)
        · rcases ih ht ((List.mem_cons.mp hm).resolve_left (Ne.symm hheadExtra)) with
            hh | hh | hh
          · exact Or.inl (hh.cons head)
          · exact Or.inr (Or.inl (hh.cons head))
          · exact Or.inr (Or.inr (hh.cons head))
  have chain (container : List ℕ) (left pivot right : ℕ) (hn : container.Nodup)
      (hl : [left, pivot].Sublist container) (hr : [pivot, right].Sublist container) :
      [left, pivot, right].Sublist container := by
    induction container with
    | nil => simp at hl
    | cons head tail ih =>
      have ht := (List.nodup_cons.mp hn).2
      by_cases hheadLeft : head = left
      · subst head
        have hne : pivot ≠ left := by
          have hh := hn.sublist hl
          have hne : left ≠ pivot := by simpa using (List.nodup_cons.mp hh).1
          exact Ne.symm hne
        exact (List.Sublist.of_cons_of_ne hne hr).cons_cons left
      · have hlTail := List.Sublist.of_cons_of_ne (Ne.symm hheadLeft) hl
        have hne : pivot ≠ head := by
          intro heq
          exact (List.nodup_cons.mp hn).1 (heq ▸ hlTail.subset (by simp))
        exact (ih ht hlTail (List.Sublist.of_cons_of_ne hne hr)).cons head
  have enclosed (extra : ℕ) (hm : extra ∈ interior)
      (he : extra < first ∨ last < extra) : [low, extra, high].Sublist interior := by
    have hnlow : extra ≠ low := by rcases he with he | he <;> omega
    have hnhigh : extra ≠ high := by rcases he with he | he <;> omega
    rcases insertThird interior low high extra pair hm hnlow hnhigh with hh | hh | hh
    · exact False.elim (noOutsideAscent _ _ _ hh he lowBound highBound ascent)
    · exact hh
    · exact False.elim (noAscentOutside _ _ _ hh lowBound highBound ascent he)
  have lowBefore (extra : ℕ) (hm : extra ∈ interior)
      (he : extra < first ∨ last < extra) : [low, extra].Sublist interior :=
    (List.sublist_append_left [low, extra] [high]).trans (enclosed extra hm he)
  have highAfter (extra : ℕ) (hm : extra ∈ interior)
      (he : extra < first ∨ last < extra) : [extra, high].Sublist interior :=
    (List.sublist_cons_self low _).trans (enclosed extra hm he)
  have noHole (left extra right : ℕ) (hs : [left, extra, right].Sublist interior)
      (hl : left < first ∨ last < left) (hr : right < first ∨ last < right)
      (he : first < extra ∧ extra < last) : False := by
    have hleftExtra : [left, extra].Sublist interior :=
      (List.sublist_append_left [left, extra] [right]).trans hs
    have hextraRight : [extra, right].Sublist interior :=
      (List.sublist_cons_self _ _).trans hs
    by_cases ha : low < extra
    · have triple := chain interior low left extra interiorNodup
        (lowBefore left (hs.subset (by simp)) hl) hleftExtra
      have hp : [low, extra].Sublist interior :=
        ((List.sublist_cons_self left [extra]).cons_cons low).trans triple
      exact noAscentOutside low extra right
        (chain interior low extra right interiorNodup hp hextraRight) lowBound he.2 ha hr
    · have triple := chain interior extra right high interiorNodup hextraRight
        (highAfter right (hs.subset (by simp)) hr)
      have hp : [extra, high].Sublist interior :=
        ((List.sublist_cons_self right [high]).cons_cons extra).trans triple
      exact noOutsideAscent left extra high
        (chain interior left extra high interiorNodup hleftExtra hp) hl he.1 highBound
          (by omega)
  have contiguous (container : List ℕ)
      (hno : ∀ left extra right, [left, extra, right].Sublist container →
        isOutside left = true → isOutside right = true → isOutside extra = false → False)
      (hex : ∃ value ∈ container, isOutside value = true) :
      ∃ before after, container = before ++ container.filter isOutside ++ after ∧
        (∀ value ∈ before, isOutside value = false) ∧
        (∀ value ∈ after, isOutside value = false) := by
    induction container with
    | nil => simpa using hex
    | cons head tail ih =>
      by_cases htail : ∃ value ∈ tail, isOutside value = true
      · obtain ⟨before, after, heq, hp, hs⟩ := ih
          (by intro left extra right hh hl hr he; exact hno _ _ _ (hh.cons head) hl hr he)
          htail
        by_cases hhead : isOutside head = true
        · have hempty : before = [] := by
            cases before with
            | nil => rfl
            | cons extra rest =>
              obtain ⟨value, hv, hm⟩ := htail
              have hf : value ∈ tail.filter isOutside := List.mem_filter.mpr ⟨hv, hm⟩
              have hselected : [head, extra, value].Sublist (head :: tail) := by
                rw [heq]
                apply List.Sublist.cons_cons
                apply List.Sublist.cons_cons
                exact (List.singleton_sublist.mpr hf).trans
                  ((List.sublist_append_right rest _).trans (List.sublist_append_left _ after))
              exact False.elim (hno head extra value hselected hhead hm (hp extra (by simp)))
          subst before
          refine ⟨[], after, ?_, by simp, hs⟩
          simpa [List.filter_cons, hhead] using congrArg (List.cons head) heq
        · have hf : isOutside head = false := Bool.eq_false_iff.mpr hhead
          refine ⟨head :: before, after, ?_, ?_, hs⟩
          · simpa [List.filter_cons, hf] using congrArg (List.cons head) heq
          · intro value hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact hf
            · exact hp value hv
      · have ht : ∀ value ∈ tail, isOutside value = false := by
          intro value hv
          apply Bool.eq_false_iff.mpr
          intro hm
          exact htail ⟨value, hv, hm⟩
        have hhead : isOutside head = true := by
          obtain ⟨value, hv, hm⟩ := hex
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hm
          · exact False.elim (htail ⟨value, hv, hm⟩)
        have htfilter : tail.filter isOutside = [] := List.filter_eq_nil_iff.mpr
          (by intro value hv; simp [ht value hv])
        exact ⟨[], tail, by simp [List.filter_cons, hhead, htfilter], by simp, ht⟩
  have outsideExists : ∃ value ∈ interior, isOutside value = true := by
    rcases houtside with hh | hh
    · have hv : 1 ∈ word := hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      have hv : 1 ∈ interior := by
        simpa [word, show 1 ≠ first by omega, show 1 ≠ last by omega] using hv
      exact ⟨1, hv, by simp [isOutside]; omega⟩
    · have hv : size ∈ word := hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      have hv : size ∈ interior := by
        simpa [word, show size ≠ first by omega, show size ≠ last by omega] using hv
      exact ⟨size, hv, by simp [isOutside]; omega⟩
  obtain ⟨before, after, split, prefixMiddle, suffixMiddle⟩ := contiguous interior
    (by
      intro left extra right hs hl hr he
      have he := of_decide_eq_false he
      rcases colors extra (hs.subset (by simp)) with hh | hh | hh
      · exact he (Or.inl hh)
      · exact noHole left extra right hs (of_decide_eq_true hl) (of_decide_eq_true hr) hh
      · exact he (Or.inr hh)) outsideExists
  let outside := interior.filter isOutside
  change interior = before ++ outside ++ after at split
  have prefixSub : before.Sublist interior := by
    rw [split]
    exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)
  have afterSub : after.Sublist interior := by rw [split]; exact List.sublist_append_right _ _
  have beforeBounds (value : ℕ) (hv : value ∈ before) : first < value ∧ value < last := by
    have hh := of_decide_eq_false (prefixMiddle value hv)
    rcases colors value (prefixSub.subset hv) with hl | hm | hu
    · exact False.elim (hh (Or.inl hl))
    · exact hm
    · exact False.elim (hh (Or.inr hu))
  have afterBounds (value : ℕ) (hv : value ∈ after) : first < value ∧ value < last := by
    have hh := of_decide_eq_false (suffixMiddle value hv)
    rcases colors value (afterSub.subset hv) with hl | hm | hu
    · exact False.elim (hh (Or.inl hl))
    · exact hm
    · exact False.elim (hh (Or.inr hu))
  obtain ⟨outsideValue, outsideMem, outsideColor⟩ := outsideExists
  have outsideValueMem : outsideValue ∈ outside := List.mem_filter.mpr
    ⟨outsideMem, outsideColor⟩
  have outsideBounds := of_decide_eq_true outsideColor
  have beforeSorted : before.Pairwise (· > ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := beforeBounds left (hs.subset (by simp))
    have hr := beforeBounds right (hs.subset (by simp))
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp ((interiorNodup.sublist prefixSub).sublist hs)).1
    by_contra hnot
    have hp : [left, right, outsideValue].Sublist interior := by
      rw [split]
      exact (hs.append (List.singleton_sublist.mpr outsideValueMem)).trans
        (List.sublist_append_left _ _)
    exact noAscentOutside left right outsideValue hp hl.1 hr.2 (by omega) outsideBounds
  have afterSorted : after.Pairwise (· > ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := afterBounds left (hs.subset (by simp))
    have hr := afterBounds right (hs.subset (by simp))
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp ((interiorNodup.sublist afterSub).sublist hs)).1
    by_contra hnot
    have hp : [outsideValue, left, right].Sublist interior := by
      rw [split]
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        ((List.singleton_sublist.mpr outsideValueMem).append hs).trans
          (List.sublist_append_right before _)
    exact noOutsideAscent outsideValue left right hp outsideBounds hl.1 hr.2 (by omega)
  have noUpperLower (upper lower : ℕ) (hs : [upper, lower].Sublist interior)
      (hu : last < upper) (hl : lower < first) : False := by
    have hp := chain interior low upper lower interiorNodup
      (lowBefore upper (hs.subset (by simp)) (Or.inr hu)) hs
    let witness := fun rank : ℕ => if rank = 1 then lower else if rank = 2 then first
      else if rank = 3 then low else upper
    apply criterion.2.1 1 (by omega) (by omega)
    change Occurs [2, 3, 4, 1] word
    refine build _ _ witness (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
    · simpa [word, witness] using (hp.cons_cons first).trans
        (List.sublist_append_left (first :: interior) [last])
  have lowerUpperSplit (container : List ℕ) (hsub : container.Sublist interior)
      (hc : ∀ value ∈ container, value < first ∨ last < value) :
      container = container.filter isLower ++ container.filter isUpper := by
    induction container with
    | nil => simp
    | cons head tail ih =>
      have ht := ih ((List.sublist_cons_self head tail).trans hsub)
        (by intro value hv; exact hc value (by simp [hv]))
      rcases hc head (by simp) with hl | hu
      · simpa [List.filter_cons, isLower, isUpper, hl, show ¬ last < head by omega] using
          congrArg (List.cons head) ht
      · have allUpper : ∀ value ∈ tail, last < value := by
          intro value hv
          rcases hc value (by simp [hv]) with hl | hu'
          · exact False.elim (noUpperLower head value
              (((List.singleton_sublist.mpr hv).cons_cons head).trans hsub) hu hl)
          · exact hu'
        have lowEmpty : tail.filter isLower = [] := List.filter_eq_nil_iff.mpr
          (by intro value hv; simp [isLower]; have := allUpper value hv; omega)
        have highAll : tail.filter isUpper = tail := List.filter_eq_self.mpr
          (by intro value hv; simp [isUpper, allUpper value hv])
        simp [List.filter_cons, isLower, isUpper, hu, show ¬ head < first by omega,
          lowEmpty, highAll]
  let lower := interior.filter isLower
  let upper := interior.filter isUpper
  have outsideSplit : outside = lower ++ upper := by
    have hh := lowerUpperSplit outside List.filter_sublist
      (by intro value hv; exact of_decide_eq_true (List.mem_filter.mp hv).2)
    have hl : outside.filter isLower = lower := by
      simp only [outside, lower, List.filter_filter]
      congr 1
      funext value
      simp [isOutside, isLower]
      exact Or.inl
    have hu : outside.filter isUpper = upper := by
      simp only [outside, upper, List.filter_filter]
      congr 1
      funext value
      simp [isOutside, isUpper]
      exact Or.inr
    simpa only [hl, hu] using hh
  have lowerSorted : lower.Pairwise (· > ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : left ∈ _))).2
    have hr := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : right ∈ _))).2
    have hs := hs.trans (List.filter_sublist (p := isLower))
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp (interiorNodup.sublist hs)).1
    by_contra hnot
    have hp := chain interior left right high interiorNodup hs
      (highAfter right (hs.subset (by simp)) (Or.inl hr))
    let witness := fun rank : ℕ => if rank = 1 then left else if rank = 2 then right
      else if rank = 3 then high else last
    apply criterion.2.2.1
    change Occurs [1, 2, 3, 4] (interior ++ [last])
    refine build _ _ witness (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
    · simpa [witness] using hp.append (List.Sublist.refl [last])
  have upperSorted : upper.Pairwise (· > ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : left ∈ _))).2
    have hr := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : right ∈ _))).2
    have hs := hs.trans (List.filter_sublist (p := isUpper))
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp (interiorNodup.sublist hs)).1
    by_contra hnot
    have hp := chain interior low left right interiorNodup
      (lowBefore left (hs.subset (by simp)) (Or.inr hl)) hs
    let witness := fun rank : ℕ => if rank = 1 then first else if rank = 2 then low
      else if rank = 3 then left else right
    apply criterion.2.2.2
    rw [dropWord]
    refine build _ _ witness (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
    · simpa [witness] using hp.cons_cons first
  have filterPerm (predicate : ℕ → Bool) (start width : ℕ)
      (hb : ∀ value, 1 ≤ value → value ≤ size →
        (predicate value = true ↔ start ≤ value ∧ value < start + width))
      (hr : 1 ≤ start ∧ start + width ≤ size + 1)
      (he : predicate first = false ∧ predicate last = false) :
      (interior.filter predicate).Perm (List.range' start width) := by
    apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [List.mem_filter, List.mem_range'_1]
    constructor
    · rintro ⟨hv, hh⟩
      have hv := bounds value (by simp [word, hv])
      have := (hb value hv.1 hv.2).mp hh
      omega
    · intro hh
      have hv : value ∈ word := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr (by omega))
      have hpred := (hb value (by omega) (by omega)).mpr (by omega)
      have hn : value ≠ first := by intro hn; subst value; simp [he.1] at hpred
      have hn' : value ≠ last := by intro hn; subst value; simp [he.2] at hpred
      exact ⟨by simpa [word, hn, hn'] using hv, hpred⟩
  have lowerPerm : lower.Perm (List.range' 1 (first - 1)) := by
    apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [lower, List.mem_filter, isLower, decide_eq_true_eq, List.mem_range'_1]
    constructor
    · rintro ⟨hv, hh⟩
      have := bounds value (by simp [word, hv]); omega
    · intro hh
      have hv : value ∈ word := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr (by omega))
      exact ⟨by simpa [word, show value ≠ first by omega,
        show value ≠ last by omega] using hv, by omega⟩
  have upperPerm : upper.Perm (List.range' (last + 1) (size - last)) :=
    filterPerm isUpper (last + 1) (size - last)
      (by intro value hlo hhi; simp only [isUpper, decide_eq_true_eq]; omega)
      (by omega)
      (by simp [isUpper]; omega)
  have lowerEq : lower = (List.range' 1 (first - 1)).reverse := by
    apply (lowerPerm.trans (List.reverse_perm _).symm).eq_of_pairwise
      (fun _ _ hl hr => by omega) lowerSorted
    simpa only [List.pairwise_reverse] using
      (List.pairwise_lt_range' (s := 1) (n := first - 1))
  have upperEq : upper = (List.range' (last + 1) (size - last)).reverse := by
    apply (upperPerm.trans (List.reverse_perm _).symm).eq_of_pairwise
      (fun _ _ hl hr => by omega) upperSorted
    simpa only [List.pairwise_reverse] using
      (List.pairwise_lt_range' (s := last + 1) (n := size - last))
  have middleFilter : interior.filter (fun value => decide (first < value ∧ value < last)) =
      before ++ after := by
    have hp : before.filter (fun value => decide (first < value ∧ value < last)) = before :=
      List.filter_eq_self.mpr (by intro value hv; simp [beforeBounds value hv])
    have hs : after.filter (fun value => decide (first < value ∧ value < last)) = after :=
      List.filter_eq_self.mpr (by intro value hv; simp [afterBounds value hv])
    have ho : outside.filter (fun value => decide (first < value ∧ value < last)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv
        have hh := of_decide_eq_true (List.mem_filter.mp hv).2
        simp only [decide_eq_true_eq]
        rcases hh with hh | hh <;> omega)
    rw [split, List.filter_append, List.filter_append, hp, ho, hs]
    simp
  have middlePerm : (before ++ after).Perm
      (List.range' (first + 1) (last - first - 1)) := by
    rw [← middleFilter]
    exact filterPerm _ _ _ (by intro value hlo hhi; simp only [decide_eq_true_eq]; omega)
      (by omega) (by simp)
  have cannotReverse (left right : ℕ) (hl : [left, right].Sublist interior)
      (hr : [right, left].Sublist interior) : False := by
    have hh := interiorNodup.sublist (chain interior left right left interiorNodup hl hr)
    simpa using hh
  have lowPrefix : low ∈ before := by
    have hv : low ∈ before ++ after := middlePerm.mem_iff.mpr
      (List.mem_range'_1.mpr (by omega))
    rcases List.mem_append.mp hv with hv | hv
    · exact hv
    · have hp : [outsideValue, low].Sublist interior := by
        rw [split]
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          ((List.singleton_sublist.mpr outsideValueMem).append
            (List.singleton_sublist.mpr hv)).trans (List.sublist_append_right before _)
      exact False.elim (cannotReverse low outsideValue
        (lowBefore outsideValue outsideMem outsideBounds) hp)
  have highSuffix : high ∈ after := by
    have hv : high ∈ before ++ after := middlePerm.mem_iff.mpr
      (List.mem_range'_1.mpr (by omega))
    rcases List.mem_append.mp hv with hv | hv
    · have hp : [high, outsideValue].Sublist interior := by
        rw [split]
        exact ((List.singleton_sublist.mpr hv).append
          (List.singleton_sublist.mpr outsideValueMem)).trans (List.sublist_append_left _ _)
      exact False.elim (cannotReverse high outsideValue hp
        (highAfter outsideValue outsideMem outsideBounds))
    · exact hv
  refine ⟨by omega, before, after, ?_, middlePerm, beforeSorted, afterSorted,
    low, lowPrefix, high, highSuffix, ascent⟩
  simpa only [outsideSplit, lowerEq, upperEq, List.append_assoc] using split

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscendingOutside
