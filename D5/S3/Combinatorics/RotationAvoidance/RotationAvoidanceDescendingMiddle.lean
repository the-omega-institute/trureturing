/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingMiddle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingMiddle
   mirror-E: none(waiver:positive-middle-descending-normal-form)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A descending upper pair encloses the increasing middle and splits two upper runs. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDescendingMiddle

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

set_option maxHeartbeats 1200000 in
theorem descending_positive_middle_normal_form (size first last : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size) (hfirst : 1 ≤ first) (hmiddle : first + 1 < last)
    (hperm : (first :: interior ++ [last]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [1, 4, 3, 2] ((first :: interior ++ [last]).rotate cut) ↔ cut = 0) :
    last + 2 ≤ size ∧ ∃ upperBefore suffix : List ℕ,
      interior = upperBefore ++ List.range' (first + 1) (last - first - 1) ++
        suffix ++ List.range' 1 (first - 1) ∧
      (upperBefore ++ suffix).Perm (List.range' (last + 1) (size - last)) ∧
      upperBefore.Pairwise (· < ·) ∧ suffix.Pairwise (· < ·) ∧
      ∃ upper ∈ upperBefore, ∃ lower ∈ suffix, lower < upper := by
  classical
  let word := first :: interior ++ [last]
  let isMiddle := fun value : ℕ => decide (first < value ∧ value < last)
  let isLower := fun value : ℕ => decide (value < first)
  let isUpper := fun value : ℕ => decide (last < value)
  have criterion := (unique_bad_cut_iff size hsize [1, 4, 3, 2] word
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
  have noLowerUpper (lower upper : ℕ) (hs : [lower, upper].Sublist interior)
      (hl : lower < first) (hu : last < upper) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then lower else if rank = 2 then first
      else if rank = 3 then last else upper
    have hh := criterion.2.1 3 (by omega) (by omega)
    apply hh
    change Occurs [2, 1, 4, 3] word
    refine build _ word chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [word, chosen] using (hs.append (List.Sublist.refl [last])).cons_cons first
  have lowerIncreasing : (interior.filter isLower).Pairwise (· < ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : left ∈ _))).2
    have hr := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : right ∈ _))).2
    have hs := hs.trans (List.filter_sublist (p := isLower))
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp (interiorNodup.sublist hs)).1
    by_contra hnot
    let chosen := fun rank : ℕ => if rank = 1 then right else if rank = 2 then left
      else if rank = 3 then first else last
    apply criterion.2.1 2 (by omega) (by omega)
    change Occurs [3, 2, 1, 4] word
    refine build _ word chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> dsimp [isLower] at * <;> omega
    · simpa [word, chosen] using (hs.append (List.Sublist.refl [last])).cons_cons first
  have noMiddleDescent (middle upper lower : ℕ)
      (hs : [middle, upper, lower].Sublist interior)
      (hm : first < middle ∧ middle < last) (hu : last < lower) (hd : lower < upper) :
      False := by
    let chosen := fun rank : ℕ => if rank = 1 then middle else if rank = 2 then last
      else if rank = 3 then lower else upper
    apply criterion.2.2.1
    change Occurs [1, 4, 3, 2] (interior ++ [last])
    refine build _ (interior ++ [last]) chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using hs.append (List.Sublist.refl [last])
  have noDescentMiddle (upper lower middle : ℕ)
      (hs : [upper, lower, middle].Sublist interior)
      (hu : last < lower) (hd : lower < upper) (hm : first < middle ∧ middle < last) :
      False := by
    let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then middle
      else if rank = 3 then lower else upper
    apply criterion.2.2.2
    rw [dropWord]
    refine build _ (first :: interior) chosen (by decide) rfl ?_ ?_
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
  have chosenLast : chosen 2 = last := by
    by_contra hne
    have hs : [chosen 2, chosen 3, chosen 4, chosen 1].Sublist
        (last :: interior.reverse ++ [first]) := by
      simpa [word] using selected.reverse
    have hs := List.Sublist.of_cons_of_ne hne hs
    have ht : ([1, 4, 3, 2].map chosen).Sublist (first :: interior) := by
      simpa using hs.reverse
    exact criterion.2.2.2 (build _ word.dropLast chosen (by decide) rfl hi (dropWord.symm ▸ ht))
  let high := chosen 4
  let low := chosen 3
  have lowBound : last < low := by dsimp [low]; omega
  have descent : low < high := chosen34
  have pair : [high, low].Sublist interior := by
    have hs : [high, low, last].Sublist (interior ++ [last]) := by
      apply (List.cons_sublist_cons (a := first)).mp
      simpa [word, chosenFirst, chosenLast, high, low] using selected
    have hr : (last :: [low, high]).Sublist (last :: interior.reverse) := by
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
  have enclosed (middle : ℕ) (hm : middle ∈ interior)
      (hb : first < middle ∧ middle < last) : [high, middle, low].Sublist interior := by
    rcases insertThird interior high low middle pair hm (by omega) (by omega) with
      hh | hh | hh
    · exact False.elim (noMiddleDescent _ _ _ hh hb lowBound descent)
    · exact hh
    · exact False.elim (noDescentMiddle _ _ _ hh lowBound descent hb)
  have highBefore (middle : ℕ) (hm : middle ∈ interior)
      (hb : first < middle ∧ middle < last) : [high, middle].Sublist interior :=
    (List.sublist_append_left [high, middle] [low]).trans (enclosed middle hm hb)
  have lowAfter (middle : ℕ) (hm : middle ∈ interior)
      (hb : first < middle ∧ middle < last) : [middle, low].Sublist interior :=
    (List.sublist_cons_self high _).trans (enclosed middle hm hb)
  have noLowerMiddle (lower middle : ℕ) (hs : [lower, middle].Sublist interior)
      (hl : lower < first) (hm : first < middle ∧ middle < last) : False := by
    have hh := chain interior lower middle low interiorNodup hs
      (lowAfter middle (hs.subset (by simp)) hm)
    have hp : [lower, low].Sublist interior :=
      ((List.sublist_cons_self middle [low]).cons_cons lower).trans hh
    exact noLowerUpper lower low hp hl lowBound
  have middleSorted : (interior.filter isMiddle).Pairwise (· < ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : left ∈ _))).2
    have hr := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : right ∈ _))).2
    have hs := hs.trans (List.filter_sublist (p := isMiddle))
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp (interiorNodup.sublist hs)).1
    by_contra hnot
    have triple := chain interior high left right interiorNodup
      (highBefore left (hs.subset (by simp)) hl) hs
    let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then right
      else if rank = 3 then left else high
    apply criterion.2.2.2
    rw [dropWord]
    refine build _ (first :: interior) chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> dsimp [high, low] at * <;> omega
    · simpa [chosen] using triple.cons_cons first
  have noHole (left extra right : ℕ) (hs : [left, extra, right].Sublist interior)
      (hl : first < left ∧ left < last) (hr : first < right ∧ right < last)
      (he : ¬ (first < extra ∧ extra < last)) : False := by
    have hleftExtra : [left, extra].Sublist interior :=
      (List.sublist_append_left [left, extra] [right]).trans hs
    have hextraRight : [extra, right].Sublist interior :=
      (List.sublist_cons_self _ _).trans hs
    rcases colors extra (hs.subset (by simp)) with hlo | hm | hhi
    · exact noLowerMiddle extra right hextraRight hlo hr
    · exact he hm
    · by_cases hd : extra < high
      · have triple := chain interior high left extra interiorNodup
          (highBefore left (hs.subset (by simp)) hl) hleftExtra
        have hp : [high, extra].Sublist interior :=
          ((List.sublist_cons_self left [extra]).cons_cons high).trans triple
        exact noDescentMiddle high extra right
          (chain interior high extra right interiorNodup hp hextraRight) hhi hd hr
      · have triple := chain interior extra right low interiorNodup hextraRight
          (lowAfter right (hs.subset (by simp)) hr)
        have hp : [extra, low].Sublist interior :=
          ((List.sublist_cons_self right [low]).cons_cons extra).trans triple
        exact noMiddleDescent left extra low
          (chain interior left extra low interiorNodup hleftExtra hp) hl lowBound (by omega)
  have contiguous (container : List ℕ)
      (hno : ∀ left extra right, [left, extra, right].Sublist container →
        isMiddle left = true → isMiddle right = true → isMiddle extra = false → False)
      (hex : ∃ value ∈ container, isMiddle value = true) :
      ∃ upperBefore suffix, container = upperBefore ++ container.filter isMiddle ++ suffix ∧
        (∀ value ∈ upperBefore, isMiddle value = false) ∧
        (∀ value ∈ suffix, isMiddle value = false) := by
    induction container with
    | nil => simpa using hex
    | cons head tail ih =>
      by_cases htail : ∃ value ∈ tail, isMiddle value = true
      · obtain ⟨upperBefore, suffix, heq, hp, hs⟩ := ih
          (by intro left extra right hh hl hr he; exact hno _ _ _ (hh.cons head) hl hr he)
          htail
        by_cases hhead : isMiddle head = true
        · have hempty : upperBefore = [] := by
            cases upperBefore with
            | nil => rfl
            | cons extra rest =>
              obtain ⟨value, hv, hm⟩ := htail
              have hf : value ∈ tail.filter isMiddle := List.mem_filter.mpr ⟨hv, hm⟩
              have hselected : [head, extra, value].Sublist (head :: tail) := by
                rw [heq]
                apply List.Sublist.cons_cons
                apply List.Sublist.cons_cons
                exact (List.singleton_sublist.mpr hf).trans
                  ((List.sublist_append_right rest _).trans (List.sublist_append_left _ suffix))
              exact False.elim (hno head extra value hselected hhead hm (hp extra (by simp)))
          subst upperBefore
          refine ⟨[], suffix, ?_, by simp, hs⟩
          simpa [List.filter_cons, hhead] using congrArg (List.cons head) heq
        · have hf : isMiddle head = false := Bool.eq_false_iff.mpr hhead
          refine ⟨head :: upperBefore, suffix, ?_, ?_, hs⟩
          · simpa [List.filter_cons, hf] using congrArg (List.cons head) heq
          · intro value hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact hf
            · exact hp value hv
      · have ht : ∀ value ∈ tail, isMiddle value = false := by
          intro value hv
          apply Bool.eq_false_iff.mpr
          intro hm
          exact htail ⟨value, hv, hm⟩
        have hhead : isMiddle head = true := by
          obtain ⟨value, hv, hm⟩ := hex
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hm
          · exact False.elim (htail ⟨value, hv, hm⟩)
        have htfilter : tail.filter isMiddle = [] := List.filter_eq_nil_iff.mpr
          (by intro value hv; simp [ht value hv])
        exact ⟨[], tail, by simp [List.filter_cons, hhead, htfilter], by simp, ht⟩
  have middleMem : first + 1 ∈ interior := by
    have hh : first + 1 ∈ word := hperm.mem_iff.mpr
      (List.mem_range'_1.mpr (by omega))
    simpa [word, show first + 1 ≠ first by omega, show first + 1 ≠ last by omega] using hh
  let middle := interior.filter isMiddle
  have middleValue : first + 1 ∈ middle := by
    exact List.mem_filter.mpr ⟨middleMem, by simp [isMiddle]; omega⟩
  obtain ⟨upperBefore, afterMiddle, split, prefixOutside, suffixOutside⟩ := contiguous interior
    (by intro left extra right hs hl hr he
        exact noHole left extra right hs (of_decide_eq_true hl) (of_decide_eq_true hr)
          (of_decide_eq_false he))
    ⟨first + 1, middleMem, by simp [isMiddle]; omega⟩
  have prefixSub : upperBefore.Sublist interior := by
    rw [split]
    exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)
  have afterSub : afterMiddle.Sublist interior := by
    rw [split]
    exact List.sublist_append_right _ _
  have prefixUpper (value : ℕ) (hv : value ∈ upperBefore) : last < value := by
    rcases colors value (prefixSub.subset hv) with hl | hm | hu
    · have hp : [value, first + 1].Sublist interior := by
        rw [split]
        exact ((List.singleton_sublist.mpr hv).append
          (List.singleton_sublist.mpr middleValue)).trans (List.sublist_append_left _ _)
      exact False.elim (noLowerMiddle _ _ hp hl (by omega))
    · exact False.elim ((of_decide_eq_false (prefixOutside value hv)) hm)
    · exact hu
  have separated (container : List ℕ) (hsub : container.Sublist interior)
      (hout : ∀ value ∈ container, isMiddle value = false) :
      container = container.filter isUpper ++ container.filter isLower := by
    induction container with
    | nil => simp
    | cons head tail ih =>
      have ht := ih ((List.sublist_cons_self head _).trans hsub)
        (by intro value hv; exact hout value (by simp [hv]))
      rcases colors head (hsub.subset (by simp)) with hl | hm | hu
      · have allLower : ∀ value ∈ tail, value < first := by
          intro value hv
          rcases colors value (hsub.subset (by simp [hv])) with hlo | hmid | hhi
          · exact hlo
          · exact False.elim ((of_decide_eq_false (hout value (by simp [hv]))) hmid)
          · exact False.elim (noLowerUpper head value
              (((List.singleton_sublist.mpr hv).cons_cons head).trans hsub) hl hhi)
        have heqLower : tail.filter isLower = tail := List.filter_eq_self.mpr
          (by intro value hv; simp [isLower, allLower value hv])
        have heqUpper : tail.filter isUpper = [] := List.filter_eq_nil_iff.mpr
          (by intro value hv; simp [isUpper]; have := allLower value hv; omega)
        simp [isLower, isUpper, hl, show ¬ last < head by omega, heqLower, heqUpper]
      · exact False.elim ((of_decide_eq_false (hout head (by simp))) hm)
      · simpa [isLower, isUpper, hu, show ¬ head < first by omega] using
          congrArg (List.cons head) ht
  have afterEq := separated afterMiddle afterSub suffixOutside
  let suffix := afterMiddle.filter isUpper
  let lower := afterMiddle.filter isLower
  have refinedSplit : interior = upperBefore ++ middle ++ suffix ++ lower := by
    simpa [middle, suffix, lower, List.append_assoc] using split.trans
      (congrArg (fun tail => upperBefore ++ interior.filter isMiddle ++ tail) afterEq)
  have middlePerm : middle.Perm (List.range' (first + 1) (last - first - 1)) := by
    apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [middle, List.mem_filter, isMiddle, decide_eq_true_eq, List.mem_range'_1]
    constructor
    · rintro ⟨_, hh⟩; omega
    · intro hh
      have hv : value ∈ word := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hv : value ∈ interior := by
        simpa [word, show value ≠ first by omega, show value ≠ last by omega] using hv
      exact ⟨hv, by omega⟩
  have middleEq : middle = List.range' (first + 1) (last - first - 1) :=
    middlePerm.eq_of_pairwise (by intro left right hl hr; omega)
      middleSorted (List.pairwise_lt_range' _ (by omega))
  have lowerFilter : interior.filter isLower = lower := by
    have hp : upperBefore.filter isLower = [] := List.filter_eq_nil_iff.mpr
      (by intro value hv; simp [isLower]; have := prefixUpper value hv; omega)
    have hm : middle.filter isLower = [] := List.filter_eq_nil_iff.mpr (by
      intro value hv
      have hh := of_decide_eq_true (List.mem_filter.mp hv).2
      simp [isLower]; omega)
    have hs : suffix.filter isLower = [] := List.filter_eq_nil_iff.mpr (by
      intro value hv
      have hh := of_decide_eq_true (List.mem_filter.mp hv).2
      simp [isLower]; omega)
    have hl : lower.filter isLower = lower := by simp [lower]
    rw [refinedSplit, List.filter_append, List.filter_append, List.filter_append,
      hp, hm, hs, hl]
    simp
  have lowerPerm : lower.Perm (List.range' 1 (first - 1)) := by
    rw [← lowerFilter]
    apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [List.mem_filter, isLower, decide_eq_true_eq, List.mem_range'_1]
    constructor
    · rintro ⟨hv, hh⟩
      have hb := bounds value (by simp [word, hv]); omega
    · intro hh
      have hv : value ∈ word := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hv : value ∈ interior := by
        simpa [word, show value ≠ first by omega, show value ≠ last by omega] using hv
      exact ⟨hv, by omega⟩
  have lowerEq := lowerPerm.eq_of_pairwise (by intro left right hl hr; omega)
    (lowerFilter ▸ lowerIncreasing) (List.pairwise_lt_range' _ (by omega))
  have suffixSub : suffix.Sublist interior :=
    (List.filter_sublist (p := isUpper)).trans afterSub
  have suffixUpper (value : ℕ) (hv : value ∈ suffix) : last < value :=
    of_decide_eq_true (List.mem_filter.mp hv).2
  have prefixSorted : upperBefore.Pairwise (· < ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := prefixUpper left (hs.subset (by simp))
    have hr := prefixUpper right (hs.subset (by simp))
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp ((interiorNodup.sublist prefixSub).sublist hs)).1
    by_contra hnot
    have hp : [left, right, first + 1].Sublist interior := by
      rw [split]
      exact (hs.append (List.singleton_sublist.mpr middleValue)).trans
        (List.sublist_append_left _ _)
    exact noDescentMiddle _ _ _ hp hr (by omega) (by omega)
  have suffixSorted : suffix.Pairwise (· < ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := suffixUpper left (hs.subset (by simp))
    have hr := suffixUpper right (hs.subset (by simp))
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp ((interiorNodup.sublist suffixSub).sublist hs)).1
    by_contra hnot
    have hp : [first + 1, left, right].Sublist interior := by
      rw [refinedSplit]
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (((List.singleton_sublist.mpr middleValue).append hs).trans
          (List.sublist_append_right upperBefore _)).trans (List.sublist_append_left _ lower)
    exact noMiddleDescent _ _ _ hp (by omega) hr (by omega)
  have upperFilter : interior.filter isUpper = upperBefore ++ suffix := by
    have hp : upperBefore.filter isUpper = upperBefore := List.filter_eq_self.mpr
      (by intro value hv; simp [isUpper, prefixUpper value hv])
    have hm : middle.filter isUpper = [] := List.filter_eq_nil_iff.mpr (by
      intro value hv
      have hh := of_decide_eq_true (List.mem_filter.mp hv).2
      simp [isUpper]; omega)
    have hs : suffix.filter isUpper = suffix := by simp [suffix]
    have hl : lower.filter isUpper = [] := List.filter_eq_nil_iff.mpr (by
      intro value hv
      have hh := of_decide_eq_true (List.mem_filter.mp hv).2
      simp [isUpper]; omega)
    rw [refinedSplit, List.filter_append, List.filter_append, List.filter_append,
      hp, hm, hs, hl]
    simp
  have upperPerm : (upperBefore ++ suffix).Perm (List.range' (last + 1) (size - last)) := by
    rw [← upperFilter]
    apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [List.mem_filter, isUpper, decide_eq_true_eq, List.mem_range'_1]
    constructor
    · rintro ⟨hv, hh⟩
      have hb := bounds value (by simp [word, hv]); omega
    · intro hh
      have hv : value ∈ word := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hv : value ∈ interior := by
        simpa [word, show value ≠ first by omega, show value ≠ last by omega] using hv
      exact ⟨hv, by omega⟩
  have middleBeforeSuffix (value : ℕ) (hv : value ∈ suffix) :
      [first + 1, value].Sublist interior := by
    rw [refinedSplit]
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      (((List.singleton_sublist.mpr middleValue).append
        (List.singleton_sublist.mpr hv)).trans (List.sublist_append_right upperBefore _)).trans
          (List.sublist_append_left _ lower)
  have prefixBeforeMiddle (value : ℕ) (hv : value ∈ upperBefore) :
      [value, first + 1].Sublist interior := by
    rw [split]
    exact ((List.singleton_sublist.mpr hv).append
      (List.singleton_sublist.mpr middleValue)).trans (List.sublist_append_left _ _)
  have cannotReverse (left right : ℕ) (hl : [left, right].Sublist interior)
      (hr : [right, left].Sublist interior) : False := by
    have hh := interiorNodup.sublist (chain interior left right left interiorNodup hl hr)
    simpa using hh
  have highPrefix : high ∈ upperBefore := by
    have hh : high ∈ upperBefore ++ suffix := by
      rw [← upperFilter]
      exact List.mem_filter.mpr ⟨pair.subset (by simp), by simp [isUpper]; omega⟩
    rcases List.mem_append.mp hh with hh | hh
    · exact hh
    · exact False.elim (cannotReverse high (first + 1)
        (highBefore (first + 1) middleMem (by omega)) (middleBeforeSuffix high hh))
  have lowSuffix : low ∈ suffix := by
    have hh : low ∈ upperBefore ++ suffix := by
      rw [← upperFilter]
      exact List.mem_filter.mpr ⟨pair.subset (by simp), by simp [isUpper, lowBound]⟩
    rcases List.mem_append.mp hh with hh | hh
    · exact False.elim (cannotReverse low (first + 1) (prefixBeforeMiddle low hh)
        (lowAfter (first + 1) middleMem (by omega)))
    · exact hh
  refine ⟨?_, upperBefore, suffix, ?_, upperPerm, prefixSorted, suffixSorted,
    high, highPrefix, low, lowSuffix, descent⟩
  · have hb := bounds high (selected.subset (by simp [high]))
    omega
  · simpa only [middleEq, lowerEq] using refinedSplit

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDescendingMiddle
