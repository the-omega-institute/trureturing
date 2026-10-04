/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayered
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLayered
   mirror-E: none(waiver:layered-endpoint-normal-form)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The 1423 obstruction profiles force upper and lower blocks between middle runs. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayered

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

set_option maxHeartbeats 1600000 in
theorem layered_endpoint_normal_form (size first last : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size) (hfirst : 1 ≤ first) (horder : first < last)
    (hperm : (first :: interior ++ [last]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [1, 4, 2, 3] ((first :: interior ++ [last]).rotate cut) ↔ cut = 0) :
    first + 1 < last ∧ last < size ∧
      ∃ before upper lower suffix : List ℕ,
        interior = before ++ upper ++ lower ++ suffix ∧
        upper.Perm (List.range' (last + 1) (size - last)) ∧
        lower.Perm (List.range' 1 (first - 1)) ∧
        (before ++ suffix).Perm (List.range' (first + 1) (last - first - 1)) ∧
        before.Pairwise (· > ·) ∧ suffix.Pairwise (· > ·) ∧
        (∀ left ∈ before, ∀ right ∈ suffix, right < left) ∧ suffix ≠ [] ∧
        (2 ≤ first → before = []) ∧
        ¬ Occurs [3, 1, 2] upper ∧ ¬ Occurs [2, 3, 1, 4] upper ∧
        ¬ Occurs [2, 3, 1] lower ∧ ¬ Occurs [1, 4, 2, 3] lower := by
  classical
  let word := first :: interior ++ [last]
  have criterion := (unique_bad_cut_iff size hsize [1, 4, 2, 3] word
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
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hv); omega
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
  have noMiddleLower (middle low : ℕ) (hs : [middle, low].Sublist interior)
      (hm : first < middle ∧ middle < last) (hl : low < first) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then low else if rank = 2 then first
      else if rank = 3 then middle else last
    apply criterion.2.1 2 (by omega) (by omega)
    change Occurs [2, 3, 1, 4] word
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [word, chosen] using (hs.cons_cons first).append (List.Sublist.refl [last])
  have noLowerUpperMiddle (low high middle : ℕ)
      (hs : [low, high, middle].Sublist interior) (hl : low < first)
      (hu : last < high) (hm : first < middle ∧ middle < last) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then low else if rank = 2 then middle
      else if rank = 3 then last else high
    apply criterion.2.2.1
    change Occurs [1, 4, 2, 3] (interior ++ [last])
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using hs.append (List.Sublist.refl [last])
  have noBetweenUpper (left middle right : ℕ)
      (hs : [left, middle, right].Sublist interior)
      (hl : last < left) (hm : first < middle ∧ middle < last) (hr : last < right) :
      False := by
    have hne : left ≠ right := by
      have hn := interiorNodup.sublist hs
      intro he
      exact (List.nodup_cons.mp hn).1 (by simp [he])
    by_cases hlt : left < right
    · let chosen := fun rank : ℕ => if rank = 1 then middle else if rank = 2 then last
        else if rank = 3 then left else right
      apply criterion.2.1 3 (by omega) (by omega)
      change Occurs [3, 1, 4, 2] word
      refine build _ _ chosen (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · simpa [word, chosen] using (hs.append (List.Sublist.refl [last])).cons first
    · let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then middle
        else if rank = 3 then right else left
      apply criterion.2.2.2
      rw [dropWord]
      refine build _ _ chosen (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · simpa [chosen] using hs.cons_cons first
  have noUpperMiddleAscent (high left right : ℕ)
      (hs : [high, left, right].Sublist interior)
      (hu : last < high) (hl : first < left) (ha : left < right) (hr : right < last) :
      False := by
    let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then left
      else if rank = 3 then right else high
    apply criterion.2.2.2
    rw [dropWord]
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using hs.cons_cons first
  have noMiddleUpperAscent (left high right : ℕ)
      (hs : [left, high, right].Sublist interior)
      (hl : first < left) (ha : left < right) (hr : right < last) (hu : last < high) :
      False := by
    let chosen := fun rank : ℕ => if rank = 1 then left else if rank = 2 then right
      else if rank = 3 then last else high
    apply criterion.2.2.1
    change Occurs [1, 4, 2, 3] (interior ++ [last])
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using hs.append (List.Sublist.refl [last])
  have noMiddle231 (left right low : ℕ)
      (hs : [left, right, low].Sublist interior)
      (hl : first < low) (ha : low < left) (hr : left < right) (hb : right < last) :
      False := by
    apply criterion.2.1 2 (by omega) (by omega)
    change Occurs [2, 3, 1, 4] word
    let chosen' := fun rank : ℕ => if rank = 1 then low else if rank = 2 then left
      else if rank = 3 then right else last
    refine build _ _ chosen' (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen'] <;> omega
    · simpa [word, chosen'] using (hs.append (List.Sublist.refl [last])).cons first
  obtain ⟨chosen, hi, _, selected, _⟩ := criterion.1
  have chosen12 : chosen 1 < chosen 2 := by simpa using hi 1 (by omega) (by decide)
  have chosen23 : chosen 2 < chosen 3 := by simpa using hi 2 (by omega) (by decide)
  have chosen34 : chosen 3 < chosen 4 := by simpa using hi 3 (by omega) (by decide)
  have chosenFirst : chosen 1 = first := by
    by_contra hne
    exact criterion.2.2.1
      (build _ word.tail chosen (by decide) rfl hi (List.Sublist.of_cons_of_ne hne selected))
  have chosenLast : chosen 3 = last := by
    by_contra hne
    have hs : [chosen 3, chosen 2, chosen 4, chosen 1].Sublist
        (last :: interior.reverse ++ [first]) := by
      simpa [word] using selected.reverse
    have hs := List.Sublist.of_cons_of_ne hne hs
    have ht : ([1, 4, 2, 3].map chosen).Sublist (first :: interior) := by
      simpa using hs.reverse
    exact criterion.2.2.2
      (build _ word.dropLast chosen (by decide) rfl hi (dropWord.symm ▸ ht))
  let high := chosen 4
  let middle := chosen 2
  have highBound : last < high := by dsimp [high]; omega
  have middleBound : first < middle ∧ middle < last := by dsimp [middle]; omega
  have selectedPair : [high, middle].Sublist interior := by
    have hs : [chosen 4, chosen 2, last].Sublist (interior ++ [last]) := by
      apply (List.cons_sublist_cons (a := first)).mp
      simpa [word, chosenFirst, chosenLast] using selected
    have hr : (last :: [chosen 2, chosen 4]).Sublist (last :: interior.reverse) := by
      simpa using hs.reverse
    simpa [high, middle] using (List.cons_sublist_cons.mp hr).reverse
  have highMem : high ∈ interior := selectedPair.subset (by simp)
  have highSize := bounds high (by simp [word, highMem])
  have chain (container : List ℕ) (left pivot right : ℕ) (hn : container.Nodup)
      (ha : [left, pivot].Sublist container) (hb : [pivot, right].Sublist container) :
      [left, pivot, right].Sublist container := by
    induction container with
    | nil => simp at ha
    | cons head tail ih =>
      have ht := (List.nodup_cons.mp hn).2
      by_cases hh : head = left
      · subst head
        have hne : pivot ≠ left := by
          exact Ne.symm (by simpa using (List.nodup_cons.mp (hn.sublist ha)).1)
        exact (List.Sublist.of_cons_of_ne hne hb).cons_cons left
      · have ha := List.Sublist.of_cons_of_ne (Ne.symm hh) ha
        have hne : pivot ≠ head := by
          intro heq
          exact (List.nodup_cons.mp hn).1 (heq ▸ ha.subset (by simp))
        exact (ih ht ha (List.Sublist.of_cons_of_ne hne hb)).cons head
  have pairOrder (container : List ℕ) (left right : ℕ)
      (ha : left ∈ container) (hb : right ∈ container) (hne : left ≠ right) :
      [left, right].Sublist container ∨ [right, left].Sublist container := by
    induction container with
    | nil => simp at ha
    | cons head tail ih =>
      by_cases hh : head = left
      · subst head
        exact Or.inl ((List.singleton_sublist.mpr
          ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))).cons_cons left)
      · by_cases hh' : head = right
        · subst head
          exact Or.inr ((List.singleton_sublist.mpr
            ((List.mem_cons.mp ha).resolve_left hne)).cons_cons right)
        · rcases ih ((List.mem_cons.mp ha).resolve_left (Ne.symm hh))
            ((List.mem_cons.mp hb).resolve_left (Ne.symm hh')) with hh | hh
          · exact Or.inl (hh.cons head)
          · exact Or.inr (hh.cons head)
  have upperBeforeTarget (value : ℕ) (hv : value ∈ interior) (hu : last < value) :
      [value, middle].Sublist interior := by
    rcases pairOrder interior value middle hv (selectedPair.subset (by simp))
      (by omega) with hh | hh
    · exact hh
    · exact False.elim (noBetweenUpper high middle value
        (chain interior high middle value interiorNodup selectedPair hh)
        highBound middleBound hu)
  have noLowerUpper (low value : ℕ) (hs : [low, value].Sublist interior)
      (hl : low < first) (hu : last < value) : False := by
    exact noLowerUpperMiddle low value middle
      (chain interior low value middle interiorNodup hs
        (upperBeforeTarget value (hs.subset (by simp)) hu)) hl hu middleBound
  let isUpper := fun value : ℕ => decide (last < value)
  have contiguous (container : List ℕ)
      (hno : ∀ left extra right, [left, extra, right].Sublist container →
        isUpper left = true → isUpper right = true → isUpper extra = false → False)
      (hex : ∃ value ∈ container, isUpper value = true) :
      ∃ before suffix, container = before ++ container.filter isUpper ++ suffix ∧
        (∀ value ∈ before, isUpper value = false) ∧
        (∀ value ∈ suffix, isUpper value = false) := by
    induction container with
    | nil => simpa using hex
    | cons head tail ih =>
      by_cases htail : ∃ value ∈ tail, isUpper value = true
      · obtain ⟨before, suffix, heq, hp, hs⟩ := ih
          (by intro left extra right hh hl hr he; exact hno _ _ _ (hh.cons head) hl hr he)
          htail
        by_cases hhead : isUpper head = true
        · have hempty : before = [] := by
            cases before with
            | nil => rfl
            | cons extra rest =>
              obtain ⟨value, hv, hm⟩ := htail
              have hf : value ∈ tail.filter isUpper := List.mem_filter.mpr ⟨hv, hm⟩
              have hselected : [head, extra, value].Sublist (head :: tail) := by
                rw [heq]
                apply List.Sublist.cons_cons
                apply List.Sublist.cons_cons
                exact (List.singleton_sublist.mpr hf).trans
                  ((List.sublist_append_right rest _).trans (List.sublist_append_left _ suffix))
              exact False.elim (hno head extra value hselected hhead hm (hp extra (by simp)))
          subst before
          refine ⟨[], suffix, ?_, by simp, hs⟩
          simpa [List.filter_cons, hhead] using congrArg (List.cons head) heq
        · have hf : isUpper head = false := Bool.eq_false_iff.mpr hhead
          refine ⟨head :: before, suffix, ?_, ?_, hs⟩
          · simpa [List.filter_cons, hf] using congrArg (List.cons head) heq
          · intro value hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact hf
            · exact hp value hv
      · have ht : ∀ value ∈ tail, isUpper value = false := by
          intro value hv
          apply Bool.eq_false_iff.mpr
          intro hm
          exact htail ⟨value, hv, hm⟩
        have hhead : isUpper head = true := by
          obtain ⟨value, hv, hm⟩ := hex
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hm
          · exact False.elim (htail ⟨value, hv, hm⟩)
        have htfilter : tail.filter isUpper = [] := List.filter_eq_nil_iff.mpr
          (by intro value hv; simp [ht value hv])
        exact ⟨[], tail, by simp [hhead, htfilter], by simp, ht⟩
  let upper := interior.filter isUpper
  have upperValue : high ∈ upper :=
    List.mem_filter.mpr ⟨highMem, by simp [isUpper, highBound]⟩
  obtain ⟨before, after, split, prefixOutside, afterOutside⟩ := contiguous interior
    (by
      intro left extra right hs hl hr he
      have hlu : last < left := of_decide_eq_true hl
      have hru : last < right := of_decide_eq_true hr
      have hem : extra ∈ interior := hs.subset (by simp)
      rcases colors extra hem with heLow | heMid | heHigh
      · exact noLowerUpper extra right
          ((List.sublist_cons_self left [extra, right]).trans hs) heLow hru
      · exact noBetweenUpper left extra right hs hlu heMid hru
      · simp [isUpper, heHigh] at he)
    ⟨high, highMem, by simp [isUpper, highBound]⟩
  have split : interior = before ++ (upper ++ after) := by
    simpa only [upper, List.append_assoc] using split
  have prefixSub : before.Sublist interior := by
    rw [split]
    exact List.sublist_append_left _ _
  have upperSub : upper.Sublist interior := List.filter_sublist
  have afterSub : after.Sublist interior := by
    rw [split]
    exact (List.sublist_append_right upper after).trans (List.sublist_append_right before _)
  have upperBound (value : ℕ) (hv : value ∈ upper) : last < value :=
    of_decide_eq_true (List.mem_filter.mp hv).2
  have prefixMiddle (value : ℕ) (hv : value ∈ before) : first < value ∧ value < last := by
    rcases colors value (prefixSub.subset hv) with hl | hm | hu
    · exact False.elim (noLowerUpper value high
        (by
          rw [split]
          exact ((List.singleton_sublist.mpr hv).append
            ((List.singleton_sublist.mpr upperValue).trans
              (List.sublist_append_left upper after)))) hl highBound)
    · exact hm
    · exact False.elim ((of_decide_eq_false (prefixOutside value hv)) hu)
  have targetAfter : middle ∈ after := by
    have hm : middle ∈ interior := selectedPair.subset (by simp)
    rw [split, List.mem_append, List.mem_append] at hm
    rcases hm with hm | hm | hm
    · have reversedPair : [middle, high].Sublist interior := by
        rw [split]
        exact (List.singleton_sublist.mpr hm).append
          ((List.singleton_sublist.mpr upperValue).trans (List.sublist_append_left upper after))
      have hn := interiorNodup.sublist
        (chain interior high middle high interiorNodup selectedPair reversedPair)
      exact False.elim ((List.nodup_cons.mp hn).1 (by simp))
    · have hh := upperBound middle hm
      omega
    · exact hm
  let isLower := fun value : ℕ => decide (value < first)
  let isMiddle := fun value : ℕ => decide (first < value ∧ value < last)
  have separated (container : List ℕ) (hsub : container.Sublist interior)
      (hout : ∀ value ∈ container, isUpper value = false) :
      container = container.filter isLower ++ container.filter isMiddle := by
    induction container with
    | nil => simp
    | cons head tail ih =>
      have ht := ih ((List.sublist_cons_self head _).trans hsub)
        (by intro value hv; exact hout value (by simp [hv]))
      rcases colors head (hsub.subset (by simp)) with hl | hm | hu
      · simpa [isLower, isMiddle, hl, show ¬ first < head by omega] using
          congrArg (List.cons head) ht
      · have allMiddle : ∀ value ∈ tail, first < value ∧ value < last := by
          intro value hv
          rcases colors value (hsub.subset (by simp [hv])) with hlo | hmid | hhi
          · exact False.elim (noMiddleLower head value
              (((List.singleton_sublist.mpr hv).cons_cons head).trans hsub) hm hlo)
          · exact hmid
          · exact False.elim ((of_decide_eq_false (hout value (by simp [hv]))) hhi)
        have heqMiddle : tail.filter isMiddle = tail := List.filter_eq_self.mpr
          (by intro value hv; simp [isMiddle, allMiddle value hv])
        have heqLower : tail.filter isLower = [] := List.filter_eq_nil_iff.mpr
          (by intro value hv; simp [isLower]; have := allMiddle value hv; omega)
        have hheadLower : isLower head = false := by simp [isLower]; omega
        have hheadMiddle : isMiddle head = true := by simp [isMiddle, hm]
        simp only [List.filter_cons, hheadLower, hheadMiddle, Bool.false_eq_true,
          Bool.true_eq, ↓reduceIte, heqMiddle, heqLower, List.nil_append]
      · exact False.elim ((of_decide_eq_false (hout head (by simp))) hu)
  let lower := after.filter isLower
  let suffix := after.filter isMiddle
  have afterEq : after = lower ++ suffix := separated after afterSub afterOutside
  have refinedSplit : interior = before ++ (upper ++ (lower ++ suffix)) := by
    exact split.trans (congrArg (fun tail => before ++ (upper ++ tail)) afterEq)
  have lowerSub : lower.Sublist interior := List.filter_sublist.trans afterSub
  have suffixSub : suffix.Sublist interior := List.filter_sublist.trans afterSub
  have lowerBound (value : ℕ) (hv : value ∈ lower) : value < first :=
    of_decide_eq_true (List.mem_filter.mp hv).2
  have suffixMiddle (value : ℕ) (hv : value ∈ suffix) : first < value ∧ value < last :=
    of_decide_eq_true (List.mem_filter.mp hv).2
  have suffixValue : middle ∈ suffix :=
    List.mem_filter.mpr ⟨targetAfter, by simp [isMiddle, middleBound]⟩
  have suffixNotNil : suffix ≠ [] := List.ne_nil_of_mem suffixValue
  have suffixSorted : suffix.Pairwise (· > ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := suffixMiddle left (hs.subset (by simp))
    have hr := suffixMiddle right (hs.subset (by simp))
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp ((interiorNodup.sublist suffixSub).sublist hs)).1
    by_contra hnot
    have hp : [high, left, right].Sublist interior := by
      rw [refinedSplit]
      exact ((List.singleton_sublist.mpr upperValue).append
        (hs.trans (List.sublist_append_right lower suffix))).trans
          (List.sublist_append_right before _)
    exact noUpperMiddleAscent high left right hp highBound hl.1 (by omega) hr.2
  have prefixAboveSuffix : ∀ left ∈ before, ∀ right ∈ suffix, right < left := by
    intro left hl right hr
    have hlm := prefixMiddle left hl
    have hrm := suffixMiddle right hr
    have hp : [left, high, right].Sublist interior := by
      rw [refinedSplit]
      exact (List.singleton_sublist.mpr hl).append
        ((List.singleton_sublist.mpr upperValue).append
          ((List.singleton_sublist.mpr hr).trans (List.sublist_append_right lower suffix)))
    have hne : left ≠ right := by
      intro he
      exact (List.nodup_cons.mp (interiorNodup.sublist hp)).1 (by simp [he])
    by_contra hnot
    exact noMiddleUpperAscent left high right hp hlm.1 (by omega) hrm.2 highBound
  have prefixSorted : before.Pairwise (· > ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := prefixMiddle left (hs.subset (by simp))
    have hr := prefixMiddle right (hs.subset (by simp))
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp ((interiorNodup.sublist prefixSub).sublist hs)).1
    by_contra hnot
    have hp : [left, right, middle].Sublist interior := by
      rw [refinedSplit]
      exact hs.append ((List.singleton_sublist.mpr suffixValue).trans
        ((List.sublist_append_right lower suffix).trans (List.sublist_append_right upper _)))
    exact noMiddle231 left right middle hp middleBound.1
      (prefixAboveSuffix left (hs.subset (by simp)) middle suffixValue) (by omega) hr.2
  have lowerFilter : interior.filter isLower = lower := by
    have hp : before.filter isLower = [] := List.filter_eq_nil_iff.mpr
      (by intro value hv; simp [isLower]; have := prefixMiddle value hv; omega)
    have hu : upper.filter isLower = [] := List.filter_eq_nil_iff.mpr
      (by intro value hv; simp [isLower]; have := upperBound value hv; omega)
    have hl : lower.filter isLower = lower := by simp [lower]
    have hs : suffix.filter isLower = [] := List.filter_eq_nil_iff.mpr
      (by intro value hv; simp [isLower]; have := suffixMiddle value hv; omega)
    rw [refinedSplit, List.filter_append, List.filter_append, List.filter_append, hp, hu, hl, hs]
    simp
  have middleFilter : interior.filter isMiddle = before ++ suffix := by
    have hp : before.filter isMiddle = before := List.filter_eq_self.mpr
      (by intro value hv; simp [isMiddle, prefixMiddle value hv])
    have hu : upper.filter isMiddle = [] := List.filter_eq_nil_iff.mpr
      (by intro value hv; simp [isMiddle]; have := upperBound value hv; omega)
    have hl : lower.filter isMiddle = [] := List.filter_eq_nil_iff.mpr
      (by intro value hv; simp [isMiddle]; have := lowerBound value hv; omega)
    have hs : suffix.filter isMiddle = suffix := by simp [suffix]
    rw [refinedSplit, List.filter_append, List.filter_append, List.filter_append, hp, hu, hl, hs]
    simp
  have filterPerm (predicate : ℕ → Bool) (start width : ℕ)
      (hb : ∀ value, 1 ≤ value → value ≤ size →
        (predicate value = true ↔ start ≤ value ∧ value < start + width))
      (hr : 1 ≤ start ∧ start + width ≤ size + 1)
      (he : predicate first = false ∧ predicate last = false) :
      (interior.filter predicate).Perm (List.range' start width) := by
    apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    rw [List.mem_filter, List.mem_range'_1]
    constructor
    · rintro ⟨hv, hh⟩
      have hvb := bounds value (by simp [word, hv])
      exact (hb value hvb.1 hvb.2).mp hh
    · intro hv
      have hvb : 1 ≤ value ∧ value ≤ size := by omega
      have hh := (hb value hvb.1 hvb.2).mpr hv
      have hn : value ≠ first := by intro heq; subst value; simp [he.1] at hh
      have hn' : value ≠ last := by intro heq; subst value; simp [he.2] at hh
      have hw : value ∈ word := hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      exact ⟨by simpa [word, hn, hn'] using hw, hh⟩
  have upperPerm : upper.Perm (List.range' (last + 1) (size - last)) := by
    apply filterPerm isUpper (last + 1) (size - last)
    · intro value hvlo hvhi
      simp only [isUpper, decide_eq_true_eq]
      omega
    · omega
    · simp [isUpper]; omega
  have lowerPerm : lower.Perm (List.range' 1 (first - 1)) := by
    rw [← lowerFilter]
    apply filterPerm isLower 1 (first - 1)
    · intro value hvlo hvhi
      simp only [isLower, decide_eq_true_eq]
      omega
    · have := bounds first (by simp [word]); omega
    · simp [isLower]; omega
  have middlePerm : (before ++ suffix).Perm
      (List.range' (first + 1) (last - first - 1)) := by
    rw [← middleFilter]
    apply filterPerm isMiddle (first + 1) (last - first - 1)
    · intro value hvlo hvhi
      simp only [isMiddle, decide_eq_true_eq]
      omega
    · omega
    · simp [isMiddle]
  have lowerForcesEmpty : 2 ≤ first → before = [] := by
    intro hnonempty
    have lowMem : 1 ∈ lower := lowerPerm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
    by_contra hnot
    obtain ⟨value, hv⟩ := List.exists_mem_of_ne_nil before hnot
    have hp : [value, 1].Sublist interior := by
      rw [refinedSplit]
      exact (List.singleton_sublist.mpr hv).append
        ((List.singleton_sublist.mpr lowMem).trans
          ((List.sublist_append_left lower suffix).trans (List.sublist_append_right upper _)))
    exact noMiddleLower value 1 hp (prefixMiddle value hv) (by omega)
  have noUpper312 : ¬ Occurs [3, 1, 2] upper := by
    rintro ⟨witness, hw, _, hs, _⟩
    have h12 : witness 1 < witness 2 := by simpa using hw 1 (by omega) (by decide)
    have h23 : witness 2 < witness 3 := by simpa using hw 2 (by omega) (by decide)
    have hb := upperBound (witness 1) (hs.subset (by simp))
    let chosen := fun rank : ℕ => if rank = 1 then first else witness (rank - 1)
    apply criterion.2.2.2
    rw [dropWord]
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using (hs.trans upperSub).cons_cons first
  have noUpper2314 : ¬ Occurs [2, 3, 1, 4] upper := by
    rintro ⟨witness, hw, _, hs, _⟩
    apply criterion.2.1 2 (by omega) (by omega)
    change Occurs [2, 3, 1, 4] word
    refine build _ _ witness (by decide) rfl hw ?_
    exact (hs.trans upperSub).trans
      ((List.sublist_append_left interior [last]).trans (List.sublist_cons_self first _))
  have noLower231 : ¬ Occurs [2, 3, 1] lower := by
    rintro ⟨witness, hw, _, hs, _⟩
    have h12 : witness 1 < witness 2 := by simpa using hw 1 (by omega) (by decide)
    have h23 : witness 2 < witness 3 := by simpa using hw 2 (by omega) (by decide)
    have hb := lowerBound (witness 3) (hs.subset (by simp))
    let chosen := fun rank : ℕ => if rank = 4 then last else witness rank
    apply criterion.2.1 2 (by omega) (by omega)
    change Occurs [2, 3, 1, 4] word
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [word, chosen] using ((hs.trans lowerSub).append
        (List.Sublist.refl [last])).cons first
  have noLower1423 : ¬ Occurs [1, 4, 2, 3] lower := by
    rintro ⟨witness, hw, _, hs, _⟩
    apply criterion.2.2.1
    change Occurs [1, 4, 2, 3] (interior ++ [last])
    refine build _ _ witness (by decide) rfl hw ?_
    exact (hs.trans lowerSub).trans (List.sublist_append_left interior [last])
  refine ⟨by omega, by omega, before, upper, lower, suffix, ?_, upperPerm,
    lowerPerm, middlePerm, prefixSorted, suffixSorted, prefixAboveSuffix, suffixNotNil,
    lowerForcesEmpty, noUpper312, noUpper2314, noLower231, noLower1423⟩
  simpa only [List.append_assoc] using refinedSplit

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLayered
