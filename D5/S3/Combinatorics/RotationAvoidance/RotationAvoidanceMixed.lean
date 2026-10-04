/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixed
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixed
   mirror-E: none(waiver:nonempty-lower-mixed-endpoint-normal-form)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A lower value forces the 1243 middle to be a singleton before a sorted shuffle. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscending
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixed

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

set_option maxHeartbeats 1200000 in
theorem mixed_nonempty_lower_normal_form (size first last : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size) (hfirst : 2 ≤ first) (horder : first < last)
    (hperm : (first :: interior ++ [last]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [1, 2, 4, 3] ((first :: interior ++ [last]).rotate cut) ↔ cut = 0) :
    last = first + 2 ∧ last < size ∧ ∃ suffix : List ℕ,
      interior = (first + 1) :: suffix ∧
      suffix.Perm (List.range' 1 (first - 1) ++ List.range' (last + 1) (size - last)) ∧
      (suffix.filter (fun value => decide (value < first))).Pairwise (· > ·) ∧
      (suffix.filter (fun value => decide (last < value))).Pairwise (· < ·) := by
  classical
  let word := first :: interior ++ [last]
  have criterion := (unique_bad_cut_iff size hsize [1, 2, 4, 3] word
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
  have noAscendingUpper (left right upper : ℕ)
      (hs : [left, right, upper].Sublist interior)
      (ha : left < right) (hl : right < last) (hu : last < upper) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then left else if rank = 2 then right
      else if rank = 3 then last else upper
    apply criterion.2.2.1
    change Occurs [1, 2, 4, 3] (interior ++ [last])
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using hs.append (List.Sublist.refl [last])
  have noMiddleUpperAscent (left upper right : ℕ)
      (hs : [left, upper, right].Sublist interior)
      (hl : first < left) (ha : left < right) (hr : right < last) (hu : last < upper) :
      False := by
    let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then left
      else if rank = 3 then right else upper
    apply criterion.2.2.2
    rw [dropWord]
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using hs.cons_cons first
  have noMiddleDescentLower (high low lower : ℕ)
      (hs : [high, low, lower].Sublist interior)
      (hl : first < low) (hd : low < high) (he : lower < first) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then lower else if rank = 2 then first
      else if rank = 3 then low else high
    apply criterion.2.1 1 (by omega) (by omega)
    change Occurs [2, 4, 3, 1] word
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [word, chosen] using (hs.cons_cons first).trans
        (List.sublist_append_left (first :: interior) [last])
  have noMiddleLowerDescent (high lower low : ℕ)
      (hs : [high, lower, low].Sublist interior)
      (hd : low < high) (hl : first < low) (hh : high < last) (he : lower < first) :
      False := by
    let chosen := fun rank : ℕ => if rank = 1 then lower else if rank = 2 then low
      else if rank = 3 then high else last
    apply criterion.2.1 3 (by omega) (by omega)
    change Occurs [3, 1, 2, 4] word
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [word, chosen] using (hs.append (List.Sublist.refl [last])).cons first
  have noUpperMiddleLower (upper middle lower : ℕ)
      (hs : [upper, middle, lower].Sublist interior)
      (hu : last < upper) (hm : first < middle ∧ middle < last) (hl : lower < first) :
      False := by
    let chosen := fun rank : ℕ => if rank = 1 then lower else if rank = 2 then first
      else if rank = 3 then middle else upper
    apply criterion.2.1 1 (by omega) (by omega)
    change Occurs [2, 4, 3, 1] word
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [word, chosen] using (hs.cons_cons first).trans
        (List.sublist_append_left (first :: interior) [last])
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
    have hs : [chosen 3, chosen 4, chosen 2, chosen 1].Sublist
        (last :: interior.reverse ++ [first]) := by
      simpa [word] using selected.reverse
    have hs := List.Sublist.of_cons_of_ne hne hs
    have ht : ([1, 2, 4, 3].map chosen).Sublist (first :: interior) := by
      simpa using hs.reverse
    exact criterion.2.2.2 (build _ word.dropLast chosen (by decide) rfl hi (dropWord.symm ▸ ht))
  let middle := chosen 2
  let upper := chosen 4
  have middleBounds : first < middle ∧ middle < last := by dsimp [middle]; omega
  have upperBound : last < upper := by dsimp [upper]; omega
  have pair : [middle, upper].Sublist interior := by
    have hs : [middle, upper, last].Sublist (interior ++ [last]) := by
      apply (List.cons_sublist_cons (a := first)).mp
      simpa [word, chosenFirst, chosenLast, middle, upper] using selected
    have hr : (last :: [upper, middle]).Sublist (last :: interior.reverse) := by
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
  have cannotReverse (left right : ℕ) (hl : [left, right].Sublist interior)
      (hr : [right, left].Sublist interior) : False := by
    have hh := interiorNodup.sublist (chain interior left right left interiorNodup hl hr)
    simpa using hh
  have noLowerBefore (lower : ℕ) (hs : [lower, middle].Sublist interior)
      (hl : lower < first) : False :=
    noAscendingUpper lower middle upper (chain interior lower middle upper interiorNodup hs pair)
      (by omega) middleBounds.2 upperBound
  have middleBeforeLower (lower : ℕ) (hv : lower ∈ interior) (hl : lower < first) :
      [middle, lower].Sublist interior := by
    rcases pairOrder interior middle lower (pair.subset (by simp)) hv (by omega) with hs | hs
    · exact hs
    · exact False.elim (noLowerBefore lower hs hl)
  have lowerMem : 1 ∈ interior := by
    have hv : 1 ∈ word := hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
    simpa [word, show 1 ≠ first by omega, show 1 ≠ last by omega] using hv
  have middleLower : [middle, 1].Sublist interior := middleBeforeLower 1 lowerMem (by omega)
  have noMiddleDescent (value : ℕ) (hs : [middle, value].Sublist interior)
      (hv : first < value ∧ value < middle) : False := by
    rcases insertThird interior middle value 1 hs lowerMem (by omega) (by omega) with
      hh | hh | hh
    · have hp : [1, middle].Sublist interior :=
        (List.sublist_append_left [1, middle] [value]).trans hh
      exact noLowerBefore 1 hp (by omega)
    · exact noMiddleLowerDescent middle 1 value hh hv.2 hv.1 middleBounds.2 (by omega)
    · exact noMiddleDescentLower middle value 1 hh hv.1 hv.2 (by omega)
  have onlyMiddle (value : ℕ) (hv : value ∈ interior)
      (hb : first < value ∧ value < last) : value = middle := by
    by_contra hne
    rcases insertThird interior middle upper value pair hv hne (by omega) with hh | hh | hh
    · by_cases ha : value < middle
      · exact noAscendingUpper value middle upper hh ha middleBounds.2 upperBound
      · have hp : [value, middle].Sublist interior :=
          (List.sublist_append_left [value, middle] [upper]).trans hh
        exact noMiddleDescentLower value middle 1
          (chain interior value middle 1 interiorNodup hp middleLower)
            middleBounds.1 (by omega) (by omega)
    · by_cases ha : middle < value
      · exact noAscendingUpper middle value upper hh ha hb.2 upperBound
      · have hp : [middle, value].Sublist interior :=
          (List.sublist_append_left [middle, value] [upper]).trans hh
        exact noMiddleDescent value hp ⟨hb.1, by omega⟩
    · by_cases ha : middle < value
      · exact noMiddleUpperAscent middle upper value hh middleBounds.1 ha hb.2 upperBound
      · have hp : [middle, value].Sublist interior :=
          ((List.sublist_cons_self upper [value]).cons_cons middle).trans hh
        exact noMiddleDescent value hp ⟨hb.1, by omega⟩
  have middleBeforeUpper (value : ℕ) (hv : value ∈ interior) (hu : last < value) :
      [middle, value].Sublist interior := by
    rcases pairOrder interior middle value (pair.subset (by simp)) hv (by omega) with hs | hs
    · exact hs
    · exact False.elim (noUpperMiddleLower value middle 1
        (chain interior value middle 1 interiorNodup hs middleLower) hu middleBounds (by omega))
  have rangeMiddle (value : ℕ) (hb : first < value ∧ value < last) : value ∈ interior := by
    have hv : value ∈ word := hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
    simpa [word, show value ≠ first by omega, show value ≠ last by omega] using hv
  have middleEq : middle = first + 1 := by
    exact (onlyMiddle (first + 1) (rangeMiddle _ (by omega)) (by omega)).symm
  have lastEq : last = first + 2 := by
    have hh := onlyMiddle (last - 1) (rangeMiddle _ (by omega)) (by omega)
    omega
  obtain ⟨before, suffix, split⟩ :=
    List.mem_iff_append.mp (pair.subset (by simp : middle ∈ _))
  have prefixEmpty : before = [] := by
    cases before with
    | nil => rfl
    | cons head tail =>
      have hs : [head, middle].Sublist interior := by
        rw [split]
        simpa only [List.cons_append] using
          (List.singleton_sublist.mpr
            (by simp : middle ∈ tail ++ middle :: suffix)).cons_cons head
      have hne : head ≠ middle := by
        simpa using (List.nodup_cons.mp (interiorNodup.sublist hs)).1
      rcases colors head (hs.subset (by simp)) with hl | hm | hu
      · exact False.elim (noLowerBefore head hs hl)
      · exact False.elim (hne (onlyMiddle head (hs.subset (by simp)) hm))
      · exact False.elim (cannotReverse head middle hs
          (middleBeforeUpper head (hs.subset (by simp)) hu))
  have interiorEq : interior = middle :: suffix := by simpa [prefixEmpty] using split
  have suffixNodup : suffix.Nodup := (List.nodup_cons.mp (interiorEq ▸ interiorNodup)).2
  have suffixSub : suffix.Sublist interior := by rw [interiorEq]; exact List.sublist_cons_self _ _
  have suffixColors (value : ℕ) (hv : value ∈ suffix) : value < first ∨ last < value := by
    rcases colors value (suffixSub.subset hv) with hl | hm | hu
    · exact Or.inl hl
    · have he := onlyMiddle value (suffixSub.subset hv) hm
      exact False.elim ((List.nodup_cons.mp (interiorEq ▸ interiorNodup)).1 (he ▸ hv))
    · exact Or.inr hu
  have lowerSorted : (suffix.filter (fun value => decide (value < first))).Pairwise (· > ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : left ∈ _))).2
    have hr := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : right ∈ _))).2
    have hs := hs.trans List.filter_sublist
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp (suffixNodup.sublist hs)).1
    by_contra hnot
    let witness := fun rank : ℕ => if rank = 1 then left else if rank = 2 then right
      else if rank = 3 then first else last
    apply criterion.2.1 3 (by omega) (by omega)
    change Occurs [3, 1, 2, 4] word
    refine build _ _ witness (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
    · simpa [word, witness] using
        ((hs.trans suffixSub).append (List.Sublist.refl [last])).cons_cons first
  have upperSorted : (suffix.filter (fun value => decide (last < value))).Pairwise (· < ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : left ∈ _))).2
    have hr := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : right ∈ _))).2
    have hs := hs.trans List.filter_sublist
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp (suffixNodup.sublist hs)).1
    by_contra hnot
    let witness := fun rank : ℕ => if rank = 1 then first else if rank = 2 then middle
      else if rank = 3 then right else left
    apply criterion.2.2.2
    rw [dropWord, interiorEq]
    refine build _ _ witness (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
    · simpa [witness] using (hs.cons_cons middle).cons_cons first
  have baseNodup : (List.range' 1 (first - 1) ++
      List.range' (last + 1) (size - last)).Nodup := List.nodup_append.mpr
    ⟨List.nodup_range', List.nodup_range', by
      intro left hl right hr he
      have := List.mem_range'_1.mp hl
      have := List.mem_range'_1.mp hr
      omega⟩
  have suffixPerm : suffix.Perm (List.range' 1 (first - 1) ++
      List.range' (last + 1) (size - last)) := by
    apply (List.perm_ext_iff_of_nodup suffixNodup baseNodup).mpr
    intro value
    simp only [List.mem_append, List.mem_range'_1]
    constructor
    · intro hv
      have hb := bounds value (by simp [word, suffixSub.subset hv])
      rcases suffixColors value hv with hl | hu
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · intro hv
      have hb : 1 ≤ value ∧ value ≤ size := by rcases hv with hv | hv <;> omega
      have hn : value ≠ first ∧ value ≠ last ∧ value ≠ middle := by
        rcases hv with hv | hv <;> omega
      have hm : value ∈ word := hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      simpa [word, interiorEq, hn.1, hn.2.1, hn.2.2] using hm
  refine ⟨lastEq, ?_, suffix, ?_, suffixPerm, lowerSorted, upperSorted⟩
  · have hh := bounds upper (by simp [word, pair.subset (by simp : upper ∈ _)])
    omega
  · simpa only [middleEq] using interiorEq

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxSize 4096 in
theorem mixed_nonempty_lower_endpoint_count (size first : ℕ)
    (hfirst : 2 ≤ first) (hupper : first + 2 < size) :
    ({word : List ℕ | word.Perm (List.range' 1 size) ∧
      word.head? = some first ∧ word.getLast? = some (first + 2) ∧
      ∀ cut < size, Occurs [1, 2, 4, 3] (word.rotate cut) ↔ cut = 0} :
      Set (List ℕ)).ncard = (size - 3).choose (first - 1) := by
  let last := first + 2
  let lower := (List.range' 1 (first - 1)).reverse
  let upper := List.range' (last + 1) (size - last)
  let predicate := fun value : ℕ => decide (value < first)
  let domain : Set (List ℕ) := {suffix | suffix.Perm (lower ++ upper) ∧
    suffix.filter predicate = lower ∧ suffix.filter (fun value => !predicate value) = upper}
  let target : Set (List ℕ) := {word | word.Perm (List.range' 1 size) ∧
    word.head? = some first ∧ word.getLast? = some last ∧
    ∀ cut < size, Occurs [1, 2, 4, 3] (word.rotate cut) ↔ cut = 0}
  let emit := fun suffix : List ℕ => first :: (first + 1) :: suffix ++ [last]
  have basePerm : (first :: (first + 1) :: lower ++ upper ++ [last]).Perm
      (List.range' 1 size) := by
    have hr : List.range' 1 size = List.range' 1 (first - 1) ++
        [first, first + 1, last] ++ upper := by
      conv_lhs => rw [show size = (first - 1) + 3 + (size - last) by dsimp [last]; omega]
      rw [← List.range'_append, ← List.range'_append]
      simp only [Nat.one_mul, show 1 + (first - 1) = first by omega,
        show 1 + (first - 1 + 3) = last + 1 by dsimp [last]; omega]
      simp [List.range'_succ, last, upper]
    apply List.perm_iff_count.mpr
    intro value
    rw [hr]
    simp only [lower, List.count_reverse, List.count_cons, List.count_append, List.count_nil]
    omega
  have emitPerm (suffix : List ℕ) (hp : suffix.Perm (lower ++ upper)) :
      (emit suffix).Perm (List.range' 1 size) :=
    ((hp.append_right [last]).cons (first + 1)).cons first |>.trans basePerm
  have construction (suffix : List ℕ) (hp : suffix ∈ domain) :
      ∀ cut < size, Occurs [1, 2, 4, 3] ((emit suffix).rotate cut) ↔ cut = 0 := by
    let word := emit suffix
    have wordPerm := emitPerm suffix hp.1
    have wordNodup := wordPerm.nodup_iff.mpr List.nodup_range'
    change word.Nodup at wordNodup
    have suffixBounds (value : ℕ) (hv : value ∈ suffix) : value < first ∨ last < value := by
      have hh := hp.1.mem_iff.mp hv
      simp only [lower, upper, List.mem_append, List.mem_reverse, List.mem_range'_1] at hh
      rcases hh with hh | hh <;> omega
    let bucket := fun value : ℕ => if value < first then 0 else if value = first then 1
      else if value < last then 2 else if value = last then 3 else 4
    have bucketBound (value : ℕ) : bucket value < 5 := by
      dsimp [bucket]; split_ifs <;> omega
    let color := fun value : ℕ => (⟨bucket value, bucketBound value⟩ : Fin 5)
    let slot := fun shade : Fin 5 => if shade = 1 then 0 else if shade = 2 then 1
      else if shade = 3 then 3 else 2
    let position := fun value : ℕ => slot (color value)
    have firstColor : color first = 1 := by simp [color, bucket]
    have middleColor : color (first + 1) = 2 := by
      simp [color, bucket, last, show ¬ first + 1 < first by omega]
    have lastColor : color last = 3 := by
      simp [color, bucket, last, show ¬ first + 2 < first by omega]
    have suffixSlot (value : ℕ) (hv : value ∈ suffix) : position value = 2 := by
      rcases suffixBounds value hv with hh | hh
      · simp [position, slot, color, bucket, hh]
      · simp [position, slot, color, bucket, show ¬ value < first by dsimp [last] at hh; omega,
          show value ≠ first by dsimp [last] at hh; omega, show ¬ value < last by omega,
          show value ≠ last by omega]
    have firstPosition : position first = 0 := by simp [position, slot, firstColor]
    have middlePosition : position (first + 1) = 1 := by simp [position, slot, middleColor]
    have lastPosition : position last = 3 := by simp [position, slot, lastColor]
    have positions : word.Pairwise (fun left right => position left ≤ position right) := by
      have hs : suffix.Pairwise (fun left right => position left ≤ position right) := by
        apply List.pairwise_iff_forall_sublist.mpr
        intro left right hs
        simp [suffixSlot left (hs.subset (by simp)), suffixSlot right (hs.subset (by simp))]
      simp only [word, emit, List.cons_append, List.pairwise_cons, List.pairwise_append,
        List.pairwise_singleton, List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, forall_false, or_imp, forall_and, forall_eq, and_true]
      and_intros
      all_goals first
        | exact hs
        | (intros; simp [firstPosition, middlePosition, lastPosition, suffixSlot, *])
    have lowColor (value : ℕ) (hc : color value = 0) : value < first := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he; split_ifs at he <;> omega
    have highColor (value : ℕ) (hc : color value = 4) : last < value := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he; split_ifs at he <;> omega
    have singletonColor (left right : ℕ) (he : color left = color right)
        (hl : color left ≠ 0) (hu : color left ≠ 4) : left = right := by
      have hc := congrArg Fin.val he
      have hl : bucket left ≠ 0 := by simpa [color, Fin.ext_iff] using hl
      have hu : bucket left ≠ 4 := by simpa [color, Fin.ext_iff] using hu
      dsimp [color, bucket, last] at hc hl hu
      split_ifs at hc hl hu <;> omega
    have lowerWord : word.filter predicate = lower := by
      simp [word, emit, predicate, hp.2.1, last, show ¬ first + 1 < first by omega,
        show ¬ first + 2 < first by omega]
    have highSuffix : suffix.filter (fun value => decide (last < value)) = upper := by
      have he : suffix.filter (fun value => decide (last < value)) =
          suffix.filter (fun value => !predicate value) := by
        apply List.filter_congr
        intro value hv
        rcases suffixBounds value hv with hh | hh
        · simp [predicate, hh, show ¬ last < value by dsimp [last]; omega]
        · simp [predicate, hh, show ¬ value < first by dsimp [last] at hh; omega]
      exact he.trans hp.2.2
    have upperWord : word.filter (fun value => decide (last < value)) = upper := by
      simp [word, emit, highSuffix, last, show ¬ first + 2 < first by omega,
        show ¬ first + 2 < first + 1 by omega]
    have lowerSorted : lower.Pairwise (· > ·) := by
      simpa only [lower, List.pairwise_reverse] using
        (List.pairwise_lt_range' (s := 1) (n := first - 1))
    have upperSorted : upper.Pairwise (· < ·) := List.pairwise_lt_range' _ (by omega)
    let allowed := fun left right : Fin 5 => fun ascending : Bool =>
      slot left ≤ slot right ∧ (left = right →
        (left = 0 ∧ ascending = false) ∨ (left = 4 ∧ ascending = true))
    have pairAllowed (left right : ℕ) (hs : [left, right].Sublist word) :
        allowed (color left) (color right) (decide (left < right)) := by
      refine ⟨List.pairwise_iff_forall_sublist.mp positions hs, ?_⟩
      intro he
      by_cases hl : color left = 0
      · have hr : color right = 0 := he.symm.trans hl
        have hsub := hs.filter predicate
        have hsub : [left, right].Sublist lower := by
          simpa [predicate, lowColor left hl, lowColor right hr, lowerWord] using hsub
        have hd := List.pairwise_iff_forall_sublist.mp lowerSorted hsub
        exact Or.inl ⟨hl, by simp; omega⟩
      · by_cases hu : color left = 4
        · have hr : color right = 4 := he.symm.trans hu
          have hsub := hs.filter (fun value => decide (last < value))
          have hsub : [left, right].Sublist upper := by
            simpa [highColor left hu, highColor right hr, upperWord] using hsub
          have hi := List.pairwise_iff_forall_sublist.mp upperSorted hsub
          exact Or.inr ⟨hu, by simp [hi]⟩
        · have hne : left ≠ right := by
            simpa using (List.nodup_cons.mp (wordNodup.sublist hs)).1
          exact False.elim (hne (singletonColor left right he hl hu))
    let patternColors := fun (left second third right : Fin 5) (index : ℕ) =>
      if index = 1 then left else if index = 2 then second else if index = 3 then third else right
    let fits := fun (pattern : List ℕ) (left second third right : Fin 5) =>
      pattern.Pairwise (fun before after =>
        allowed (patternColors left second third right before)
          (patternColors left second third right after)
          (@decide (before < after) (Nat.decLt before after)))
    have profiles : ∀ left second third right : Fin 5, left ≤ second → second ≤ third →
        third ≤ right →
        (fits [1, 2, 4, 3] left second third right → left = 1 ∧ third = 3) ∧
        ¬ fits [2, 4, 3, 1] left second third right ∧
        ¬ fits [4, 3, 1, 2] left second third right ∧
        ¬ fits [3, 1, 2, 4] left second third right := by
      simp only [fits, List.pairwise_cons, List.Pairwise.nil, List.mem_cons,
        List.not_mem_nil, forall_eq_or_imp, forall_false, forall_const, and_true]
      dsimp only [allowed, patternColors, slot]
      decide
    have colorMono (left right : ℕ) (hh : left ≤ right) : color left ≤ color right := by
      change bucket left ≤ bucket right
      dsimp [bucket]; split_ifs <;> omega
    have matching (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hp : pattern.Perm [1, 2, 3, 4]) (hc : container.Sublist word)
        (hs : (pattern.map chosen).Sublist container)
        (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1)) :
        fits pattern (color (chosen 1)) (color (chosen 2)) (color (chosen 3))
          (color (chosen 4)) := by
      have h12 := hi 1 (by omega) (by omega)
      have h23 := hi 2 (by omega) (by omega)
      have h34 := hi 3 (by omega) (by omega)
      simp only [Nat.reduceAdd] at h12 h23 h34
      apply List.pairwise_iff_forall_sublist.mpr
      intro left right ht
      have leftMem := hp.mem_iff.mp (ht.subset (by simp : left ∈ _))
      have rightMem := hp.mem_iff.mp (ht.subset (by simp : right ∈ _))
      have leftBound : 1 ≤ left ∧ left ≤ 4 := by simp at leftMem; omega
      have rightBound : 1 ≤ right ∧ right ≤ 4 := by simp at rightMem; omega
      have colorsAt (rank : ℕ) (hb : 1 ≤ rank ∧ rank ≤ 4) :
          patternColors (color (chosen 1)) (color (chosen 2)) (color (chosen 3))
            (color (chosen 4)) rank = color (chosen rank) := by
        obtain ⟨hlo, hhi⟩ := hb
        interval_cases rank <;> simp [patternColors]
      have faithful : decide (chosen left < chosen right) = decide (left < right) := by
        obtain ⟨hll, hlh⟩ := leftBound
        obtain ⟨hrl, hrh⟩ := rightBound
        apply Bool.decide_congr
        interval_cases left <;> interval_cases right <;>
          simp only [Nat.reduceLT, iff_false, iff_true] <;> omega
      change allowed _ _ _
      rw [colorsAt left leftBound, colorsAt right rightBound]
      exact faithful ▸ pairAllowed _ _ ((ht.map chosen).trans (hs.trans hc))
    have firstEndpoint (value : ℕ) (hc : color value = 1) : value = first := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he; split_ifs at he <;> omega
    have lastEndpoint (value : ℕ) (hc : color value = 3) : value = last := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he; split_ifs at he <;> omega
    have profile (chosen : ℕ → ℕ)
        (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1)) :=
      profiles (color (chosen 1)) (color (chosen 2)) (color (chosen 3)) (color (chosen 4))
        (colorMono _ _ (hi 1 (by omega) (by omega)).le)
        (colorMono _ _ (hi 2 (by omega) (by omega)).le)
        (colorMono _ _ (hi 3 (by omega) (by omega)).le)
    have forcedEndpoints (container : List ℕ) (hc : container.Sublist word)
        (ho : Occurs [1, 2, 4, 3] container) : first ∈ container ∧ last ∈ container := by
      obtain ⟨chosen, hi, _, hs, _⟩ := ho
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa [letters] using hi
      have hp := (profile chosen hi').1 (matching _ _ _ (by decide) hc hs hi')
      exact ⟨firstEndpoint _ hp.1 ▸ hs.subset (by simp),
        lastEndpoint _ hp.2 ▸ hs.subset (by simp)⟩
    apply (unique_bad_cut_iff size (by omega) [1, 2, 4, 3] word (by decide) wordPerm).mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hu : last + 1 ∈ suffix := hp.1.mem_iff.mpr (by
        simp only [List.mem_append, upper, List.mem_range'_1]
        exact Or.inr (by dsimp [last]; omega))
      let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then first + 1
        else if rank = 3 then last else last + 1
      refine ⟨chosen, ?_, ?_, ?_, by simp⟩
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by simp [letters] at hhi; omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen, last]
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
          simp [letters] at hhi; omega
        rcases hh with rfl | rfl | rfl | rfl <;> simp [word, emit, chosen, hu]
      · simpa [word, emit, chosen] using
          ((List.singleton_sublist.mpr hu).append (List.Sublist.refl [last])).cons_cons
            (first + 1) |>.cons_cons first
    · intro shift hlo hhi ho
      have hh : shift = 1 ∨ shift = 2 ∨ shift = 3 := by omega
      rcases hh with rfl | rfl | rfl
      all_goals
        obtain ⟨chosen, hi, _, hs, _⟩ := ho
        have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
          simpa [letters] using hi
      · exact (profile chosen hi').2.1 (matching _ _ _ (by decide) (List.Sublist.refl _) hs hi')
      · exact (profile chosen hi').2.2.1 (matching _ _ _ (by decide) (List.Sublist.refl _) hs hi')
      · exact (profile chosen hi').2.2.2 (matching _ _ _ (by decide) (List.Sublist.refl _) hs hi')
    · intro ho
      exact (List.nodup_cons.mp wordNodup).1
        ((forcedEndpoints word.tail (List.tail_sublist _) ho).1)
    · intro ho
      have hh := (forcedEndpoints word.dropLast (List.dropLast_sublist _) ho).2
      have ht : word = (first :: (first + 1) :: suffix) ++ [last] := rfl
      have hn := List.nodup_append.mp (ht ▸ wordNodup)
      have he : word.dropLast = first :: (first + 1) :: suffix := by
        rw [ht, List.dropLast_append_cons]; simp
      exact hn.2.2 last (he ▸ hh) last (by simp) rfl
  have emitMember (suffix : List ℕ) (hp : suffix ∈ domain) : emit suffix ∈ target := by
    refine ⟨emitPerm suffix hp.1, by simp [emit], ?_, construction suffix hp⟩
    change ((first :: (first + 1) :: suffix) ++ [last]).getLast? = some last
    rw [List.getLast?_append_cons]; rfl
  have emitSurjective (word : List ℕ) (hw : word ∈ target) :
      ∃ suffix ∈ domain, emit suffix = word := by
    obtain ⟨front, hlast⟩ := List.getLast?_eq_some_iff.mp hw.2.2.1
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = first :: interior ++ [last] := by
      cases front with
      | nil => have := hw.1.length_eq; simp [hlast] at this; omega
      | cons head interior =>
        have hh : head = first := by simpa [hlast] using hw.2.1
        exact ⟨interior, by simpa [hh] using hlast⟩
    obtain ⟨_, _, suffix, he, hp, hl, hu⟩ := mixed_nonempty_lower_normal_form size first last
      interior (by omega) hfirst (by dsimp [last]; omega) (hsplit ▸ hw.1) (hsplit ▸ hw.2.2.2)
    have colors (value : ℕ) (hv : value ∈ suffix) : value < first ∨ last < value := by
      have hh := hp.mem_iff.mp hv
      simp only [List.mem_append, List.mem_range'_1] at hh
      rcases hh with hh | hh <;> omega
    have permFilters := (hp.filter predicate)
    have lowFilter : (List.range' 1 (first - 1)).filter predicate =
        List.range' 1 (first - 1) := List.filter_eq_self.mpr (by
      intro value hv; have := List.mem_range'_1.mp hv; simp [predicate]; omega)
    have highFilter : upper.filter predicate = [] := List.filter_eq_nil_iff.mpr (by
      intro value hv; have := List.mem_range'_1.mp hv; simp [predicate]; dsimp [last] at *; omega)
    have lowerPerm : (suffix.filter predicate).Perm (List.range' 1 (first - 1)) := by
      rw [List.filter_append] at permFilters
      change (suffix.filter predicate).Perm
        ((List.range' 1 (first - 1)).filter predicate ++ upper.filter predicate) at permFilters
      simpa only [List.filter_append, lowFilter, highFilter, List.append_nil] using permFilters
    have lowEq : suffix.filter predicate = lower := by
      apply (lowerPerm.trans (List.reverse_perm _).symm).eq_of_pairwise
        (fun _ _ hh hn => by omega) hl
      simpa only [List.pairwise_reverse] using
        (List.pairwise_lt_range' (s := 1) (n := first - 1))
    have upperPerm : (suffix.filter (fun value => decide (last < value))).Perm upper := by
      have hh := hp.filter (fun value => decide (last < value))
      rw [List.filter_append] at hh
      change (suffix.filter (fun value => decide (last < value))).Perm
        ((List.range' 1 (first - 1)).filter (fun value => decide (last < value)) ++
          upper.filter (fun value => decide (last < value))) at hh
      have hlow : (List.range' 1 (first - 1)).filter (fun value => decide (last < value)) = [] :=
        List.filter_eq_nil_iff.mpr (by
          intro value hv; have := List.mem_range'_1.mp hv; simp; dsimp [last]; omega)
      have hhigh : upper.filter (fun value => decide (last < value)) = upper :=
        List.filter_eq_self.mpr (by
          intro value hv; have := List.mem_range'_1.mp hv; simp; omega)
      simpa only [List.filter_append, hlow, hhigh, List.nil_append] using hh
    have highEq : suffix.filter (fun value => decide (last < value)) = upper :=
      upperPerm.eq_of_pairwise (by intro left right hl hr; omega) hu
        (List.pairwise_lt_range' _ (by omega))
    have highComplement : suffix.filter (fun value => !predicate value) = upper := by
      rw [← highEq]
      apply List.filter_congr
      intro value hv
      rcases colors value hv with hh | hh
      · simp [predicate, hh, show ¬ last < value by dsimp [last]; omega]
      · simp [predicate, hh, show ¬ value < first by dsimp [last] at hh; omega]
    refine ⟨suffix, ⟨?_, lowEq, highComplement⟩, ?_⟩
    · exact hp.trans ((List.reverse_perm _).symm.append_right upper)
    · simpa only [emit, he] using hsplit.symm
  have hcard := Set.ncard_congr (s := domain) (t := target) (fun suffix _ => emit suffix)
    emitMember (by
      intro left right hl hr he
      exact List.append_cancel_right (List.cons.inj (List.cons.inj he).2).2) (by
      intro word hw
      obtain ⟨suffix, hs, he⟩ := emitSurjective word hw
      exact ⟨suffix, hs, he⟩)
  have hcount := RotationAvoidanceAscending.shuffle_count predicate lower upper
    (by intro value hv; have := List.mem_range'_1.mp (List.mem_reverse.mp hv); simp [predicate];
        omega)
    (by intro value hv; have := List.mem_range'_1.mp hv; simp [predicate]; dsimp [last] at *;
        omega)
  change target.ncard = _
  rw [← hcard]
  change domain.ncard = _ at hcount
  simpa only [lower, upper, List.length_reverse, List.length_range',
    show first - 1 + (size - last) = size - 3 by dsimp [last]; omega] using hcount

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixed
