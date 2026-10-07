/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMiddle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMiddle
   mirror-E: none(waiver:positive-middle-endpoint-normal-form)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A positive middle interval forces the five increasing blocks of the 2143 slice. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceOneAscent
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMiddle

open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceCircular RotationAvoidanceOneAscent

theorem paired_endpoint_middle_normal_form (size first last : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size) (hgap : first + 1 < last)
    (hperm : (first :: interior ++ [last]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [2, 1, 4, 3] ((first :: interior ++ [last]).rotate cut) ↔ cut = 0) :
    ∃ lowerSplit upperSplit : ℕ, 1 ≤ lowerSplit ∧ lowerSplit < first ∧
      upperSplit < size - last ∧
      interior = List.range' (last + 1) upperSplit ++ List.range' 1 lowerSplit ++
        List.range' (first + 1) (last - first - 1) ++
        List.range' (last + upperSplit + 1) (size - last - upperSplit) ++
        List.range' (lowerSplit + 1) (first - 1 - lowerSplit) := by
  classical
  let word := first :: interior ++ [last]
  let isMiddle := fun value : ℕ => decide (first < value ∧ value < last)
  let isLower := fun value : ℕ => decide (value < first)
  let isUpper := fun value : ℕ => decide (last < value)
  have criterion := (unique_bad_cut_iff size hsize [2, 1, 4, 3] word
    (by decide) hperm).mp hcuts
  obtain ⟨endpointOrder, lowerSorted, upperSorted, low, high, selected, lowBound, highBound⟩ :=
    paired_endpoint_color_order size first last interior hsize hperm hcuts
  have hn : word.Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have interiorNodup : interior.Nodup :=
    (List.nodup_append.mp (List.nodup_cons.mp hn).2).1
  have notFirst : first ∉ interior := by
    exact fun hh => (List.nodup_cons.mp hn).1 (List.mem_append_left _ hh)
  have notLast : last ∉ interior := by
    exact fun hh => (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.2
      last hh last (by simp) rfl
  have dropWord : word.dropLast = first :: interior := by
    change ((first :: interior) ++ [last]).dropLast = _
    rw [List.dropLast_append_cons]; simp
  have firstBounds : 1 ≤ first ∧ first ≤ size := by
    have hh : first ∈ word := by simp [word]
    have := List.mem_range'_1.mp (hperm.mem_iff.mp hh)
    omega
  have lastBounds : 1 ≤ last ∧ last ≤ size := by
    have hh : last ∈ word := by simp [word]
    have := List.mem_range'_1.mp (hperm.mem_iff.mp hh)
    omega
  have colors (value : ℕ) (hh : value ∈ interior) :
      value < first ∨ (first < value ∧ value < last) ∨ last < value := by
    have hneFirst : value ≠ first := fun heq => notFirst (heq ▸ hh)
    have hneLast : value ≠ last := fun heq => notLast (heq ▸ hh)
    omega
  have build (chosen : ℕ → ℕ) (container : List ℕ)
      (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1))
      (hs : ([2, 1, 4, 3].map chosen).Sublist container) :
      Occurs [2, 1, 4, 3] container := by
    refine ⟨chosen, ?_, ?_, hs, by simp⟩
    · simpa [letters] using hi
    · intro rank hlo hhi
      have hr : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
        simp [letters] at hhi
        omega
      apply hs.subset
      apply List.mem_map_of_mem
      rcases hr with rfl | rfl | rfl | rfl <;> simp
  have noMiddleLowerUpper (middle lower upper : ℕ)
      (hs : [middle, lower, upper].Sublist interior)
      (hm : first < middle ∧ middle < last) (hl : lower < first) (hu : last < upper) :
      False := by
    let chosen := fun rank : ℕ => if rank = 1 then lower else if rank = 2 then middle
      else if rank = 3 then last else upper
    apply criterion.2.2.1
    refine build chosen (interior ++ [last]) ?_ ?_
    · intro rank hlo hhi
      have hr : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hr with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using hs.append (List.Sublist.refl [last])
  have noLowerUpperMiddle (lower upper middle : ℕ)
      (hs : [lower, upper, middle].Sublist interior)
      (hl : lower < first) (hu : last < upper) (hm : first < middle ∧ middle < last) :
      False := by
    let chosen := fun rank : ℕ => if rank = 1 then lower else if rank = 2 then first
      else if rank = 3 then middle else upper
    apply criterion.2.2.2
    rw [dropWord]
    refine build chosen (first :: interior) ?_ ?_
    · intro rank hlo hhi
      have hr : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hr with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using hs.cons_cons first
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
      [extra, left, right].Sublist container ∨
        [left, extra, right].Sublist container ∨
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
      (hb : first < middle ∧ middle < last) : [low, middle, high].Sublist interior := by
    rcases insertThird interior low high middle selected hm (by omega) (by omega) with
      hh | hh | hh
    · exact False.elim (noMiddleLowerUpper _ _ _ hh hb lowBound highBound)
    · exact hh
    · exact False.elim (noLowerUpperMiddle _ _ _ hh lowBound highBound hb)
  have lowBefore (middle : ℕ) (hm : middle ∈ interior)
      (hb : first < middle ∧ middle < last) : [low, middle].Sublist interior :=
    (List.sublist_append_left [low, middle] [high]).trans (enclosed middle hm hb)
  have highAfter (middle : ℕ) (hm : middle ∈ interior)
      (hb : first < middle ∧ middle < last) : [middle, high].Sublist interior :=
    (List.sublist_cons_self low _).trans (enclosed middle hm hb)
  have middleSorted : (interior.filter isMiddle).Pairwise (· < ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : left ∈ _))).2
    have hr := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : right ∈ _))).2
    have hsInterior := hs.trans (List.filter_sublist (p := isMiddle))
    have hne : left ≠ right := by
      have hh := interiorNodup.sublist hsInterior
      simpa using (List.nodup_cons.mp hh).1
    by_contra hnot
    have hdesc : right < left := by omega
    have triple := chain interior low left right interiorNodup
      (lowBefore left (hsInterior.subset (by simp)) hl) hsInterior
    let chosen := fun rank : ℕ => if rank = 1 then low else if rank = 2 then first
      else if rank = 3 then right else left
    apply criterion.2.2.2
    rw [dropWord]
    refine build chosen (first :: interior) ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using triple.cons_cons first
  have noHole (left extra right : ℕ) (hs : [left, extra, right].Sublist interior)
      (hl : first < left ∧ left < last) (hr : first < right ∧ right < last)
      (he : ¬ (first < extra ∧ extra < last)) : False := by
    have hleftExtra : [left, extra].Sublist interior :=
      (List.sublist_append_left [left, extra] [right]).trans hs
    have hextraRight : [extra, right].Sublist interior := (List.sublist_cons_self _ _).trans hs
    rcases colors extra (hs.subset (by simp)) with hlo | hm | hhi
    · have triple := chain interior extra right high interiorNodup hextraRight
        (highAfter right (hs.subset (by simp)) hr)
      have hextraHigh : [extra, high].Sublist interior :=
        ((List.sublist_cons_self right [high]).cons_cons extra).trans triple
      exact noMiddleLowerUpper left extra high
        (chain interior left extra high interiorNodup hleftExtra hextraHigh)
        hl hlo highBound
    · exact he hm
    · have triple := chain interior low left extra interiorNodup
        (lowBefore left (hs.subset (by simp)) hl) hleftExtra
      have hlowExtra : [low, extra].Sublist interior :=
        ((List.sublist_cons_self left [extra]).cons_cons low).trans triple
      exact noLowerUpperMiddle low extra right
        (chain interior low extra right interiorNodup hlowExtra hextraRight)
        lowBound hhi hr
  have contiguous (container : List ℕ)
      (hno : ∀ left extra right, [left, extra, right].Sublist container →
        isMiddle left = true → isMiddle right = true → isMiddle extra = false → False)
      (hex : ∃ value ∈ container, isMiddle value = true) :
      ∃ beforeMiddle suffix, container = beforeMiddle ++ container.filter isMiddle ++ suffix ∧
        (∀ value ∈ beforeMiddle, isMiddle value = false) ∧
        (∀ value ∈ suffix, isMiddle value = false) := by
    induction container with
    | nil => simpa using hex
    | cons head tail ih =>
      by_cases htail : ∃ value ∈ tail, isMiddle value = true
      · obtain ⟨beforeMiddle, suffix, heq, hp, hs⟩ := ih
          (by intro left extra right hh hl hr he; exact hno _ _ _ (hh.cons head) hl hr he)
          htail
        by_cases hhead : isMiddle head = true
        · have hempty : beforeMiddle = [] := by
            cases beforeMiddle with
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
          subst beforeMiddle
          refine ⟨[], suffix, ?_, by simp, hs⟩
          simpa [List.filter_cons, hhead] using congrArg (List.cons head) heq
        · have hf : isMiddle head = false := Bool.eq_false_iff.mpr hhead
          refine ⟨head :: beforeMiddle, suffix, ?_, ?_, hs⟩
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
    have hmem : first + 1 ∈ word := hperm.mem_iff.mpr
      (List.mem_range'_1.mpr (by omega))
    simp only [word, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with (hh | hh) | hh
    · omega
    · exact hh
    · omega
  obtain ⟨beforeMiddle, suffix, split, prefixOutside, suffixOutside⟩ := contiguous interior
    (by intro left extra right hs hl hr he
        exact noHole left extra right hs (of_decide_eq_true hl) (of_decide_eq_true hr)
          (of_decide_eq_false he))
    ⟨first + 1, middleMem, by simp [isMiddle]; omega⟩
  have middleExists : ∃ value ∈ interior.filter isMiddle, first < value ∧ value < last :=
    ⟨first + 1, List.mem_filter.mpr ⟨middleMem, by simp [isMiddle]; omega⟩, by omega⟩
  have prefixSub : beforeMiddle.Sublist interior := by
    rw [split]
    exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)
  have suffixSub : suffix.Sublist interior := by
    rw [split]
    exact List.sublist_append_right _ _
  have separated (container : List ℕ) (hsub : container.Sublist interior)
      (hout : ∀ value ∈ container, isMiddle value = false)
      (hno : ∀ lower upper, [lower, upper].Sublist container →
        lower < first → last < upper → False) :
      container = container.filter isUpper ++ container.filter isLower := by
    induction container with
    | nil => simp
    | cons head tail ih =>
      have ht := ih ((List.sublist_cons_self head _).trans hsub)
        (by intro value hv; exact hout value (by simp [hv]))
        (by intro lower upper hs hl hu; exact hno _ _ (hs.cons head) hl hu)
      rcases colors head (hsub.subset (by simp)) with hl | hm | hu
      · have allLower : ∀ value ∈ tail, value < first := by
          intro value hv
          rcases colors value (hsub.subset (by simp [hv])) with hh | hh | hh
          · exact hh
          · have hn := of_decide_eq_false (hout value (by simp [hv]))
            exact False.elim (hn hh)
          · exact False.elim (hno head value
              ((List.singleton_sublist.mpr hv).cons_cons head) hl hh)
        have heqLower : tail.filter isLower = tail := List.filter_eq_self.mpr
          (by intro value hv; simp [isLower, allLower value hv])
        have heqUpper : tail.filter isUpper = [] := List.filter_eq_nil_iff.mpr
          (by intro value hv; simp [isUpper]; have := allLower value hv; omega)
        simp [isLower, isUpper, hl, show ¬ last < head by omega, heqLower, heqUpper]
      · exact False.elim ((of_decide_eq_false (hout head (by simp))) hm)
      · simpa [isLower, isUpper, hu, show ¬ head < first by omega] using
          congrArg (List.cons head) ht
  have prefixEq := separated beforeMiddle prefixSub prefixOutside (by
    intro lower upper hs hl hu
    obtain ⟨value, hv, hm⟩ := middleExists
    have triple : [lower, upper, value].Sublist interior := by
      rw [split]
      exact (hs.append (List.singleton_sublist.mpr hv)).trans
        (List.sublist_append_left _ suffix)
    exact noLowerUpperMiddle _ _ _ triple hl hu hm)
  have suffixEq := separated suffix suffixSub suffixOutside (by
    intro lower upper hs hl hu
    obtain ⟨value, hv, hm⟩ := middleExists
    have triple : [value, lower, upper].Sublist interior := by
      rw [split]
      rw [List.append_assoc]
      exact ((List.singleton_sublist.mpr hv).append hs).trans
        (List.sublist_append_right beforeMiddle _)
    exact noMiddleLowerUpper _ _ _ triple hm hl hu)
  have filterInterval (predicate : ℕ → Bool) (start count : ℕ)
      (hiff : ∀ value, predicate value = true ∧ value ∈ interior ↔
        value ∈ List.range' start count)
      (hsorted : (interior.filter predicate).Pairwise (· < ·)) :
      interior.filter predicate = List.range' start count := by
    have hp : (interior.filter predicate).Perm (List.range' start count) := by
      apply (List.perm_ext_iff_of_nodup
        (interiorNodup.sublist (List.filter_sublist)) List.nodup_range').mpr
      intro value
      simpa only [List.mem_filter, and_comm] using hiff value
    exact hp.eq_of_pairwise (by intro left right hl hr; omega) hsorted
      (List.pairwise_lt_range' _ (by omega))
  have interiorValues (value : ℕ) : value ∈ interior ↔
      1 ≤ value ∧ value ≤ size ∧ value ≠ first ∧ value ≠ last := by
    constructor
    · intro hv
      have hvWord : value ∈ word := by simp [word, hv]
      have hb := List.mem_range'_1.mp (hperm.mem_iff.mp hvWord)
      exact ⟨hb.1, by omega, fun heq => notFirst (heq ▸ hv),
        fun heq => notLast (heq ▸ hv)⟩
    · intro hv
      have hm : value ∈ word := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr ⟨hv.1, by omega⟩)
      simp only [word, List.mem_cons, List.mem_append, List.mem_singleton,
        List.not_mem_nil, or_false] at hm
      exact (hm.resolve_right hv.2.2.2).resolve_left hv.2.2.1
  have middleEq := filterInterval isMiddle (first + 1) (last - first - 1)
    (by intro value; simp only [isMiddle, decide_eq_true_eq, interiorValues, List.mem_range'_1]
        omega) middleSorted
  have lowerEq := filterInterval isLower 1 (first - 1)
    (by intro value; simp only [isLower, decide_eq_true_eq, interiorValues, List.mem_range'_1]
        omega) lowerSorted
  have upperEq := filterInterval isUpper (last + 1) (size - last)
    (by intro value; simp only [isUpper, decide_eq_true_eq, interiorValues, List.mem_range'_1]
        omega) upperSorted
  have middleLower : (interior.filter isMiddle).filter isLower = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro value hv
    have hh := of_decide_eq_true (List.mem_filter.mp hv).2
    simp [isLower]; omega
  have middleUpper : (interior.filter isMiddle).filter isUpper = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro value hv
    have hh := of_decide_eq_true (List.mem_filter.mp hv).2
    simp [isUpper]; omega
  have noBackwards (before after : List ℕ) (left right : ℕ)
      (hs : [left, right].Sublist (before ++ after))
      (hl : left ∉ before) (hr : right ∉ after) : False := by
    obtain ⟨selectedLeft, selectedRight, heq, hleft, hright⟩ :=
      List.sublist_append_iff.mp hs
    let boundary := selectedLeft.length
    have hbound : boundary ≤ 2 := by
      have hh := congrArg List.length heq
      simp only [List.length_cons, List.length_nil, List.length_append] at hh
      dsimp [boundary]; omega
    have hp : ([left, right].take boundary).Sublist before := by
      simpa only [boundary, heq, List.take_left] using hleft
    have ht : ([left, right].drop boundary).Sublist after := by
      simpa only [boundary, heq, List.drop_left] using hright
    interval_cases boundary
    · exact hr (ht.subset (by simp))
    · exact hl (hp.subset (by simp))
    · exact hl (hp.subset (by simp))
  have lowPrefix : low ∈ beforeMiddle := by
    obtain ⟨value, hv, hm⟩ := middleExists
    have hs := lowBefore value (List.mem_filter.mp hv).1 hm
    by_contra hnot
    have notMiddle : low ∉ interior.filter isMiddle := by
      intro hh; have hb := of_decide_eq_true (List.mem_filter.mp hh).2; omega
    rw [split, List.append_assoc] at hs
    have ht := hs.of_sublist_append_right (by
      intro item hi hb
      have hh : item = low ∨ item = value := by simpa using hi
      rcases hh with hh | hh
      · exact hnot (hh ▸ hb)
      · exact (of_decide_eq_false (prefixOutside value (hh ▸ hb))) hm)
    exact noBackwards (interior.filter isMiddle) suffix low value ht notMiddle
      (by intro hh; exact (of_decide_eq_false (suffixOutside value hh)) hm)
  have highSuffix : high ∈ suffix := by
    obtain ⟨value, hv, hm⟩ := middleExists
    have hs := highAfter value (List.mem_filter.mp hv).1 hm
    by_contra hnot
    have notMiddle : high ∉ interior.filter isMiddle := by
      intro hh; have hb := of_decide_eq_true (List.mem_filter.mp hh).2; omega
    rw [split] at hs
    have ht := hs.of_sublist_append_left (by
      intro item hi hb
      have hh : item = value ∨ item = high := by simpa using hi
      rcases hh with hh | hh
      · exact (of_decide_eq_false (suffixOutside value (hh ▸ hb))) hm
      · exact hnot (hh ▸ hb))
    exact noBackwards beforeMiddle (interior.filter isMiddle) value high ht
      (by intro hh; exact (of_decide_eq_false (prefixOutside value hh)) hm) notMiddle
  have lowerSplitEq : beforeMiddle.filter isLower ++ suffix.filter isLower =
      List.range' 1 (first - 1) := by
    have hh := congrArg (List.filter isLower) split
    simpa only [List.filter_append, middleLower, List.append_nil, lowerEq] using hh.symm
  have upperSplitEq : beforeMiddle.filter isUpper ++ suffix.filter isUpper =
      List.range' (last + 1) (size - last) := by
    have hh := congrArg (List.filter isUpper) split
    simpa only [List.filter_append, middleUpper, List.append_nil, upperEq] using hh.symm
  let lowerSplit := (beforeMiddle.filter isLower).length
  let upperSplit := (beforeMiddle.filter isUpper).length
  have lowerLengths := congrArg List.length lowerSplitEq
  have upperLengths := congrArg List.length upperSplitEq
  simp only [List.length_append, List.length_range'] at lowerLengths upperLengths
  have lowerPositive : 1 ≤ lowerSplit := by
    have hm : low ∈ beforeMiddle.filter isLower :=
      List.mem_filter.mpr ⟨lowPrefix, by simp [isLower, lowBound]⟩
    have := List.length_pos_of_mem hm
    dsimp [lowerSplit]; omega
  have upperRemaining : 0 < (suffix.filter isUpper).length := by
    exact List.length_pos_of_mem
      (List.mem_filter.mpr ⟨highSuffix, by simp [isUpper, highBound]⟩)
  have lowerBound : lowerSplit ≤ first - 1 := by dsimp [lowerSplit]; omega
  have upperBound : upperSplit ≤ size - last := by dsimp [upperSplit]; omega
  have lowerLeftEq : beforeMiddle.filter isLower = List.range' 1 lowerSplit := by
    have hh := congrArg (List.take lowerSplit) lowerSplitEq
    simpa only [lowerSplit, List.take_left,
      List.take_range'_of_length_ge lowerBound] using hh
  have lowerRightEq : suffix.filter isLower =
      List.range' (lowerSplit + 1) (first - 1 - lowerSplit) := by
    have hh := congrArg (List.drop lowerSplit) lowerSplitEq
    simpa only [lowerSplit, List.drop_left, List.drop_range', Nat.mul_one,
      Nat.add_comm 1] using hh
  have upperLeftEq : beforeMiddle.filter isUpper =
      List.range' (last + 1) upperSplit := by
    have hh := congrArg (List.take upperSplit) upperSplitEq
    simpa only [upperSplit, List.take_left,
      List.take_range'_of_length_ge upperBound] using hh
  have upperRightEq : suffix.filter isUpper =
      List.range' (last + upperSplit + 1) (size - last - upperSplit) := by
    have hh := congrArg (List.drop upperSplit) upperSplitEq
    simpa only [upperSplit, List.drop_left, List.drop_range', Nat.mul_one,
      Nat.add_right_comm last 1] using hh
  refine ⟨lowerSplit, upperSplit, lowerPositive, by omega, ?_, ?_⟩
  · dsimp [upperSplit]; omega
  · calc
      interior = beforeMiddle ++ interior.filter isMiddle ++ suffix := split
      _ = _ := by
        conv_lhs =>
          rw [middleEq, prefixEq, suffixEq, lowerLeftEq, lowerRightEq,
            upperLeftEq, upperRightEq]
        simp only [List.append_assoc]


end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMiddle
