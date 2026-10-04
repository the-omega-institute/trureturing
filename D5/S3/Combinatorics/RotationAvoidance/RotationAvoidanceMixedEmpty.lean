/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmpty
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceMixedEmpty
   mirror-E: none(waiver:zero-lower-mixed-endpoint-normal-form)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Forbidden witnesses force a decreasing middle and at most two skew upper runs. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixedEmpty

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

set_option maxHeartbeats 1600000 in
theorem mixed_empty_lower_normal_form (size last : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size) (horder : 1 < last)
    (hperm : (1 :: interior ++ [last]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [1, 2, 4, 3] ((1 :: interior ++ [last]).rotate cut) ↔ cut = 0) :
    2 < last ∧ last < size ∧
      interior.filter (fun value => decide (value < last)) =
        (List.range' 2 (last - 2)).reverse ∧
      ((interior.filter (fun value => decide (last < value)) =
          List.range' (last + 1) (size - last) ∧
        interior ≠ List.range' (last + 1) (size - last) ++
          (List.range' 2 (last - 2)).reverse) ∨
      ∃ split : ℕ, 1 ≤ split ∧ split < size - last ∧
        interior = List.range' (size - split + 1) split ++
          (List.range' 2 (last - 2)).reverse ++
            List.range' (last + 1) (size - last - split)) := by
  classical
  let word := 1 :: interior ++ [last]
  let isMiddle := fun value : ℕ => decide (value < last)
  let isUpper := fun value : ℕ => decide (last < value)
  have criterion := (unique_bad_cut_iff size hsize [1, 2, 4, 3] word
    (by decide) hperm).mp hcuts
  have dropWord : word.dropLast = 1 :: interior := by
    change ((1 :: interior) ++ [last]).dropLast = _
    rw [List.dropLast_append_cons]; simp
  have wordNodup := hperm.nodup_iff.mpr List.nodup_range'
  have interiorNodup := (List.nodup_cons.mp wordNodup).2.sublist
    (List.sublist_append_left interior [last])
  have notFirst : 1 ∉ interior := fun hv =>
    (List.nodup_cons.mp wordNodup).1 (List.mem_append_left _ hv)
  have notLast : last ∉ interior := fun hv =>
    (List.nodup_append.mp (List.nodup_cons.mp wordNodup).2).2.2
      last hv last (by simp) rfl
  have bounds (value : ℕ) (hv : value ∈ word) : 1 ≤ value ∧ value ≤ size := by
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hv); omega
  have colors (value : ℕ) (hv : value ∈ interior) :
      (1 < value ∧ value < last) ∨ last < value := by
    have hn : value ≠ 1 := fun he => notFirst (he ▸ hv)
    have hn' : value ≠ last := fun he => notLast (he ▸ hv)
    have hh := bounds value (by simp [word, hv])
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
      (hl : 1 < left) (ha : left < right) (hr : right < last) (hu : last < upper) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then left
      else if rank = 3 then right else upper
    apply criterion.2.2.2
    rw [dropWord]
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using hs.cons_cons 1
  have noMiddle312 (high low middle : ℕ)
      (hs : [high, low, middle].Sublist interior)
      (hb : low < middle ∧ middle < high ∧ high < last) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then low else if rank = 2 then middle
      else if rank = 3 then high else last
    apply criterion.2.1 3 (by omega) (by omega)
    change Occurs [3, 1, 2, 4] word
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [word, chosen] using (hs.append (List.Sublist.refl [last])).cons 1
  have noMiddleDescent (middle high low : ℕ)
      (hs : [middle, high, low].Sublist interior)
      (hm : 1 < middle ∧ middle < last) (hl : last < low) (hd : low < high) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then middle
      else if rank = 3 then low else high
    apply criterion.2.2.2
    rw [dropWord]
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [chosen] using hs.cons_cons 1
  have noDescentMiddle (high low middle : ℕ)
      (hs : [high, low, middle].Sublist interior)
      (hl : last < low) (hd : low < high) (hm : middle < last) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then middle else if rank = 2 then last
      else if rank = 3 then low else high
    apply criterion.2.1 2 (by omega) (by omega)
    change Occurs [4, 3, 1, 2] word
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [word, chosen] using (hs.append (List.Sublist.refl [last])).cons 1
  have noUpper132 (low high middle : ℕ)
      (hs : [low, high, middle].Sublist interior)
      (hb : last < low ∧ low < middle ∧ middle < high) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then last else if rank = 2 then low
      else if rank = 3 then middle else high
    apply criterion.2.1 1 (by omega) (by omega)
    change Occurs [2, 4, 3, 1] word
    refine build _ _ chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [word, chosen] using (hs.append (List.Sublist.refl [last])).cons 1
  obtain ⟨chosen, hi, _, selected, _⟩ := criterion.1
  have chosen12 : chosen 1 < chosen 2 := by simpa using hi 1 (by omega) (by decide)
  have chosen23 : chosen 2 < chosen 3 := by simpa using hi 2 (by omega) (by decide)
  have chosen34 : chosen 3 < chosen 4 := by simpa using hi 3 (by omega) (by decide)
  have chosenFirst : chosen 1 = 1 := by
    by_contra hne
    exact criterion.2.2.1
      (build _ word.tail chosen (by decide) rfl hi (List.Sublist.of_cons_of_ne hne selected))
  have chosenLast : chosen 3 = last := by
    by_contra hne
    have hs : [chosen 3, chosen 4, chosen 2, chosen 1].Sublist
        (last :: interior.reverse ++ [1]) := by simpa [word] using selected.reverse
    have hs := List.Sublist.of_cons_of_ne hne hs
    have ht : ([1, 2, 4, 3].map chosen).Sublist (1 :: interior) := by
      simpa using hs.reverse
    exact criterion.2.2.2 (build _ word.dropLast chosen (by decide) rfl hi (dropWord.symm ▸ ht))
  let middle := chosen 2
  let upper := chosen 4
  have middleBounds : 1 < middle ∧ middle < last := by dsimp [middle]; omega
  have upperBound : last < upper := by dsimp [upper]; omega
  have pair : [middle, upper].Sublist interior := by
    have hs : [middle, upper, last].Sublist (interior ++ [last]) := by
      apply (List.cons_sublist_cons (a := 1)).mp
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
  have middleSorted : (interior.filter isMiddle).Pairwise (· > ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : left ∈ _))).2
    have hr := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : right ∈ _))).2
    have hs := hs.trans (List.filter_sublist (p := isMiddle))
    have leftBounds := (colors left (hs.subset (by simp))).resolve_right (by omega)
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp (interiorNodup.sublist hs)).1
    by_contra hnot
    have ha : left < right := by omega
    rcases insertThird interior left right upper hs (pair.subset (by simp))
        (by omega) (by omega) with hh | hh | hh
    · have hp : [upper, right].Sublist interior :=
        ((List.sublist_cons_self left [right]).cons_cons upper).trans hh
      have ht := chain interior middle upper right interiorNodup pair hp
      by_cases hm : middle < right
      · exact noMiddleUpperAscent middle upper right ht middleBounds.1 hm hr upperBound
      · have hrightMiddle := (List.sublist_append_left [upper, left] [right]).trans hh
        have hml : [middle, left].Sublist interior :=
          ((List.sublist_cons_self upper [left]).cons_cons middle).trans
            (chain interior middle upper left interiorNodup pair hrightMiddle)
        have hmne : middle ≠ right := by
          intro heq
          have hn := interiorNodup.sublist ht
          simpa [heq] using hn
        exact noMiddle312 middle left right
          (chain interior middle left right interiorNodup hml hs) (by omega)
    · exact noMiddleUpperAscent left upper right hh leftBounds.1 ha hr upperBound
    · exact noAscendingUpper left right upper hh ha hr upperBound
  have filterPerm (predicate : ℕ → Bool) (start width : ℕ)
      (hb : ∀ value, 1 ≤ value → value ≤ size →
        (predicate value = true ↔ start ≤ value ∧ value < start + width))
      (he : predicate 1 = false ∧ predicate last = false)
      (hr : 1 ≤ start ∧ start + width ≤ size + 1) :
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
      have hn : value ≠ 1 := by intro heq; subst value; simp [he.1] at hh
      have hn' : value ≠ last := by intro heq; subst value; simp [he.2] at hh
      have hw : value ∈ word := hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      exact ⟨by simpa [word, hn, hn'] using hw, hh⟩
  have gap : 2 < last := by omega
  have lastBound : last < size := by
    have hh := bounds upper (by simp [word, pair.subset (by simp : upper ∈ _)])
    omega
  have middlePerm : (interior.filter isMiddle).Perm (List.range' 2 (last - 2)) := by
    apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [List.mem_filter, isMiddle, decide_eq_true_eq, List.mem_range'_1]
    constructor
    · rintro ⟨hv, hl⟩
      have hh := (colors value hv).resolve_right (by omega); omega
    · intro hb
      have hv : value ∈ word := hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      exact ⟨by simpa [word, show value ≠ 1 by omega, show value ≠ last by omega] using hv,
        by omega⟩
  have middleEq : interior.filter isMiddle = (List.range' 2 (last - 2)).reverse :=
    (middlePerm.trans (List.reverse_perm _).symm).eq_of_pairwise
      (by intro left right hl hr; omega) middleSorted
      (by simpa only [List.pairwise_reverse] using
        (List.pairwise_lt_range' (s := 2) (n := last - 2)))
  have upperPerm : (interior.filter isUpper).Perm
      (List.range' (last + 1) (size - last)) := by
    apply filterPerm isUpper (last + 1) (size - last)
    · intro value hvlo hvhi
      simp only [isUpper, decide_eq_true_eq]; omega
    · simp [isUpper]; omega
    · omega
  refine ⟨gap, lastBound, middleEq, ?_⟩
  by_cases upperSorted : (interior.filter isUpper).Pairwise (· < ·)
  · left
    refine ⟨upperPerm.eq_of_pairwise (by intro left right hl hr; omega)
      upperSorted (List.pairwise_lt_range'), ?_⟩
    intro he
    have ordered : interior.Pairwise (fun left right =>
        (if last < left then 0 else 1 : ℕ) ≤ if last < right then 0 else 1) := by
      rw [he]
      apply List.pairwise_append.mpr
      refine ⟨List.pairwise_of_forall_mem_list ?_, List.pairwise_of_forall_mem_list ?_, ?_⟩
      · intro left hl right hr
        have := List.mem_range'_1.mp hl; have := List.mem_range'_1.mp hr
        simp [show last < left by omega, show last < right by omega]
      · intro left hl right hr
        have := List.mem_range'_1.mp (List.mem_reverse.mp hl)
        have := List.mem_range'_1.mp (List.mem_reverse.mp hr)
        simp [show ¬ last < left by omega, show ¬ last < right by omega]
      · intro left hl right hr
        have := List.mem_range'_1.mp hl
        have := List.mem_range'_1.mp (List.mem_reverse.mp hr)
        simp [show last < left by omega, show ¬ last < right by omega]
    have hh := List.pairwise_iff_forall_sublist.mp ordered pair
    simp [show ¬ last < middle by omega, upperBound] at hh
  · right
    obtain ⟨high, low, descentPair, descent⟩ : ∃ high low,
        [high, low].Sublist (interior.filter isUpper) ∧ low < high := by
      by_contra! hnone
      apply upperSorted
      apply List.pairwise_iff_forall_sublist.mpr
      intro high low hs
      have hn := (interiorNodup.sublist List.filter_sublist).sublist hs
      have hne : high ≠ low := by simpa using (List.nodup_cons.mp hn).1
      have hh := hnone high low hs
      omega
    have highBound : last < high := of_decide_eq_true
      (List.mem_filter.mp (descentPair.subset (by simp))).2
    have lowBound : last < low := of_decide_eq_true
      (List.mem_filter.mp (descentPair.subset (by simp))).2
    have descentPair := descentPair.trans (List.filter_sublist (p := isUpper))
    have enclosed (value : ℕ) (hv : value ∈ interior) (hb : 1 < value ∧ value < last) :
        [high, value, low].Sublist interior := by
      rcases insertThird interior high low value descentPair hv (by omega) (by omega) with
          hh | hh | hh
      · exact False.elim (noMiddleDescent value high low hh hb lowBound descent)
      · exact hh
      · exact False.elim (noDescentMiddle high low value hh lowBound descent hb.2)
    have highBefore (value : ℕ) (hv : value ∈ interior) (hb : 1 < value ∧ value < last) :
        [high, value].Sublist interior :=
      (List.sublist_append_left [high, value] [low]).trans (enclosed value hv hb)
    have lowAfter (value : ℕ) (hv : value ∈ interior) (hb : 1 < value ∧ value < last) :
        [value, low].Sublist interior :=
      (List.sublist_cons_self high _).trans (enclosed value hv hb)
    have noHole (left extra right : ℕ) (hs : [left, extra, right].Sublist interior)
        (hl : left < last) (hr : right < last) (he : ¬ extra < last) : False := by
      have hleftExtra : [left, extra].Sublist interior :=
        (List.sublist_append_left [left, extra] [right]).trans hs
      have hextraRight : [extra, right].Sublist interior :=
        (List.sublist_cons_self left _).trans hs
      have hb := (colors extra (hs.subset (by simp))).resolve_left (by omega)
      have hlb := (colors left (hs.subset (by simp))).resolve_right (by omega)
      have hrb := (colors right (hs.subset (by simp))).resolve_right (by omega)
      by_cases hd : extra < high
      · have ht := chain interior high left extra interiorNodup
          (highBefore left (hs.subset (by simp)) hlb) hleftExtra
        have hp : [high, extra].Sublist interior :=
          ((List.sublist_cons_self left [extra]).cons_cons high).trans ht
        exact noDescentMiddle high extra right
          (chain interior high extra right interiorNodup hp hextraRight) hb hd hr
      · have ht := chain interior extra right low interiorNodup hextraRight
          (lowAfter right (hs.subset (by simp)) hrb)
        have hp : [extra, low].Sublist interior :=
          ((List.sublist_cons_self right [low]).cons_cons extra).trans ht
        exact noMiddleDescent left extra low
          (chain interior left extra low interiorNodup hleftExtra hp) hlb lowBound (by omega)
    have contiguous (container : List ℕ)
        (hno : ∀ left extra right, [left, extra, right].Sublist container →
          isMiddle left = true → isMiddle right = true → isMiddle extra = false → False)
        (hex : ∃ value ∈ container, isMiddle value = true) :
        ∃ before after, container = before ++ container.filter isMiddle ++ after ∧
          (∀ value ∈ before, isMiddle value = false) ∧
          (∀ value ∈ after, isMiddle value = false) := by
      induction container with
      | nil => simpa using hex
      | cons head tail ih =>
        by_cases htail : ∃ value ∈ tail, isMiddle value = true
        · obtain ⟨before, after, heq, hp, hs⟩ := ih
            (by intro left extra right hh hl hr he; exact hno _ _ _ (hh.cons head) hl hr he)
            htail
          by_cases hhead : isMiddle head = true
          · have hempty : before = [] := by
              cases before with
              | nil => rfl
              | cons extra rest =>
                obtain ⟨value, hv, hm⟩ := htail
                have hf : value ∈ tail.filter isMiddle := List.mem_filter.mpr ⟨hv, hm⟩
                have ht : [head, extra, value].Sublist (head :: tail) := by
                  rw [heq]
                  apply List.Sublist.cons_cons
                  apply List.Sublist.cons_cons
                  exact (List.singleton_sublist.mpr hf).trans
                    ((List.sublist_append_right rest _).trans (List.sublist_append_left _ after))
                exact False.elim (hno head extra value ht hhead hm (hp extra (by simp)))
            subst before
            refine ⟨[], after, ?_, by simp, hs⟩
            simpa [List.filter_cons, hhead] using congrArg (List.cons head) heq
          · have hf : isMiddle head = false := Bool.eq_false_iff.mpr hhead
            refine ⟨head :: before, after, ?_, ?_, hs⟩
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
          have hf : tail.filter isMiddle = [] := List.filter_eq_nil_iff.mpr
            (by intro value hv; simp [ht value hv])
          exact ⟨[], tail, by simp [List.filter_cons, hhead, hf], by simp, ht⟩
    have middleMem : 2 ∈ interior.filter isMiddle := by
      rw [middleEq]
      exact List.mem_reverse.mpr (List.mem_range'_1.mpr (by omega))
    obtain ⟨before, after, hsplit, hb, ha⟩ := contiguous interior
      (by intro left extra right hs hl hr he
          exact noHole left extra right hs (of_decide_eq_true hl) (of_decide_eq_true hr)
            (of_decide_eq_false he))
      ⟨2, (List.mem_filter.mp middleMem).1, (List.mem_filter.mp middleMem).2⟩
    have beforeSub : before.Sublist interior := by
      rw [hsplit]; exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _)
    have afterSub : after.Sublist interior := by
      rw [hsplit]; exact List.sublist_append_right _ _
    have beforeBound (value : ℕ) (hv : value ∈ before) : last < value := by
      have hh := colors value (beforeSub.subset hv)
      have hn := of_decide_eq_false (hb value hv)
      omega
    have afterBound (value : ℕ) (hv : value ∈ after) : last < value := by
      have hh := colors value (afterSub.subset hv)
      have hn := of_decide_eq_false (ha value hv)
      omega
    have beforeSorted : before.Pairwise (· < ·) := by
      apply List.pairwise_iff_forall_sublist.mpr
      intro left right hs
      have hl := beforeBound left (hs.subset (by simp))
      have hr := beforeBound right (hs.subset (by simp))
      have hn := (interiorNodup.sublist beforeSub).sublist hs
      have hne : left ≠ right := by simpa using (List.nodup_cons.mp hn).1
      by_contra hh
      have ht : [left, right, 2].Sublist interior := by
        rw [hsplit]
        exact (hs.append (List.singleton_sublist.mpr middleMem)).trans
          (List.sublist_append_left _ after)
      exact noDescentMiddle left right 2 ht hr (by omega) (by omega)
    have afterSorted : after.Pairwise (· < ·) := by
      apply List.pairwise_iff_forall_sublist.mpr
      intro left right hs
      have hl := afterBound left (hs.subset (by simp))
      have hr := afterBound right (hs.subset (by simp))
      have hn := (interiorNodup.sublist afterSub).sublist hs
      have hne : left ≠ right := by simpa using (List.nodup_cons.mp hn).1
      by_contra hh
      have ht : [2, left, right].Sublist interior := by
        rw [hsplit]
        exact ((List.singleton_sublist.mpr middleMem).append hs).trans
          (by simpa only [List.append_assoc] using List.sublist_append_right before _)
      exact noMiddleDescent 2 left right ht (by omega) hr (by omega)
    have upperEq : interior.filter isUpper = before ++ after := by
      have hbKeep : before.filter isUpper = before := List.filter_eq_self.mpr
        (by intro value hv; simp [isUpper, beforeBound value hv])
      have haKeep : after.filter isUpper = after := List.filter_eq_self.mpr
        (by intro value hv; simp [isUpper, afterBound value hv])
      have hmDrop : (interior.filter isMiddle).filter isUpper = [] :=
        List.filter_eq_nil_iff.mpr (by
          intro value hv
          have hh := of_decide_eq_true (List.mem_filter.mp hv).2
          simp only [isUpper, decide_eq_true_eq]; omega)
      conv_lhs => arg 2; rw [hsplit]
      rw [List.filter_append, List.filter_append, hbKeep, haKeep, hmDrop, List.append_nil]
    have upperConcatPerm : (before ++ after).Perm
        (List.range' (last + 1) (size - last)) := upperEq ▸ upperPerm
    obtain ⟨high, hhigh, low, hlow, hd⟩ :
        ∃ high ∈ before, ∃ low ∈ after, low < high := by
      by_contra! hnone
      apply upperSorted
      rw [upperEq]
      apply List.pairwise_append.mpr ⟨beforeSorted, afterSorted, ?_⟩
      intro left hl right hr
      have hn := upperConcatPerm.nodup_iff.mpr List.nodup_range'
      have hne : left ≠ right := fun he =>
        (List.nodup_append.mp hn).2.2 left hl right hr he
      have hh := hnone left hl right hr
      omega
    have above : ∀ left ∈ before, ∀ right ∈ after, right < left := by
      intro left hl right hr
      have hn := upperConcatPerm.nodup_iff.mpr List.nodup_range'
      have hne : left ≠ right := fun he =>
        (List.nodup_append.mp hn).2.2 left hl right hr he
      by_contra hh
      have ascend : left < right := by omega
      by_cases hleft : left < low
      · have hp : [left, high].Sublist before := by
          rcases pairOrder before left high hl hhigh (by omega) with hp | hp
          · exact hp
          · have hh := List.pairwise_iff_forall_sublist.mp beforeSorted hp
            omega
        have ht : [left, high, low].Sublist interior := by
          rw [hsplit]
          exact ((hp.trans (List.sublist_append_left before _)).append
            (List.singleton_sublist.mpr hlow))
        exact noUpper132 left high low ht ⟨beforeBound left hl, hleft, hd⟩
      · have hnelow : left ≠ low := fun he =>
          (List.nodup_append.mp hn).2.2 left hl low hlow he
        have hp : [low, right].Sublist after := by
          rcases pairOrder after low right hlow hr (by omega) with hp | hp
          · exact hp
          · have hh := List.pairwise_iff_forall_sublist.mp afterSorted hp
            omega
        let chosen := fun rank : ℕ => if rank = 1 then 2 else if rank = 2 then low
          else if rank = 3 then left else right
        apply criterion.2.1 3 (by omega) (by omega)
        change Occurs [3, 1, 2, 4] word
        refine build _ _ chosen (by decide) rfl ?_ ?_
        · intro rank hlo hhi
          have hb := afterBound low hlow
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> simp [chosen] <;> omega
        · have ht : [left, 2, low, right].Sublist interior := by
            rw [hsplit]
            exact ((List.singleton_sublist.mpr hl).append
              (List.singleton_sublist.mpr middleMem)).append hp
          simpa [word, chosen] using (ht.trans (List.sublist_append_left interior [last])).cons 1
    have reorderedEq : after ++ before = List.range' (last + 1) (size - last) :=
      ((List.perm_append_comm : (after ++ before).Perm (before ++ after)).trans
        upperConcatPerm).eq_of_pairwise (by intro left right hl hr; omega)
          (List.pairwise_append.mpr ⟨afterSorted, beforeSorted, by
            intro left hl right hr; exact above right hr left hl⟩) List.pairwise_lt_range'
    let split := before.length
    have hs : 1 ≤ split ∧ split < size - last := by
      have hb : 0 < before.length := List.length_pos_iff.mpr
        (List.ne_nil_of_mem hhigh)
      have ha : 0 < after.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hlow)
      have hh := upperConcatPerm.length_eq
      simp only [List.length_append, List.length_range'] at hh
      dsimp [split]; omega
    have afterLength : after.length = size - last - split := by
      have hh := upperConcatPerm.length_eq
      simp only [List.length_append, List.length_range'] at hh
      dsimp [split]; omega
    have rangeSplit : List.range' (last + 1) (size - last) =
        List.range' (last + 1) (size - last - split) ++
          List.range' (size - split + 1) split := by
      have hh := List.range'_append_1 (s := last + 1) (m := size - last - split) (n := split)
      have hsum : size - last - split + split = size - last := by omega
      have hstart : last + 1 + (size - last - split) = size - split + 1 := by omega
      rw [hsum, hstart] at hh
      exact hh.symm
    have afterEq : after = List.range' (last + 1) (size - last - split) := by
      have hh := congrArg (List.take after.length) (reorderedEq.trans rangeSplit)
      have ht : List.take after.length
          (List.range' (last + 1) (size - last - split) ++
            List.range' (size - split + 1) split) =
              List.range' (last + 1) (size - last - split) := by
        rw [afterLength]
        simpa only [List.length_range'] using
          (List.take_left (l₁ := List.range' (last + 1) (size - last - split))
            (l₂ := List.range' (size - split + 1) split))
      simpa only [List.take_left] using hh.trans ht
    have beforeEq : before = List.range' (size - split + 1) split := by
      have hh := congrArg (List.drop after.length) (reorderedEq.trans rangeSplit)
      have ht : List.drop after.length
          (List.range' (last + 1) (size - last - split) ++
            List.range' (size - split + 1) split) = List.range' (size - split + 1) split := by
        rw [afterLength]
        simpa only [List.length_range'] using
          (List.drop_left (l₁ := List.range' (last + 1) (size - last - split))
            (l₂ := List.range' (size - split + 1) split))
      simpa only [List.drop_left] using hh.trans ht
    exact ⟨split, hs.1, hs.2, by simpa only [beforeEq, afterEq, middleEq] using hsplit⟩

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceMixedEmpty
