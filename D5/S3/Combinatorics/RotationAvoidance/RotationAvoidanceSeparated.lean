/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSeparated
   mirror-E: none(waiver:separated-endpoint-normal-forms)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Endpoint witnesses force the three color blocks of the 2413 slice. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCircular
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSeparated

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

theorem alternating_positive_middle_normal_form (size first last : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size) (hgap : first + 1 < last)
    (hperm : (first :: interior ++ [last]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [2, 4, 1, 3] ((first :: interior ++ [last]).rotate cut) ↔ cut = 0) :
    2 ≤ first ∧ last < size ∧
      interior = interior.filter (fun value => decide (last < value)) ++
        List.range' (first + 1) (last - first - 1) ++
        interior.filter (fun value => decide (value < first)) ∧
      ¬ Occurs [2, 1, 3] (interior.filter (fun value => decide (last < value))) ∧
      ¬ Occurs [4, 1, 3, 2] (interior.filter (fun value => decide (last < value))) ∧
      ¬ Occurs [1, 3, 2] (interior.filter (fun value => decide (value < first))) ∧
      ¬ Occurs [3, 2, 4, 1] (interior.filter (fun value => decide (value < first))) := by
  classical
  let word := first :: interior ++ [last]
  let isUpper := fun value : ℕ => decide (last < value)
  let isMiddle := fun value : ℕ => decide (first < value ∧ value < last)
  let isLower := fun value : ℕ => decide (value < first)
  have criterion := (unique_bad_cut_iff size hsize [2, 4, 1, 3] word
    (by decide) hperm).mp hcuts
  have dropWord : word.dropLast = first :: interior := by
    change ((first :: interior) ++ [last]).dropLast = _
    rw [List.dropLast_append_cons]; simp
  have interiorNodup : interior.Nodup :=
    ((List.nodup_cons.mp (hperm.nodup_iff.mpr List.nodup_range')).2).sublist
      (List.sublist_append_left _ _)
  have notFirst : first ∉ interior := by
    have hh := (List.nodup_cons.mp (hperm.nodup_iff.mpr List.nodup_range')).1
    exact fun hv => hh (List.mem_append_left _ hv)
  have notLast : last ∉ interior := by
    have hh := (List.nodup_append.mp
      (List.nodup_cons.mp (hperm.nodup_iff.mpr List.nodup_range')).2).2.2
    exact fun hv => hh last hv last (by simp) rfl
  have bounds (value : ℕ) (hv : value ∈ word) : 1 ≤ value ∧ value ≤ size := by
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hv)
    omega
  have firstBounds := bounds first (by simp [word])
  have lastBounds := bounds last (by simp [word])
  have colors (value : ℕ) (hv : value ∈ interior) :
      last < value ∨ (first < value ∧ value < last) ∨ value < first := by
    have hfirst : value ≠ first := fun heq => notFirst (heq ▸ hv)
    have hlast : value ≠ last := fun heq => notLast (heq ▸ hv)
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
  have noRotated (pattern : List ℕ) (shift : ℕ) (hs : 0 < shift) (hb : shift < 4)
      (heq : ([2, 4, 1, 3] : List ℕ).rotate shift = pattern) : ¬ Occurs pattern word := by
    simpa only [heq] using criterion.2.1 shift hs hb
  obtain ⟨chosen, chosenIncreasing, _, chosenSublist, _⟩ := criterion.1
  have chosen12 : chosen 1 < chosen 2 := by
    simpa using chosenIncreasing 1 (by omega) (by decide)
  have chosen23 : chosen 2 < chosen 3 := by
    simpa using chosenIncreasing 2 (by omega) (by decide)
  have chosen34 : chosen 3 < chosen 4 := by
    simpa using chosenIncreasing 3 (by omega) (by decide)
  have chosenFirst : chosen 2 = first := by
    by_contra hne
    have hs := List.Sublist.of_cons_of_ne hne chosenSublist
    exact criterion.2.2.1
      (build _ word.tail chosen (by decide) rfl chosenIncreasing hs)
  have chosenLast : chosen 3 = last := by
    by_contra hne
    have hs : [chosen 3, chosen 1, chosen 4, chosen 2].Sublist
        (last :: interior.reverse ++ [first]) := by
      simpa [word] using chosenSublist.reverse
    have hs := List.Sublist.of_cons_of_ne hne hs
    have ht : ([2, 4, 1, 3].map chosen).Sublist (first :: interior) := by
      simpa using hs.reverse
    exact criterion.2.2.2
      (build _ word.dropLast chosen (by decide) rfl chosenIncreasing (dropWord.symm ▸ ht))
  let high := chosen 4
  let low := chosen 1
  have highBound : last < high := by dsimp [high]; omega
  have lowBound : low < first := by dsimp [low]; omega
  have selected : [high, low].Sublist interior := by
    have hs : [chosen 4, chosen 1, last].Sublist (interior ++ [last]) := by
      apply (List.cons_sublist_cons (a := first)).mp
      simpa [word, chosenFirst, chosenLast] using chosenSublist
    have hr : (last :: [chosen 1, chosen 4]).Sublist (last :: interior.reverse) := by
      simpa using hs.reverse
    simpa [high, low] using (List.cons_sublist_cons.mp hr).reverse
  have middleExists : first + 1 ∈ interior := by
    have hh : first + 1 ∈ word := hperm.mem_iff.mpr
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    simpa [word, show first + 1 ≠ first by omega, show first + 1 ≠ last by omega]
      using hh
  have noMiddleHighLow (middle upper lower : ℕ)
      (hs : [middle, upper, lower].Sublist interior)
      (hm : first < middle ∧ middle < last) (hu : last < upper) (hl : lower < first) :
      False := by
    let witness := fun rank : ℕ => if rank = 1 then lower else if rank = 2 then middle
      else if rank = 3 then last else upper
    apply criterion.2.2.1
    refine build [2, 4, 1, 3] (interior ++ [last]) witness (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
    · simpa [witness] using hs.append (List.Sublist.refl [last])
  have noHighLowMiddle (upper lower middle : ℕ)
      (hs : [upper, lower, middle].Sublist interior)
      (hu : last < upper) (hl : lower < first) (hm : first < middle ∧ middle < last) :
      False := by
    let witness := fun rank : ℕ => if rank = 1 then lower else if rank = 2 then first
      else if rank = 3 then middle else upper
    apply criterion.2.2.2
    rw [dropWord]
    refine build [2, 4, 1, 3] (first :: interior) witness (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
    · simpa [witness] using hs.cons_cons first
  have chain (container : List ℕ) (left pivot right : ℕ) (hn : container.Nodup)
      (hl : [left, pivot].Sublist container) (hr : [pivot, right].Sublist container) :
      [left, pivot, right].Sublist container := by
    induction container with
    | nil => simp at hl
    | cons head tail ih =>
      have ht := (List.nodup_cons.mp hn).2
      by_cases hh : head = left
      · subst head
        have hne : pivot ≠ left := by
          have hh := hn.sublist hl
          exact Ne.symm (by simpa using (List.nodup_cons.mp hh).1)
        exact (List.Sublist.of_cons_of_ne hne hr).cons_cons left
      · have hl := List.Sublist.of_cons_of_ne (Ne.symm hh) hl
        have hne : pivot ≠ head := by
          intro heq
          exact (List.nodup_cons.mp hn).1 (heq ▸ hl.subset (by simp))
        exact (ih ht hl (List.Sublist.of_cons_of_ne hne hr)).cons head
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
    | nil => simp at hs
    | cons head tail ih =>
      by_cases hh : head = extra
      · subst head
        exact Or.inl ((List.Sublist.of_cons_of_ne (Ne.symm hneLeft) hs).cons_cons extra)
      · have hm := (List.mem_cons.mp hm).resolve_left (Ne.symm hh)
        by_cases hl : head = left
        · subst head
          have hr := List.singleton_sublist.mp (List.cons_sublist_cons.mp hs)
          have he : extra ∈ tail := (List.mem_cons.mp hm).resolve_left hneLeft
          rcases pairOrder tail extra right he hr hneRight with ht | ht
          · exact Or.inr (Or.inl (ht.cons_cons left))
          · exact Or.inr (Or.inr (ht.cons_cons left))
        · rcases ih (List.Sublist.of_cons_of_ne (Ne.symm hl) hs) hm with ht | ht | ht
          · exact Or.inl (ht.cons head)
          · exact Or.inr (Or.inl (ht.cons head))
          · exact Or.inr (Or.inr (ht.cons head))
  have enclosed (middle : ℕ) (hm : middle ∈ interior)
      (hb : first < middle ∧ middle < last) : [high, middle, low].Sublist interior := by
    rcases insertThird interior high low middle selected hm (by omega) (by omega) with
      hs | hs | hs
    · exact False.elim (noMiddleHighLow _ _ _ hs hb highBound lowBound)
    · exact hs
    · exact False.elim (noHighLowMiddle _ _ _ hs highBound lowBound hb)
  have noUpperSplit (left middle right : ℕ)
      (hs : [left, middle, right].Sublist interior)
      (hl : last < left) (hm : first < middle ∧ middle < last) (hr : last < right) :
      False := by
    have hne : left ≠ right := by
      have hh := interiorNodup.sublist hs
      exact fun heq => (List.nodup_cons.mp hh).1 (by simp [heq])
    by_cases hlt : left < right
    · let witness := fun rank : ℕ => if rank = 1 then first else if rank = 2 then middle
        else if rank = 3 then left else right
      apply noRotated [1, 3, 2, 4] 2 (by omega) (by omega) (by decide)
      refine build _ word witness (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
      · simpa [word, witness] using (hs.trans (List.sublist_append_left _ _)).cons_cons first
    · let witness := fun rank : ℕ => if rank = 1 then middle else if rank = 2 then last
        else if rank = 3 then right else left
      apply noRotated [4, 1, 3, 2] 1 (by omega) (by omega) (by decide)
      refine build _ word witness (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
      · simpa [word, witness] using (hs.append (List.Sublist.refl [last])).cons first
  have noLowerSplit (left middle right : ℕ)
      (hs : [left, middle, right].Sublist interior)
      (hl : left < first) (hm : first < middle ∧ middle < last) (hr : right < first) :
      False := by
    have hne : left ≠ right := by
      have hh := interiorNodup.sublist hs
      exact fun heq => (List.nodup_cons.mp hh).1 (by simp [heq])
    by_cases hlt : left < right
    · let witness := fun rank : ℕ => if rank = 1 then left else if rank = 2 then right
        else if rank = 3 then middle else last
      apply noRotated [1, 3, 2, 4] 2 (by omega) (by omega) (by decide)
      refine build _ word witness (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
      · simpa [word, witness] using (hs.append (List.Sublist.refl [last])).cons first
    · let witness := fun rank : ℕ => if rank = 1 then right else if rank = 2 then left
        else if rank = 3 then first else middle
      apply noRotated [3, 2, 4, 1] 3 (by omega) (by omega) (by decide)
      refine build _ word witness (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
      · simpa [word, witness] using (hs.trans (List.sublist_append_left _ _)).cons_cons first
  have noMiddleUpper (middle upper : ℕ) (hs : [middle, upper].Sublist interior)
      (hm : first < middle ∧ middle < last) (hu : last < upper) : False := by
    have hh : [high, middle].Sublist interior :=
      (List.sublist_append_left _ [low]).trans (enclosed middle (hs.subset (by simp)) hm)
    exact noUpperSplit high middle upper (chain _ _ _ _ interiorNodup hh hs)
      highBound hm hu
  have noLowerMiddle (lower middle : ℕ) (hs : [lower, middle].Sublist interior)
      (hl : lower < first) (hm : first < middle ∧ middle < last) : False := by
    have hh : [middle, low].Sublist interior :=
      (List.sublist_cons_self high _).trans (enclosed middle (hs.subset (by simp)) hm)
    exact noLowerSplit lower middle low (chain _ _ _ _ interiorNodup hs hh) hl hm lowBound
  have noLowerUpper (lower upper : ℕ) (hs : [lower, upper].Sublist interior)
      (hl : lower < first) (hu : last < upper) : False := by
    rcases insertThird interior lower upper (first + 1) hs middleExists
      (by omega) (by omega) with hh | hh | hh
    · exact noMiddleUpper _ _ ((List.sublist_cons_self lower _).cons_cons _ |>.trans hh)
        (by omega) hu
    · exact noLowerMiddle _ _ ((List.sublist_append_left _ [upper]).trans hh) hl (by omega)
    · exact noLowerMiddle _ _ ((List.sublist_cons_self upper _).cons_cons _ |>.trans hh)
        hl (by omega)
  have separated (container : List ℕ) (hs : container.Sublist interior) :
      container = container.filter isUpper ++ container.filter isMiddle ++
        container.filter isLower := by
    induction container with
    | nil => simp
    | cons head tail ih =>
      have ht := ih ((List.sublist_cons_self head _).trans hs)
      rcases colors head (hs.subset (by simp)) with hu | hm | hl
      · simpa [isUpper, isMiddle, isLower, hu, show ¬ head < first by omega,
          show ¬ (first < head ∧ head < last) by omega] using congrArg (List.cons head) ht
      · have noUpper : tail.filter isUpper = [] := List.filter_eq_nil_iff.mpr (by
          intro value hv
          simp only [isUpper]
          simp only [decide_eq_true_eq]
          exact fun hh => noMiddleUpper head value
            (((List.singleton_sublist.mpr hv).cons_cons head).trans hs) hm hh)
        simpa [isUpper, isMiddle, isLower, hm, show ¬ last < head by omega,
          show ¬ head < first by omega, noUpper] using congrArg (List.cons head) ht
      · have allLower : ∀ value ∈ tail, value < first := by
          intro value hv
          rcases colors value (hs.subset (by simp [hv])) with hh | hh | hh
          · exact False.elim (noLowerUpper head value
              (((List.singleton_sublist.mpr hv).cons_cons head).trans hs) hl hh)
          · exact False.elim (noLowerMiddle head value
              (((List.singleton_sublist.mpr hv).cons_cons head).trans hs) hl hh)
          · exact hh
        have noUpper : tail.filter isUpper = [] := List.filter_eq_nil_iff.mpr
          (by intro value hv; simp [isUpper]; have := allLower value hv; omega)
        have noMiddle : tail.filter isMiddle = [] := List.filter_eq_nil_iff.mpr
          (by intro value hv; simp [isMiddle]; have := allLower value hv; omega)
        have lowerEq : tail.filter isLower = tail := List.filter_eq_self.mpr
          (by intro value hv; simp [isLower, allLower value hv])
        simp only [List.filter_cons, show isUpper head = false by simp [isUpper]; omega,
          show isMiddle head = false by simp [isMiddle]; omega,
          show isLower head = true by simp [isLower, hl], Bool.false_eq_true,
          if_false, if_true, noUpper, noMiddle, lowerEq, List.nil_append]
  have middleSorted : (interior.filter isMiddle).Pairwise (· < ·) := by
    apply List.pairwise_iff_forall_sublist.mpr
    intro left right hs
    have hl := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : left ∈ _))).2
    have hr := of_decide_eq_true (List.mem_filter.mp (hs.subset (by simp : right ∈ _))).2
    have hs := hs.trans (List.filter_sublist (p := isMiddle))
    have hne : left ≠ right := by simpa using (List.nodup_cons.mp
      (interiorNodup.sublist hs)).1
    by_contra hnot
    let witness := fun rank : ℕ => if rank = 1 then first else if rank = 2 then right
      else if rank = 3 then left else last
    apply noRotated [1, 3, 2, 4] 2 (by omega) (by omega) (by decide)
    refine build _ word witness (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [witness] <;> dsimp [isMiddle] at * <;> omega
    · simpa [word, witness] using (hs.append (List.Sublist.refl [last])).cons_cons first
  have middlePerm : (interior.filter isMiddle).Perm
      (List.range' (first + 1) (last - first - 1)) := by
    apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [List.mem_filter, isMiddle]
    simp only [decide_eq_true_eq, List.mem_range'_1]
    constructor
    · rintro ⟨_, hh⟩
      rcases hh with ⟨hlo, hhi⟩
      omega
    · intro hh
      have hv : value ∈ word := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hv : value ∈ interior := by
        simpa [word, show value ≠ first by omega, show value ≠ last by omega] using hv
      exact ⟨hv, by omega⟩
  have middleEq := middlePerm.eq_of_pairwise (by intro left right hl hr; omega)
    middleSorted (List.pairwise_lt_range' _ (by omega))
  have upperSub : (interior.filter isUpper).Sublist word :=
    List.filter_sublist.trans ((List.sublist_append_left _ _).cons first)
  have lowerSub : (interior.filter isLower).Sublist word :=
    List.filter_sublist.trans ((List.sublist_append_left _ _).cons first)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := bounds low (by
      have hv : low ∈ interior := selected.subset (by simp)
      simp [word, hv])
    omega
  · have hh := bounds high (by
      have hv : high ∈ interior := selected.subset (by simp)
      simp [word, hv])
    omega
  · simpa only [middleEq] using separated interior (List.Sublist.refl _)
  · rintro ⟨witness, hi, _, hs, _⟩
    have h1 : witness 1 < witness 2 := by simpa using hi 1 (by omega) (by decide)
    have h2 : witness 2 < witness 3 := by simpa using hi 2 (by omega) (by decide)
    have hb := of_decide_eq_true (List.mem_filter.mp
      (hs.subset (by simp : witness 1 ∈ [2, 1, 3].map witness))).2
    let lifted := fun rank : ℕ => if rank = 1 then first else witness (rank - 1)
    apply noRotated [1, 3, 2, 4] 2 (by omega) (by omega) (by decide)
    refine build _ word lifted (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [lifted] <;> omega
    · have hs := hs.trans (List.filter_sublist (p := isUpper))
      simpa [word, lifted] using (hs.trans (List.sublist_append_left _ _)).cons_cons first
  · intro hh
    apply noRotated [4, 1, 3, 2] 1 (by omega) (by omega) (by decide)
    rcases hh with ⟨witness, hi, hm, hs, _⟩
    exact ⟨witness, hi, fun rank hlo hhi => upperSub.subset (hm rank hlo hhi),
      hs.trans upperSub, by simp⟩
  · rintro ⟨witness, hi, _, hs, _⟩
    have h1 : witness 1 < witness 2 := by simpa using hi 1 (by omega) (by decide)
    have h2 : witness 2 < witness 3 := by simpa using hi 2 (by omega) (by decide)
    have hb := of_decide_eq_true (List.mem_filter.mp
      (hs.subset (by simp : witness 3 ∈ [1, 3, 2].map witness))).2
    let lifted := fun rank : ℕ => if rank = 4 then last else witness rank
    apply noRotated [1, 3, 2, 4] 2 (by omega) (by omega) (by decide)
    refine build _ word lifted (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [lifted] <;> omega
    · have hs := hs.trans (List.filter_sublist (p := isLower))
      simpa [word, lifted] using (hs.append (List.Sublist.refl [last])).cons first
  · intro hh
    apply noRotated [3, 2, 4, 1] 3 (by omega) (by omega) (by decide)
    rcases hh with ⟨witness, hi, hm, hs, _⟩
    exact ⟨witness, hi, fun rank hlo hhi => lowerSub.subset (hm rank hlo hhi),
      hs.trans lowerSub, by simp⟩

theorem fibonacci_least_endpoint_normal_form (size last : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size)
    (hperm : (1 :: interior ++ [last]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [1, 3, 2, 4] ((1 :: interior ++ [last]).rotate cut) ↔ cut = 0) :
    4 ≤ last ∧
      interior = interior.filter (fun value => decide (last < value)) ++
        interior.filter (fun value => decide (value < last)) ∧
      (interior.filter (fun value => decide (last < value))).Perm
        (List.range' (last + 1) (size - last)) ∧
      (interior.filter (fun value => decide (value < last))).Perm
        (List.range' 2 (last - 2)) ∧
      ¬ Occurs [2, 1, 3] (interior.filter (fun value => decide (last < value))) ∧
      ¬ Occurs [4, 1, 3, 2] (interior.filter (fun value => decide (last < value))) ∧
      ¬ Occurs [1, 3, 2] (interior.filter (fun value => decide (value < last))) ∧
      ¬ Occurs [2, 1, 3] (interior.filter (fun value => decide (value < last))) ∧
      ¬ (interior.filter (fun value => decide (value < last))).Pairwise (· < ·) := by
  classical
  let word := 1 :: interior ++ [last]
  let isUpper := fun value : ℕ => decide (last < value)
  let isMiddle := fun value : ℕ => decide (value < last)
  have criterion := (unique_bad_cut_iff size hsize [1, 3, 2, 4] word
    (by decide) hperm).mp hcuts
  have dropWord : word.dropLast = 1 :: interior := by
    change ((1 :: interior) ++ [last]).dropLast = _
    rw [List.dropLast_append_cons]; simp
  have wordNodup := hperm.nodup_iff.mpr List.nodup_range'
  have interiorNodup : interior.Nodup :=
    (List.nodup_cons.mp wordNodup).2.sublist (List.sublist_append_left _ _)
  have notFirst : 1 ∉ interior := fun hv =>
    (List.nodup_cons.mp wordNodup).1 (List.mem_append_left _ hv)
  have notLast : last ∉ interior := fun hv =>
    (List.nodup_append.mp (List.nodup_cons.mp wordNodup).2).2.2
      last hv last (by simp) rfl
  have values (value : ℕ) : value ∈ interior ↔
      2 ≤ value ∧ value ≤ size ∧ value ≠ last := by
    constructor
    · intro hv
      have hvWord : value ∈ (1 :: interior ++ [last]) := by simp [hv]
      have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hvWord)
      have hn : value ≠ 1 := fun heq => notFirst (heq ▸ hv)
      exact ⟨by omega, by omega, fun heq => notLast (heq ▸ hv)⟩
    · intro hv
      have hh : value ∈ (1 :: interior ++ [last]) :=
        hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      simpa [show value ≠ 1 by omega, hv.2.2] using hh
  have lastBound : last ≤ size := by
    have hvWord : last ∈ (1 :: interior ++ [last]) := by simp
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hvWord)
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
  obtain ⟨chosen, chosenIncreasing, _, chosenSublist, _⟩ := criterion.1
  have chosen12 : chosen 1 < chosen 2 := by
    simpa using chosenIncreasing 1 (by omega) (by decide)
  have chosen23 : chosen 2 < chosen 3 := by
    simpa using chosenIncreasing 2 (by omega) (by decide)
  have chosen34 : chosen 3 < chosen 4 := by
    simpa using chosenIncreasing 3 (by omega) (by decide)
  have chosenFirst : chosen 1 = 1 := by
    by_contra hne
    have hs := List.Sublist.of_cons_of_ne hne chosenSublist
    exact criterion.2.2.1
      (build _ word.tail chosen (by decide) rfl chosenIncreasing hs)
  have chosenLast : chosen 4 = last := by
    by_contra hne
    have hs : [chosen 4, chosen 2, chosen 3, chosen 1].Sublist
        (last :: interior.reverse ++ [1]) := by
      simpa [word] using chosenSublist.reverse
    have hs := List.Sublist.of_cons_of_ne hne hs
    have ht : ([1, 3, 2, 4].map chosen).Sublist (1 :: interior) := by
      simpa using hs.reverse
    exact criterion.2.2.2
      (build _ word.dropLast chosen (by decide) rfl chosenIncreasing (dropWord.symm ▸ ht))
  let left := chosen 3
  let right := chosen 2
  have selected : [left, right].Sublist interior := by
    have hs : [chosen 3, chosen 2, last].Sublist (interior ++ [last]) := by
      apply (List.cons_sublist_cons (a := 1)).mp
      simpa [word, chosenFirst, chosenLast] using chosenSublist
    have hr : (last :: [chosen 2, chosen 3]).Sublist (last :: interior.reverse) := by
      simpa using hs.reverse
    simpa [left, right] using (List.cons_sublist_cons.mp hr).reverse
  have descending : right < left := chosen23
  have leftBound : 1 < left ∧ left < last := by dsimp [left]; omega
  have rightBound : 1 < right ∧ right < last := by dsimp [right]; omega
  have noMHM (lower upper middle : ℕ) (hs : [lower, upper, middle].Sublist interior)
      (hl : 1 < lower ∧ lower < last) (hu : last < upper) (hm : middle < lower) :
      False := by
    have hmPositive := (values middle).mp (hs.subset (by simp))
    let witness := fun rank : ℕ => if rank = 1 then middle else if rank = 2 then lower
      else if rank = 3 then last else upper
    apply criterion.2.1 2 (by omega) (by omega)
    change Occurs [2, 4, 1, 3] word
    refine build _ word witness (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
    · simpa [word, witness] using (hs.append (List.Sublist.refl [last])).cons 1
  have noMMH (upper : ℕ) (hs : [left, right, upper].Sublist interior)
      (hu : last < upper) : False := by
    let witness := fun rank : ℕ => if rank = 1 then 1 else if rank = 2 then right
      else if rank = 3 then left else upper
    apply criterion.2.2.2
    rw [dropWord]
    refine build [1, 3, 2, 4] (1 :: interior) witness (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [witness] <;> omega
    · simpa [witness] using hs.cons_cons 1
  have insertThird (container : List ℕ) (extra : ℕ) (hs : [left, right].Sublist container)
      (hm : extra ∈ container) (hneLeft : extra ≠ left) (hneRight : extra ≠ right) :
      [extra, left, right].Sublist container ∨ [left, extra, right].Sublist container ∨
        [left, right, extra].Sublist container := by
    have pairOrder (container : List ℕ) (one two : ℕ)
        (h1 : one ∈ container) (h2 : two ∈ container) (hne : one ≠ two) :
        [one, two].Sublist container ∨ [two, one].Sublist container := by
      induction container with
      | nil => simp at h1
      | cons head tail ih =>
        by_cases he : head = one
        · subst head
          exact Or.inl ((List.singleton_sublist.mpr
            ((List.mem_cons.mp h2).resolve_left (Ne.symm hne))).cons_cons one)
        · by_cases ht : head = two
          · subst head
            exact Or.inr ((List.singleton_sublist.mpr
              ((List.mem_cons.mp h1).resolve_left hne)).cons_cons two)
          · rcases ih ((List.mem_cons.mp h1).resolve_left (Ne.symm he))
              ((List.mem_cons.mp h2).resolve_left (Ne.symm ht)) with hh | hh
            · exact Or.inl (hh.cons head)
            · exact Or.inr (hh.cons head)
    induction container with
    | nil => simp at hs
    | cons head tail ih =>
      by_cases he : head = extra
      · subst head
        exact Or.inl ((List.Sublist.of_cons_of_ne (Ne.symm hneLeft) hs).cons_cons extra)
      · by_cases hl : head = left
        · subst head
          have hm := (List.mem_cons.mp hm).resolve_left hneLeft
          have hr := List.singleton_sublist.mp (List.cons_sublist_cons.mp hs)
          rcases pairOrder tail extra right hm hr hneRight with hh | hh
          · exact Or.inr (Or.inl (hh.cons_cons left))
          · exact Or.inr (Or.inr (hh.cons_cons left))
        · rcases ih (List.Sublist.of_cons_of_ne (Ne.symm hl) hs)
            ((List.mem_cons.mp hm).resolve_left (Ne.symm he)) with hh | hh | hh
          · exact Or.inl (hh.cons head)
          · exact Or.inr (Or.inl (hh.cons head))
          · exact Or.inr (Or.inr (hh.cons head))
  have upperBefore (upper : ℕ) (hu : upper ∈ interior) (hb : last < upper) :
      [upper, left, right].Sublist interior := by
    rcases insertThird interior upper selected hu (by omega) (by omega) with hs | hs | hs
    · exact hs
    · exact False.elim (noMHM left upper right hs leftBound hb descending)
    · exact False.elim (noMMH upper hs hb)
  have chain (container : List ℕ) (one pivot two : ℕ) (hn : container.Nodup)
      (hl : [one, pivot].Sublist container) (hr : [pivot, two].Sublist container) :
      [one, pivot, two].Sublist container := by
    induction container with
    | nil => simp at hl
    | cons head tail ih =>
      have ht := (List.nodup_cons.mp hn).2
      by_cases hh : head = one
      · subst head
        have hne : pivot ≠ one := by
          have hh := hn.sublist hl
          exact Ne.symm (by simpa using (List.nodup_cons.mp hh).1)
        exact (List.Sublist.of_cons_of_ne hne hr).cons_cons one
      · have hl := List.Sublist.of_cons_of_ne (Ne.symm hh) hl
        have hne : pivot ≠ head := by
          intro heq
          exact (List.nodup_cons.mp hn).1 (heq ▸ hl.subset (by simp))
        exact (ih ht hl (List.Sublist.of_cons_of_ne hne hr)).cons head
  have middle132 : ¬ Occurs [1, 3, 2] (interior.filter isMiddle) := by
    rintro ⟨witness, hi, _, hs, _⟩
    have h1 : witness 1 < witness 2 := by simpa using hi 1 (by omega) (by decide)
    have h2 : witness 2 < witness 3 := by simpa using hi 2 (by omega) (by decide)
    have hb : witness 3 < last := of_decide_eq_true (List.mem_filter.mp
      (hs.subset (by simp : witness 3 ∈ [1, 3, 2].map witness))).2
    let lifted := fun rank : ℕ => if rank = 4 then last else witness rank
    apply criterion.2.2.1
    refine build [1, 3, 2, 4] (interior ++ [last]) lifted (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [lifted] <;> omega
    · simpa [lifted] using
        (hs.trans (List.filter_sublist (p := isMiddle))).append (List.Sublist.refl [last])
  have noMiddleUpper (middle upper : ℕ) (hs : [middle, upper].Sublist interior)
      (hm : middle < last) (hu : last < upper) : False := by
    have hc := upperBefore upper (hs.subset (by simp)) hu
    have hr : [upper, right].Sublist interior :=
      (((List.sublist_cons_self left [right]).cons_cons upper).trans hc)
    have triple := chain interior middle upper right interiorNodup hs hr
    have hn : middle ≠ right := fun heq => (List.nodup_cons.mp
      (interiorNodup.sublist triple)).1 (by simp [heq])
    by_cases hlt : right < middle
    · exact noMHM middle upper right triple
        ⟨by have := (values middle).mp (hs.subset (by simp)); omega, hm⟩ hu hlt
    · have hx : [upper, left].Sublist interior :=
        (List.sublist_append_left _ [right]).trans hc
      have hmx : [middle, left].Sublist interior :=
        (((List.sublist_cons_self upper [left]).cons_cons middle).trans
          (chain interior middle upper left interiorNodup hs hx))
      have mt := chain interior middle left right interiorNodup hmx selected
      have filtered : [middle, left, right].Sublist (interior.filter isMiddle) := by
        have hh := mt.filter isMiddle
        simpa [isMiddle, hm, leftBound.2, rightBound.2] using hh
      apply middle132
      let witness := fun rank : ℕ => if rank = 1 then middle else if rank = 2 then right
        else left
      refine ⟨witness, ?_, ?_, ?_, by simp⟩
      · intro rank hlo hhi
        simp only [letters, List.foldr_cons, List.foldr_nil] at hhi
        have hh : rank = 1 ∨ rank = 2 := by omega
        rcases hh with rfl | rfl <;> simp [witness] <;> omega
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by
          simp [letters] at hhi; omega
        rcases hh with rfl | rfl | rfl <;>
          simp [witness, List.mem_filter, isMiddle, hm, leftBound.2, rightBound.2,
            mt.subset (by simp : middle ∈ _), mt.subset (by simp : right ∈ _),
            mt.subset (by simp : left ∈ _)]
      · simpa [witness] using filtered
  have separated (container : List ℕ) (hs : container.Sublist interior) :
      container = container.filter isUpper ++ container.filter isMiddle := by
    induction container with
    | nil => simp
    | cons head tail ih =>
      have ht := ih ((List.sublist_cons_self head _).trans hs)
      have hn := (values head).mp (hs.subset (by simp))
      by_cases hu : last < head
      · simpa [isUpper, isMiddle, hu, show ¬ head < last by omega] using
          congrArg (List.cons head) ht
      · have hm : head < last := by omega
        have noUpper : tail.filter isUpper = [] := List.filter_eq_nil_iff.mpr (by
          intro value hv
          simp only [isUpper]
          simp only [decide_eq_true_eq]
          exact fun hh => noMiddleUpper head value
            (((List.singleton_sublist.mpr hv).cons_cons head).trans hs) hm hh)
        simpa [isUpper, isMiddle, hu, hm, noUpper] using congrArg (List.cons head) ht
  refine ⟨by omega, separated interior (List.Sublist.refl _), ?_, ?_, ?_, ?_, middle132,
    ?_, ?_⟩
  · apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [List.mem_filter, values]
    simp only [decide_eq_true_eq, List.mem_range'_1]
    omega
  · apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [List.mem_filter, values]
    simp only [decide_eq_true_eq, List.mem_range'_1]
    omega
  · rintro ⟨witness, hi, _, hs, _⟩
    have h1 : witness 1 < witness 2 := by simpa using hi 1 (by omega) (by decide)
    have h2 : witness 2 < witness 3 := by simpa using hi 2 (by omega) (by decide)
    have hv : witness 1 ∈ interior :=
      List.filter_sublist.subset (hs.subset (by simp : witness 1 ∈ [2, 1, 3].map witness))
    have hb := (values _).mp hv
    let lifted := fun rank : ℕ => if rank = 1 then 1 else witness (rank - 1)
    apply criterion.2.2.2
    rw [dropWord]
    refine build [1, 3, 2, 4] (1 :: interior) lifted (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [lifted] <;> omega
    · simpa [lifted] using
        (hs.trans (List.filter_sublist (p := isUpper))).cons_cons 1
  · rintro ⟨witness, hi, hm, hs, _⟩
    apply criterion.2.1 3 (by omega) (by omega)
    change Occurs [4, 1, 3, 2] word
    have hsub : (interior.filter isUpper).Sublist word :=
      List.filter_sublist.trans ((List.sublist_append_left _ _).cons 1)
    exact ⟨witness, hi, fun rank hlo hhi => hsub.subset (hm rank hlo hhi),
      hs.trans hsub, by simp⟩
  · rintro ⟨witness, hi, _, hs, _⟩
    have h1 : witness 1 < witness 2 := by simpa using hi 1 (by omega) (by decide)
    have h2 : witness 2 < witness 3 := by simpa using hi 2 (by omega) (by decide)
    have hv : witness 1 ∈ interior :=
      List.filter_sublist.subset (hs.subset (by simp : witness 1 ∈ [2, 1, 3].map witness))
    have hb := (values _).mp hv
    let lifted := fun rank : ℕ => if rank = 1 then 1 else witness (rank - 1)
    apply criterion.2.2.2
    rw [dropWord]
    refine build [1, 3, 2, 4] (1 :: interior) lifted (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [lifted] <;> omega
    · simpa [lifted] using
        (hs.trans (List.filter_sublist (p := isMiddle))).cons_cons 1
  · intro hsorted
    have hh := hsorted.sublist (selected.filter isMiddle)
    have hh : left < right := by
      simpa [isMiddle, leftBound.2, rightBound.2] using hh
    omega

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSeparated
