/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescending
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescending
   mirror-E: none(waiver:descending-upper-endpoint-slices)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Consecutive endpoints isolate a reversed A-class above an increasing lower block. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceEnumeration
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDescending

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular

theorem descending_consecutive_endpoint_normal_form (size first : ℕ) (interior : List ℕ)
    (hsize : 4 ≤ size) (hfirst : 1 ≤ first)
    (hperm : (first :: interior ++ [first + 1]).Perm (List.range' 1 size))
    (hcuts : ∀ cut < size,
      Occurs [1, 4, 3, 2] ((first :: interior ++ [first + 1]).rotate cut) ↔ cut = 0) :
    first + 3 ≤ size ∧
      interior = interior.filter (fun value => decide (first + 1 < value)) ++
        List.range' 1 (first - 1) ∧
      (interior.filter (fun value => decide (first + 1 < value))).Perm
        (List.range' (first + 2) (size - first - 1)) ∧
      ¬ Occurs [3, 2, 1] (interior.filter (fun value => decide (first + 1 < value))) ∧
      ¬ Occurs [2, 1, 4, 3] (interior.filter (fun value => decide (first + 1 < value))) ∧
      ¬ (interior.filter (fun value => decide (first + 1 < value))).Pairwise (· < ·) := by
  classical
  let word := first :: interior ++ [first + 1]
  let isUpper := fun value : ℕ => decide (first + 1 < value)
  let isLower := fun value : ℕ => decide (value < first)
  have criterion := (unique_bad_cut_iff size hsize [1, 4, 3, 2] word
    (by decide) hperm).mp hcuts
  have dropWord : word.dropLast = first :: interior := by
    change ((first :: interior) ++ [first + 1]).dropLast = _
    rw [List.dropLast_append_cons]; simp
  have wordNodup := hperm.nodup_iff.mpr List.nodup_range'
  have interiorNodup := (List.nodup_cons.mp wordNodup).2.sublist
    (List.sublist_append_left interior [first + 1])
  have notFirst : first ∉ interior := fun hv =>
    (List.nodup_cons.mp wordNodup).1 (List.mem_append_left _ hv)
  have notLast : first + 1 ∉ interior := fun hv =>
    (List.nodup_append.mp (List.nodup_cons.mp wordNodup).2).2.2
      (first + 1) hv (first + 1) (by simp) rfl
  have bounds (value : ℕ) (hv : value ∈ word) : 1 ≤ value ∧ value ≤ size := by
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hv)
    omega
  have colors (value : ℕ) (hv : value ∈ interior) :
      first + 1 < value ∨ value < first := by
    have hne : value ≠ first := fun he => notFirst (he ▸ hv)
    have hne' : value ≠ first + 1 := fun he => notLast (he ▸ hv)
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
      (heq : ([1, 4, 3, 2] : List ℕ).rotate shift = pattern) : ¬ Occurs pattern word := by
    simpa only [heq] using criterion.2.1 shift hs hb
  have noLowerUpper (lower upper : ℕ) (hs : [lower, upper].Sublist interior)
      (hl : lower < first) (hu : first + 1 < upper) : False := by
    let chosen := fun rank : ℕ => if rank = 1 then lower else if rank = 2 then first
      else if rank = 3 then first + 1 else upper
    apply noRotated [2, 1, 4, 3] 3 (by omega) (by omega) (by decide)
    refine build _ word chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
    · simpa [word, chosen] using (hs.append (List.Sublist.refl [first + 1])).cons_cons first
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
      else if rank = 3 then first else first + 1
    apply noRotated [3, 2, 1, 4] 2 (by omega) (by omega) (by decide)
    refine build _ word chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> dsimp [isLower] at * <;> omega
    · simpa [word, chosen] using (hs.append (List.Sublist.refl [first + 1])).cons_cons first
  have separated (selected : List ℕ) (hs : selected.Sublist interior) :
      selected = selected.filter isUpper ++ selected.filter isLower := by
    induction selected with
    | nil => simp
    | cons head tail ih =>
      have hhead := hs.subset (by simp : head ∈ head :: tail)
      have htail := (List.sublist_cons_self head tail).trans hs
      rcases colors head hhead with hu | hl
      · simpa [isUpper, isLower, hu, show ¬ head < first by omega] using
          congrArg (head :: ·) (ih htail)
      · have allLower : ∀ value ∈ tail, value < first := by
          intro value hv
          rcases colors value (htail.subset hv) with hu | hv
          · exact False.elim (noLowerUpper head value
              (((List.singleton_sublist.mpr hv).cons_cons head).trans hs) hl hu)
          · exact hv
        have keep : tail.filter isLower = tail := List.filter_eq_self.mpr
          (by intro value hv; simp [isLower, allLower value hv])
        have erase : tail.filter isUpper = [] := List.filter_eq_nil_iff.mpr
          (by intro value hv; simp [isUpper, show ¬ first + 1 < value by
            have := allLower value hv; omega])
        simp [isUpper, isLower, hl, show ¬ first + 1 < head by omega, keep, erase]
  have lowerPerm : (interior.filter isLower).Perm (List.range' 1 (first - 1)) := by
    apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [List.mem_filter, isLower, decide_eq_true_eq, List.mem_range'_1]
    constructor
    · rintro ⟨hv, hh⟩
      have hb := bounds value (by simp [word, hv])
      omega
    · intro hh
      have hv : value ∈ word := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr ⟨by omega, by
          have := bounds (first + 1) (by simp [word]); omega⟩)
      have hv : value ∈ interior := by
        simpa [word, show value ≠ first by omega, show value ≠ first + 1 by omega] using hv
      exact ⟨hv, by omega⟩
  have lowerEq := lowerPerm.eq_of_pairwise (by intro left right hl hr; omega)
    lowerIncreasing (List.pairwise_lt_range' _ (by omega))
  have upperPerm : (interior.filter isUpper).Perm
      (List.range' (first + 2) (size - first - 1)) := by
    apply (List.perm_ext_iff_of_nodup
      (interiorNodup.sublist List.filter_sublist) List.nodup_range').mpr
    intro value
    simp only [List.mem_filter, isUpper, decide_eq_true_eq, List.mem_range'_1]
    constructor
    · rintro ⟨hv, hh⟩
      have hb := bounds value (by simp [word, hv])
      omega
    · intro hh
      have hv : value ∈ word := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hv : value ∈ interior := by
        simpa [word, show value ≠ first by omega, show value ≠ first + 1 by omega] using hv
      exact ⟨hv, by omega⟩
  obtain ⟨chosen, hi, _, selected, _⟩ := criterion.1
  have chosen12 : chosen 1 < chosen 2 := by simpa using hi 1 (by omega) (by decide)
  have chosen23 : chosen 2 < chosen 3 := by simpa using hi 2 (by omega) (by decide)
  have chosen34 : chosen 3 < chosen 4 := by simpa using hi 3 (by omega) (by decide)
  have chosenFirst : chosen 1 = first := by
    by_contra hne
    exact criterion.2.2.1
      (build _ word.tail chosen (by decide) rfl hi (List.Sublist.of_cons_of_ne hne selected))
  have chosenLast : chosen 2 = first + 1 := by
    by_contra hne
    have hs : [chosen 2, chosen 3, chosen 4, chosen 1].Sublist
        ((first + 1) :: interior.reverse ++ [first]) := by
      simpa [word] using selected.reverse
    have hs := List.Sublist.of_cons_of_ne hne hs
    have ht : ([1, 4, 3, 2].map chosen).Sublist (first :: interior) := by
      simpa using hs.reverse
    exact criterion.2.2.2
      (build _ word.dropLast chosen (by decide) rfl hi (dropWord.symm ▸ ht))
  have pair : [chosen 4, chosen 3].Sublist interior := by
    have hs : [chosen 4, chosen 3, first + 1].Sublist (interior ++ [first + 1]) := by
      apply (List.cons_sublist_cons (a := first)).mp
      simpa [word, chosenFirst, chosenLast] using selected
    have hr : ((first + 1) :: [chosen 3, chosen 4]).Sublist
        ((first + 1) :: interior.reverse) := by simpa using hs.reverse
    simpa using (List.cons_sublist_cons.mp hr).reverse
  have pairUpper : [chosen 4, chosen 3].Sublist (interior.filter isUpper) := by
    have hs := pair.filter isUpper
    simpa [isUpper, show first + 1 < chosen 4 by omega,
      show first + 1 < chosen 3 by omega] using hs
  refine ⟨?_, ?_, upperPerm, ?_, ?_, ?_⟩
  · have hb := bounds (chosen 4) (selected.subset (by simp))
    omega
  · simpa only [lowerEq] using separated interior (List.Sublist.refl _)
  · rintro ⟨witness, hg, _, hs, _⟩
    have h1 : witness 1 < witness 2 := by simpa using hg 1 (by omega) (by decide)
    have h2 : witness 2 < witness 3 := by simpa using hg 2 (by omega) (by decide)
    have hb := of_decide_eq_true (List.mem_filter.mp
      (hs.subset (by simp : witness 1 ∈ [3, 2, 1].map witness))).2
    let chosen := fun rank : ℕ => if rank = 1 then first else witness (rank - 1)
    apply criterion.2.2.2
    rw [dropWord]
    refine build _ (first :: interior) chosen (by decide) rfl ?_ ?_
    · intro rank hlo hhi
      have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> dsimp [isUpper] at * <;> omega
    · simpa [chosen] using (hs.trans (List.filter_sublist (p := isUpper))).cons_cons first
  · rintro ⟨witness, hg, _, hs, _⟩
    apply noRotated [2, 1, 4, 3] 3 (by omega) (by omega) (by decide)
    refine build _ word witness (by decide) rfl hg ?_
    exact ((hs.trans (List.filter_sublist (p := isUpper))).trans
      (List.sublist_append_left _ _)).cons first
  · intro hsorted
    have hh := List.pairwise_iff_forall_sublist.mp hsorted pairUpper
    omega

set_option maxHeartbeats 1500000 in
set_option synthInstance.maxSize 2048 in
theorem descending_consecutive_endpoint_count (size first : ℕ)
    (hfirst : 1 ≤ first) (hbound : first + 3 ≤ size) :
    ({word : List ℕ | word.Perm (List.range' 1 size) ∧
      word.head? = some first ∧ word.getLast? = some (first + 1) ∧
      ∀ cut < size, Occurs [1, 4, 3, 2] (word.rotate cut) ↔ cut = 0} :
      Set (List ℕ)).ncard =
        2 ^ (size - first) - 2 * (size - first - 1) - 2 - (size - first).choose 3 := by
  have construction (upper : List ℕ)
      (hupper : upper.Perm (List.range' (first + 2) (size - first - 1)))
      (h321 : ¬ Occurs [3, 2, 1] upper) (h2143 : ¬ Occurs [2, 1, 4, 3] upper)
      (hdescent : ¬ upper.Pairwise (· < ·)) :
      (first :: upper ++ List.range' 1 (first - 1) ++ [first + 1]).Perm
          (List.range' 1 size) ∧
        ∀ cut < size, Occurs [1, 4, 3, 2]
          ((first :: upper ++ List.range' 1 (first - 1) ++ [first + 1]).rotate cut) ↔
            cut = 0 := by
    let lower := List.range' 1 (first - 1)
    let word := first :: upper ++ lower ++ [first + 1]
    let bucket := fun value : ℕ => if value < first then 0 else if value = first then 1
      else if value = first + 1 then 2 else 3
    have bucketBound (value : ℕ) : bucket value < 4 := by
      dsimp [bucket]; split_ifs <;> omega
    let color := fun value : ℕ => (⟨bucket value, bucketBound value⟩ : Fin 4)
    let slot : Fin 4 → ℕ := fun shade => if shade = 0 then 2 else if shade = 1 then 0
      else if shade = 2 then 3 else 1
    let position := fun value : ℕ => slot (color value)
    have upperBounds (value : ℕ) (hv : value ∈ upper) :
        first + 1 < value ∧ value ≤ size := by
      have hh := List.mem_range'_1.mp (hupper.mem_iff.mp hv)
      omega
    have lowerBounds (value : ℕ) (hv : value ∈ lower) : 1 ≤ value ∧ value < first := by
      have hh := List.mem_range'_1.mp hv
      omega
    have firstColor : color first = 1 := by simp [color, bucket]
    have lastColor : color (first + 1) = 2 := by
      simp [color, bucket, show ¬ first + 1 < first by omega]
    have upperColor (value : ℕ) (hv : value ∈ upper) : color value = 3 := by
      have hh := upperBounds value hv
      simp [color, bucket, show ¬ value < first by omega, show value ≠ first by omega,
        show value ≠ first + 1 by omega]
    have lowerColor (value : ℕ) (hv : value ∈ lower) : color value = 0 := by
      simp [color, bucket, (lowerBounds value hv).2]
    have colorMono (left right : ℕ) (hh : left ≤ right) : color left ≤ color right := by
      change bucket left ≤ bucket right
      dsimp [bucket]; split_ifs <;> omega
    have wordNodup : word.Nodup := by
      have hu := hupper.nodup_iff.mpr List.nodup_range'
      have hl : lower.Nodup := List.nodup_range'
      have hul : (upper ++ lower).Nodup := List.nodup_append.mpr ⟨hu, hl, by
        intro left hh right ht he
        have := upperBounds left hh
        have := lowerBounds right ht
        omega⟩
      have hule : (upper ++ lower ++ [first + 1]).Nodup := List.nodup_append.mpr
        ⟨hul, List.nodup_singleton _, by
          intro left hh right ht he
          simp only [List.mem_singleton] at ht
          rcases List.mem_append.mp hh with hh | hh
          · have := upperBounds left hh; omega
          · have := lowerBounds left hh; omega⟩
      apply List.nodup_cons.mpr
      refine ⟨?_, hule⟩
      intro hh
      change first ∈ upper ++ lower ++ [first + 1] at hh
      simp only [List.mem_append, List.mem_singleton] at hh
      rcases hh with (hh | hh) | hh
      · have := upperBounds first hh; omega
      · have := lowerBounds first hh; omega
      · omega
    have wordPerm : word.Perm (List.range' 1 size) := by
      apply (List.perm_ext_iff_of_nodup wordNodup List.nodup_range').mpr
      intro value
      simp only [word, lower, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
        hupper.mem_iff, List.mem_range'_1]
      omega
    have orderedWord : word.Pairwise (fun left right => position left ≤ position right) := by
      have upperOrdered : upper.Pairwise (fun left right => position left ≤ position right) :=
        List.pairwise_of_forall_mem_list (by
          intro left hl right hr
          simp [position, upperColor left hl, upperColor right hr])
      have lowerOrdered : lower.Pairwise (fun left right => position left ≤ position right) :=
        List.pairwise_of_forall_mem_list (by
          intro left hl right hr
          simp [position, lowerColor left hl, lowerColor right hr])
      simp only [word, List.cons_append, List.pairwise_cons, List.pairwise_append,
        List.pairwise_singleton, List.mem_append, List.mem_singleton, List.not_mem_nil,
        forall_false, or_imp, forall_and, forall_eq, and_true]
      and_intros
      all_goals first
        | exact upperOrdered
        | exact lowerOrdered
        | (intros; simp [position, firstColor, lastColor, upperColor, lowerColor, slot, *])
    have firstEndpoint (value : ℕ) (hc : color value = 1) : value = first := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he
      split_ifs at he <;> omega
    have lastEndpoint (value : ℕ) (hc : color value = 2) : value = first + 1 := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he
      split_ifs at he <;> omega
    have upperFilter : word.filter (fun value => decide (color value = 3)) = upper := by
      have hu : upper.filter (fun value => decide (color value = 3)) = upper :=
        List.filter_eq_self.mpr (by intro value hv; simp [upperColor value hv])
      have hl : lower.filter (fun value => decide (color value = 3)) = [] :=
        List.filter_eq_nil_iff.mpr (by intro value hv; simp [lowerColor value hv])
      simp [word, firstColor, lastColor, List.filter_append, hu, hl]
    have lowerFilter : word.filter (fun value => decide (color value = 0)) = lower := by
      have hu : upper.filter (fun value => decide (color value = 0)) = [] :=
        List.filter_eq_nil_iff.mpr (by intro value hv; simp [upperColor value hv])
      have hl : lower.filter (fun value => decide (color value = 0)) = lower :=
        List.filter_eq_self.mpr (by intro value hv; simp [lowerColor value hv])
      simp [word, firstColor, lastColor, List.filter_append, hu, hl]
    have finiteProfiles : ∀ low second third high : Fin 4,
        low ≤ second → second ≤ third → third ≤ high →
        (low = second → low ≠ 1 ∧ low ≠ 2) →
        (second = third → second ≠ 1 ∧ second ≠ 2) →
        (third = high → third ≠ 1 ∧ third ≠ 2) →
        ((slot low ≤ slot high ∧ slot high ≤ slot third ∧ slot third ≤ slot second) →
          ¬ (second = 0 ∧ third = 0) →
            (second = 3 ∧ third = 3 ∧ high = 3) ∨ (low = 1 ∧ second = 2)) ∧
        ((slot high ≤ slot third ∧ slot third ≤ slot second ∧ slot second ≤ slot low) →
          ¬ (low = 0 ∧ second = 0) → second = 3 ∧ third = 3 ∧ high = 3) ∧
        ((slot third ≤ slot second ∧ slot second ≤ slot low ∧ slot low ≤ slot high) →
          ¬ (low = 0 ∧ second = 0) → low = 3 ∧ second = 3 ∧ third = 3 ∧ high = 3) ∧
        ((slot second ≤ slot low ∧ slot low ≤ slot high ∧ slot high ≤ slot third) →
          ¬ (low = 0 ∧ second = 0) → low = 3 ∧ second = 3 ∧ third = 3 ∧ high = 3) := by
      decide
    have build (pattern container : List ℕ) (width : ℕ) (chosen : ℕ → ℕ)
        (hp : pattern.Perm (List.range' 1 width)) (hl : letters pattern = width)
        (hi : ∀ rank, 1 ≤ rank → rank < width → chosen rank < chosen (rank + 1))
        (hs : (pattern.map chosen).Sublist container) : Occurs pattern container := by
      refine ⟨chosen, ?_, ?_, hs, by simp⟩
      · simpa only [hl] using hi
      · intro rank hlo hhi
        rw [hl] at hhi
        exact hs.subset (List.mem_map_of_mem
          (hp.mem_iff.mpr (List.mem_range'_1.mpr (by omega))))
    have profile (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (hp : pattern.Perm [1, 2, 3, 4])
        (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1)) := by
      have singleton (left right : ℕ) (hl : left ∈ pattern) (hr : right ∈ pattern)
          (hh : chosen left < chosen right) : color (chosen left) = color (chosen right) →
            color (chosen left) ≠ 1 ∧ color (chosen left) ≠ 2 := by
        intro he
        constructor
        · intro hc
          have := firstEndpoint _ hc
          have := firstEndpoint _ (he.symm.trans hc)
          omega
        · intro hc
          have := lastEndpoint _ hc
          have := lastEndpoint _ (he.symm.trans hc)
          omega
      exact finiteProfiles (color (chosen 1)) (color (chosen 2))
        (color (chosen 3)) (color (chosen 4))
        (colorMono _ _ (hi 1 (by omega) (by omega)).le)
        (colorMono _ _ (hi 2 (by omega) (by omega)).le)
        (colorMono _ _ (hi 3 (by omega) (by omega)).le)
        (singleton 1 2 (hp.mem_iff.mpr (by simp)) (hp.mem_iff.mpr (by simp))
          (hi 1 (by omega) (by omega)))
        (singleton 2 3 (hp.mem_iff.mpr (by simp)) (hp.mem_iff.mpr (by simp))
          (hi 2 (by omega) (by omega)))
        (singleton 3 4 (hp.mem_iff.mpr (by simp)) (hp.mem_iff.mpr (by simp))
          (hi 3 (by omega) (by omega)))
    have edge (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (left right : ℕ) (hr : [left, right].Sublist pattern) :
        position (chosen left) ≤ position (chosen right) :=
      List.pairwise_iff_forall_sublist.mp orderedWord
        ((hr.map chosen).trans (hs.trans hcontainer))
    have project (pattern container ranks block : List ℕ) (chosen : ℕ → ℕ) (shade : Fin 4)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (hr : ranks.Sublist pattern) (hc : ∀ rank ∈ ranks, color (chosen rank) = shade)
        (hf : word.filter (fun value => decide (color value = shade)) = block) :
        (ranks.map chosen).Sublist block := by
      have hh := ((hr.map chosen).trans (hs.trans hcontainer)).filter
        (fun value => decide (color value = shade))
      have he : (ranks.map chosen).filter (fun value => decide (color value = shade)) =
          ranks.map chosen := List.filter_eq_self.mpr (by
        intro value hv
        obtain ⟨rank, hr, rfl⟩ := List.mem_map.mp hv
        simp [hc rank hr])
      rwa [he, hf] at hh
    have noLowerDescent (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (left right : ℕ) (hr : [left, right].Sublist pattern) (hh : chosen right < chosen left) :
        ¬ (color (chosen right) = 0 ∧ color (chosen left) = 0) := by
      rintro ⟨hc, hd⟩
      have hl := project _ _ [left, right] lower chosen 0 hcontainer hs hr
        (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
            rcases hr with rfl | rfl <;> assumption) lowerFilter
      have hi := List.pairwise_iff_forall_sublist.mp
        (List.pairwise_lt_range' 1 (by omega) : lower.Pairwise (· < ·)) hl
      omega
    have upperTriple (pattern container : List ℕ) (chosen : ℕ → ℕ) (offset : ℕ)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (hr : [offset + 3, offset + 2, offset + 1].Sublist pattern)
        (hc : ∀ rank ∈ [offset + 3, offset + 2, offset + 1], color (chosen rank) = 3)
        (hi : chosen (offset + 1) < chosen (offset + 2) ∧
          chosen (offset + 2) < chosen (offset + 3)) : False := by
      apply h321
      refine build _ upper 3 (fun rank => chosen (offset + rank)) (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 := by omega
        rcases hh with rfl | rfl
        · exact hi.1
        · exact hi.2
      · simpa using project _ _ _ upper chosen 3 hcontainer hs hr hc upperFilter
    have forcedEndpoints (container : List ℕ) (hcontainer : container.Sublist word)
        (ho : Occurs [1, 4, 3, 2] container) : first ∈ container ∧ first + 1 ∈ container := by
      obtain ⟨chosen, hi, _, hs, _⟩ := ho
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa [letters] using hi
      have hp := (profile _ _ chosen hcontainer hs (by decide) hi').1
        ⟨edge _ _ _ hcontainer hs 1 4 (by decide),
          edge _ _ _ hcontainer hs 4 3 (by decide),
          edge _ _ _ hcontainer hs 3 2 (by decide)⟩
        (noLowerDescent _ _ _ hcontainer hs 3 2 (by decide) (hi' 2 (by omega) (by omega)))
      rcases hp with hu | he
      · rcases hu with ⟨hc2, hc3, hc4⟩
        exact False.elim (upperTriple _ _ chosen 1 hcontainer hs (by decide)
          (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
              rcases hr with rfl | rfl | rfl <;> assumption)
          ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩)
      · have hf := firstEndpoint _ he.1
        have hl := lastEndpoint _ he.2
        exact ⟨hf ▸ hs.subset (by simp), hl ▸ hs.subset (by simp)⟩
    have no4321 : ¬ Occurs [4, 3, 2, 1] word := by
      rintro ⟨chosen, hi, _, hs, _⟩
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa [letters] using hi
      have hp := (profile _ _ chosen (List.Sublist.refl word) hs (by decide) hi').2.1
        ⟨edge _ _ _ (List.Sublist.refl _) hs 4 3 (by decide),
          edge _ _ _ (List.Sublist.refl _) hs 3 2 (by decide),
          edge _ _ _ (List.Sublist.refl _) hs 2 1 (by decide)⟩
        (noLowerDescent _ _ _ (List.Sublist.refl _) hs 2 1 (by decide)
          (hi' 1 (by omega) (by omega)))
      rcases hp with ⟨hc2, hc3, hc4⟩
      exact upperTriple _ _ chosen 1 (List.Sublist.refl _) hs (by decide)
        (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
            rcases hr with rfl | rfl | rfl <;> assumption)
        ⟨hi' 2 (by omega) (by omega), hi' 3 (by omega) (by omega)⟩
    have no3214 : ¬ Occurs [3, 2, 1, 4] word := by
      rintro ⟨chosen, hi, _, hs, _⟩
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa [letters] using hi
      have hp := (profile _ _ chosen (List.Sublist.refl word) hs (by decide) hi').2.2.1
        ⟨edge _ _ _ (List.Sublist.refl _) hs 3 2 (by decide),
          edge _ _ _ (List.Sublist.refl _) hs 2 1 (by decide),
          edge _ _ _ (List.Sublist.refl _) hs 1 4 (by decide)⟩
        (noLowerDescent _ _ _ (List.Sublist.refl _) hs 2 1 (by decide)
          (hi' 1 (by omega) (by omega)))
      rcases hp with ⟨hc1, hc2, hc3, hc4⟩
      exact upperTriple _ _ chosen 0 (List.Sublist.refl _) hs (by decide)
        (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
            rcases hr with rfl | rfl | rfl <;> assumption)
        ⟨hi' 1 (by omega) (by omega), hi' 2 (by omega) (by omega)⟩
    have no2143 : ¬ Occurs [2, 1, 4, 3] word := by
      rintro ⟨chosen, hi, _, hs, _⟩
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa [letters] using hi
      have hp := (profile _ _ chosen (List.Sublist.refl word) hs (by decide) hi').2.2.2
        ⟨edge _ _ _ (List.Sublist.refl _) hs 2 1 (by decide),
          edge _ _ _ (List.Sublist.refl _) hs 1 4 (by decide),
          edge _ _ _ (List.Sublist.refl _) hs 4 3 (by decide)⟩
        (noLowerDescent _ _ _ (List.Sublist.refl _) hs 2 1 (by decide)
          (hi' 1 (by omega) (by omega)))
      rcases hp with ⟨hc1, hc2, hc3, hc4⟩
      apply h2143
      apply build _ upper 4 chosen (by decide) rfl hi'
      exact project _ _ [2, 1, 4, 3] upper chosen 3 (List.Sublist.refl _) hs (by rfl)
        (by intro rank hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr;
            rcases hr with rfl | rfl | rfl | rfl <;> assumption) upperFilter
    have hasDescent : ∃ left right, [left, right].Sublist upper ∧ ¬ left < right := by
      classical
      by_contra hnone
      apply hdescent
      apply List.pairwise_iff_forall_sublist.mpr
      intro left right hs
      by_contra hh
      exact hnone ⟨left, right, hs, hh⟩
    obtain ⟨left, right, pair, hnot⟩ := hasDescent
    have hne : left ≠ right := by
      simpa using (List.nodup_cons.mp ((hupper.nodup_iff.mpr List.nodup_range').sublist pair)).1
    have leftBounds := upperBounds left (pair.subset (by simp))
    have rightBounds := upperBounds right (pair.subset (by simp))
    have targetOccurs : Occurs [1, 4, 3, 2] word := by
      let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then first + 1
        else if rank = 3 then right else left
      refine build _ word 4 chosen (by decide) rfl ?_ ?_
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · simpa [word, chosen, List.append_assoc] using
          ((pair.trans (List.sublist_append_left upper lower)).append
            (List.Sublist.refl [first + 1])).cons_cons first
    refine ⟨wordPerm, (unique_bad_cut_iff size (by omega) _ word (by decide) wordPerm).mpr
      ⟨targetOccurs, ?_, ?_, ?_⟩⟩
    · intro shift hlo hhi
      have hh : shift = 1 ∨ shift = 2 ∨ shift = 3 := by omega
      rcases hh with rfl | rfl | rfl
      · exact no4321
      · exact no3214
      · exact no2143
    · intro ho
      have hf := (forcedEndpoints word.tail (List.tail_sublist _) ho).1
      exact (List.nodup_cons.mp wordNodup).1 hf
    · intro ho
      have hl := (forcedEndpoints word.dropLast (List.dropLast_sublist _) ho).2
      have hd : word.dropLast = first :: upper ++ lower := by
        change ((first :: upper ++ lower) ++ [first + 1]).dropLast = _
        rw [List.dropLast_append_cons]; simp
      rw [hd] at hl
      rcases List.mem_cons.mp hl with he | hh
      · omega
      · rcases List.mem_append.mp hh with hh | hh
        · have := upperBounds (first + 1) hh; omega
        · have := lowerBounds (first + 1) hh; omega
  classical
  let width := size - first - 1
  let parents := Fishburn.FishburnClassicalDefs.classicalAvoiders width
    [[1, 2, 3], [3, 4, 1, 2]]
  let decreasing := (List.range' 1 width).reverse
  let domain := parents \ {decreasing}
  let target : Set (List ℕ) := {word | word.Perm (List.range' 1 size) ∧
    word.head? = some first ∧ word.getLast? = some (first + 1) ∧
    ∀ cut < size, Occurs [1, 4, 3, 2] (word.rotate cut) ↔ cut = 0}
  let emit := fun parent : List ℕ => first ::
    parent.reverse.map (fun value => first + 1 + value) ++
      List.range' 1 (first - 1) ++ [first + 1]
  have membership (parent : List ℕ) : parent ∈ domain ↔
      parent.Perm (List.range' 1 width) ∧ ¬ Occurs [1, 2, 3] parent ∧
        ¬ Occurs [3, 4, 1, 2] parent ∧ ¬ parent.Pairwise (· > ·) := by
    have descent (hp : parent.Perm (List.range' 1 width)) :
        parent = decreasing ↔ parent.Pairwise (· > ·) := by
      have hd : decreasing.Pairwise (· > ·) :=
        List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
      exact ⟨fun he => he ▸ hd, fun hh =>
        (hp.trans (List.reverse_perm _).symm).eq_of_pairwise
          (by intro left right hl hr; omega) hh hd⟩
    simp only [domain, parents, Set.mem_sdiff, Fishburn.FishburnClassicalDefs.classicalAvoiders,
      Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hp, h123, h3412⟩, hne⟩
      exact ⟨hp, h123, h3412, fun hd => hne ((descent hp).mpr hd)⟩
    · rintro ⟨hp, h123, h3412, hd⟩
      exact ⟨⟨hp, h123, h3412⟩, fun he => hd ((descent hp).mp he)⟩
  have reverseOccurrence (pattern container : List ℕ)
      (hl : letters pattern.reverse = letters pattern) :
      Occurs pattern.reverse container.reverse ↔ Occurs pattern container := by
    constructor
    · rintro ⟨chosen, hi, hm, hs, _⟩
      refine ⟨chosen, by simpa only [hl] using hi,
        fun rank hlo hhi => List.mem_reverse.mp (hm rank hlo (hl.symm ▸ hhi)), ?_, by simp⟩
      simpa only [List.map_reverse, List.reverse_reverse] using hs.reverse
    · rintro ⟨chosen, hi, hm, hs, _⟩
      refine ⟨chosen, by simpa only [hl] using hi,
        fun rank hlo hhi => List.mem_reverse.mpr (hm rank hlo (hl ▸ hhi)), ?_, by simp⟩
      simpa only [List.map_reverse] using hs.reverse
  have shift (pattern parent : List ℕ) (hl : letters pattern = pattern.length) :
      Occurs pattern (parent.map (fun value => first + 1 + value)) ↔ Occurs pattern parent := by
    unfold Occurs
    rw [hl]
    exact ArcherCyclicPadovanPatterns.contains_map_iff _ _ _ (by
      intro left right hh; dsimp; omega)
  have upperPerm (parent : List ℕ) (hp : parent.Perm (List.range' 1 width)) :
      (parent.reverse.map (fun value => first + 1 + value)).Perm
        (List.range' (first + 2) width) := by
    have hr := List.map_add_range' (a := first + 1) 1 width 1
    simpa only [show first + 1 + 1 = first + 2 by omega, Nat.mul_one] using
      ((List.reverse_perm parent).trans hp).map (fun value => first + 1 + value) |>.trans
        (List.Perm.of_eq hr)
  have emitMember (parent : List ℕ) (hp : parent ∈ domain) : emit parent ∈ target := by
    obtain ⟨hperm, h123, h3412, hd⟩ := (membership parent).mp hp
    have hconstruction := construction _ (upperPerm parent hperm)
      (fun ho => h123 ((reverseOccurrence [1, 2, 3] parent rfl).mp
        ((shift _ _ rfl).mp ho)))
      (fun ho => h3412 ((reverseOccurrence [3, 4, 1, 2] parent rfl).mp
        ((shift _ _ rfl).mp ho)))
      (fun hi => hd (List.pairwise_reverse.mp (List.pairwise_map.mp hi |>.imp
        (by intro left right hh; omega))))
    refine ⟨hconstruction.1, by simp [emit], ?_, hconstruction.2⟩
    change ((first :: parent.reverse.map (fun value => first + 1 + value) ++
      List.range' 1 (first - 1)) ++ [first + 1]).getLast? = some (first + 1)
    rw [List.getLast?_append_cons]; rfl
  have emitInjective : Function.Injective emit := by
    intro left right he
    have hh := List.append_cancel_right (List.append_cancel_right (List.cons.inj he).2)
    have hh := List.map_injective_iff.mpr (show Function.Injective
      (fun value : ℕ => first + 1 + value) from by intro left right hh; dsimp at hh; omega) hh
    simpa using congrArg List.reverse hh
  have emitSurjective (word : List ℕ) (hw : word ∈ target) :
      ∃ parent ∈ domain, emit parent = word := by
    obtain ⟨front, hlast⟩ := List.getLast?_eq_some_iff.mp hw.2.2.1
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = first :: interior ++ [first + 1] := by
      cases front with
      | nil => have := hw.1.length_eq; simp [hlast] at this; omega
      | cons head interior =>
        have hh : head = first := by simpa [hlast] using hw.2.1
        exact ⟨interior, by simpa [hh] using hlast⟩
    obtain ⟨_, hnormal, huPerm, hu321, hu2143, huDescent⟩ :=
      descending_consecutive_endpoint_normal_form size first interior (by omega) hfirst
        (hsplit ▸ hw.1) (by simpa only [← hsplit] using hw.2.2.2)
    let upper := interior.filter (fun value => decide (first + 1 < value))
    change upper.Perm _ at huPerm
    change ¬ Occurs [3, 2, 1] upper at hu321
    change ¬ Occurs [2, 1, 4, 3] upper at hu2143
    change ¬ upper.Pairwise (· < ·) at huDescent
    let parent := (upper.map (fun value => value - (first + 1))).reverse
    have restore : parent.reverse.map (fun value => first + 1 + value) = upper := by
      rw [List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id upper]
      apply List.map_congr_left
      intro value hv
      have hh := List.mem_range'_1.mp (huPerm.mem_iff.mp hv)
      dsimp; omega
    have parentPerm : parent.Perm (List.range' 1 width) := by
      have hh := huPerm.map (fun value => value - (first + 1))
      have hp : (upper.map (fun value => value - (first + 1))).Perm (List.range' 1 width) := by
        simpa only [List.map_sub_range' (by omega : first + 1 ≤ first + 2)
          (size - first - 1), show first + 2 - (first + 1) = 1 by omega] using hh
      exact (List.reverse_perm _).trans hp
    refine ⟨parent, (membership parent).mpr ⟨parentPerm, ?_, ?_, ?_⟩, ?_⟩
    · intro ho
      exact hu321 (restore ▸ (shift _ _ rfl).mpr
        ((reverseOccurrence [1, 2, 3] parent rfl).mpr ho))
    · intro ho
      exact hu2143 (restore ▸ (shift _ _ rfl).mpr
        ((reverseOccurrence [3, 4, 1, 2] parent rfl).mpr ho))
    · intro hd
      exact huDescent (restore ▸ List.pairwise_map.mpr
        ((List.pairwise_reverse.mpr hd).imp (by intro left right hh; omega)))
    · simpa only [emit, restore, List.cons_append, List.append_assoc] using
        (hsplit.trans (congrArg (fun tail => first :: tail ++ [first + 1]) hnormal)).symm
  have hcard := Set.ncard_congr (s := domain) (t := target) (fun parent _ => emit parent)
    emitMember (fun left right hl hr he => emitInjective he) (by
      intro word hw
      obtain ⟨parent, hp, he⟩ := emitSurjective word hw
      exact ⟨parent, hp, he⟩)
  have decreasingMember : decreasing ∈ parents := by
    have hd : decreasing.Pairwise (· > ·) :=
      List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega))
    refine ⟨List.reverse_perm _, ?_⟩
    intro pattern hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rintro ⟨chosen, hi, _, hs, _⟩
      have hh := List.pairwise_iff_forall_sublist.mp hd
        (((by decide : [1, 2].Sublist [1, 2, 3]).map chosen).trans hs)
      have ht : chosen 1 < chosen 2 := by simpa using hi 1 (by omega) (by decide)
      omega
    · rintro ⟨chosen, hi, _, hs, _⟩
      have hh := List.pairwise_iff_forall_sublist.mp hd
        (((by decide : [3, 4].Sublist [3, 4, 1, 2]).map chosen).trans hs)
      have ht : chosen 3 < chosen 4 := by simpa using hi 3 (by omega) (by decide)
      omega
  have finiteParents : parents.Finite := by
    apply (List.finite_toSet (List.range' 1 width).permutations).subset
    intro parent hp
    exact List.mem_permutations.mpr hp.1
  have hminus := Set.ncard_sdiff_singleton_add_one decreasingMember finiteParents
  have henum := RotationAvoidanceEnumeration.ascending_count width
  change target.ncard = _
  change domain.ncard + 1 = parents.ncard at hminus
  change parents.ncard = _ at henum
  have hwidth : width + 1 = size - first := by dsimp [width]; omega
  rw [hwidth] at henum
  omega

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDescending
