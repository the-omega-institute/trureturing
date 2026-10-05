/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingSplit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDescendingSplit
   mirror-E: none(waiver:positive-middle-descending-slice-count)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The middle block marks the unique descent split of two increasing upper runs. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDescendingMiddle
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceOneAscent
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDescendingSplit

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular
open RotationAvoidanceDescendingMiddle

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxSize 4096 in
theorem descending_positive_middle_endpoint_count (size first last : ℕ)
    (hfirst : 1 ≤ first) (hmiddle : first + 1 < last) (hupper : last + 2 ≤ size) :
    ({word : List ℕ | word.Perm (List.range' 1 size) ∧
      word.head? = some first ∧ word.getLast? = some last ∧
      ∀ cut < size, Occurs [1, 4, 3, 2] (word.rotate cut) ↔ cut = 0} :
      Set (List ℕ)).ncard = 2 ^ (size - last) - (size - last) - 1 := by
  classical
  let middle := List.range' (first + 1) (last - first - 1)
  let lower := List.range' 1 (first - 1)
  have construction (before after : List ℕ)
      (hu : (before ++ after).Perm (List.range' (last + 1) (size - last)))
      (hb : before.Pairwise (· < ·)) (ha : after.Pairwise (· < ·))
      (hex : ∃ upper ∈ before, ∃ bottom ∈ after, bottom < upper) :
      let word := first :: before ++ middle ++ after ++ lower ++ [last]
      word.Perm (List.range' 1 size) ∧
        ∀ cut < size, Occurs [1, 4, 3, 2] (word.rotate cut) ↔ cut = 0 := by
    let word := first :: before ++ middle ++ after ++ lower ++ [last]
    have upperBounds (value : ℕ) (hv : value ∈ before ++ after) :
        last < value ∧ value ≤ size := by
      have hh := List.mem_range'_1.mp (hu.mem_iff.mp hv); omega
    have middleBounds (value : ℕ) (hv : value ∈ middle) :
        first < value ∧ value < last := by
      have hh := List.mem_range'_1.mp hv; omega
    have lowerBounds (value : ℕ) (hv : value ∈ lower) : 1 ≤ value ∧ value < first := by
      have hh := List.mem_range'_1.mp hv; omega
    have upperNodup := hu.nodup_iff.mpr List.nodup_range'
    have betweenNodup : (before ++ middle ++ after).Nodup := by
      have hba : (before ++ after ++ middle).Nodup := List.nodup_append.mpr
        ⟨upperNodup, List.nodup_range', by
          intro left hl right hr he
          have := upperBounds left hl; have := middleBounds right hr; omega⟩
      have hp : (before ++ middle ++ after).Perm (before ++ after ++ middle) := by
        simpa only [List.append_assoc] using
          (List.Perm.append_left before (List.perm_append_comm :
            (middle ++ after).Perm (after ++ middle)))
      exact hp.nodup_iff.mpr hba
    have interiorNodup : (before ++ middle ++ after ++ lower).Nodup :=
      List.nodup_append.mpr ⟨betweenNodup, List.nodup_range', by
        intro left hl right hr he
        have := lowerBounds right hr
        simp only [List.mem_append] at hl
        rcases hl with (hl | hl) | hl
        · have := upperBounds left (List.mem_append_left _ hl); omega
        · have := middleBounds left hl; omega
        · have := upperBounds left (List.mem_append_right _ hl); omega⟩
    have wordNodup : word.Nodup := by
      have ht : (before ++ middle ++ after ++ lower ++ [last]).Nodup :=
        List.nodup_append.mpr ⟨interiorNodup, List.nodup_singleton _, by
          intro left hl right hr he
          simp only [List.mem_singleton] at hr
          simp only [List.mem_append] at hl
          rcases hl with ((hl | hl) | hl) | hl
          · have := upperBounds left (List.mem_append_left _ hl); omega
          · have := middleBounds left hl; omega
          · have := upperBounds left (List.mem_append_right _ hl); omega
          · have := lowerBounds left hl; omega⟩
      refine List.nodup_cons.mpr ⟨?_, ht⟩
      intro hh
      change first ∈ before ++ middle ++ after ++ lower ++ [last] at hh
      simp only [List.mem_append, List.mem_singleton] at hh
      rcases hh with (((hh | hh) | hh) | hh) | hh
      · have := upperBounds first (List.mem_append_left _ hh); omega
      · have := middleBounds first hh; omega
      · have := upperBounds first (List.mem_append_right _ hh); omega
      · have := lowerBounds first hh; omega
      · omega
    have wordPerm : word.Perm (List.range' 1 size) := by
      apply (List.perm_ext_iff_of_nodup wordNodup List.nodup_range').mpr
      intro value
      have hh := hu.mem_iff (a := value)
      simp only [List.mem_append, List.mem_range'_1] at hh
      simp only [word, middle, lower, List.mem_cons, List.mem_append, List.mem_singleton,
        List.mem_range'_1, List.not_mem_nil, or_false]
      constructor
      · intro hv
        rcases hv with ((((hv | hv) | hv) | hv) | hv) | hv
        · omega
        · have := upperBounds value (List.mem_append_left _ hv); omega
        · omega
        · have := upperBounds value (List.mem_append_right _ hv); omega
        · omega
        · omega
      · intro hv
        by_cases hl : value < first
        · exact Or.inl (Or.inr (by omega))
        · by_cases hf : value = first
          · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hf))))
          · by_cases hm : value < last
            · exact Or.inl (Or.inl (Or.inl (Or.inr (by omega))))
            · by_cases he : value = last
              · exact Or.inr he
              · rcases hh.mpr (by omega) with hb | ha
                · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hb))))
                · exact Or.inl (Or.inl (Or.inr ha))
    let bucket := fun value : ℕ => if value < first then 0 else if value = first then 1
      else if value < last then 2 else if value = last then 3
      else if value ∈ before then 4 else 5
    have bucketBound (value : ℕ) : bucket value < 6 := by
      dsimp [bucket]; split_ifs <;> omega
    let color := fun value : ℕ => (⟨bucket value, bucketBound value⟩ : Fin 6)
    let slot : Fin 6 → ℕ := fun shade => if shade = 0 then 4 else if shade = 1 then 0
      else if shade = 2 then 2 else if shade = 3 then 5 else if shade = 4 then 1 else 3
    let position := fun value : ℕ => slot (color value)
    have firstColor : color first = 1 := by simp [color, bucket]
    have lastColor : color last = 3 := by
      simp [color, bucket, show ¬ last < first by omega, show last ≠ first by omega]
    have beforeColor (value : ℕ) (hv : value ∈ before) : color value = 4 := by
      have hh := upperBounds value (List.mem_append_left _ hv)
      simp [color, bucket, show ¬ value < first by omega, show value ≠ first by omega,
        show ¬ value < last by omega, show value ≠ last by omega, hv]
    have afterColor (value : ℕ) (hv : value ∈ after) : color value = 5 := by
      have hh := upperBounds value (List.mem_append_right _ hv)
      have hn : value ∉ before := fun hm =>
        (List.nodup_append.mp upperNodup).2.2 value hm value hv rfl
      simp [color, bucket, show ¬ value < first by omega, show value ≠ first by omega,
        show ¬ value < last by omega, show value ≠ last by omega, hn]
    have middleColor (value : ℕ) (hv : value ∈ middle) : color value = 2 := by
      have hh := middleBounds value hv
      simp [color, bucket, show ¬ value < first by omega, show value ≠ first by omega, hh.2]
    have lowerColor (value : ℕ) (hv : value ∈ lower) : color value = 0 := by
      simp [color, bucket, (lowerBounds value hv).2]
    have collapsed (value : ℕ) : min (color value).val 4 =
        if value < first then 0 else if value = first then 1 else if value < last then 2
        else if value = last then 3 else 4 := by
      dsimp [color, bucket]; split_ifs <;> rfl
    have colorMono (left right : ℕ) (hh : left ≤ right) :
        min (color left).val 4 ≤ min (color right).val 4 := by
      rw [collapsed, collapsed]; split_ifs <;> omega
    let ordered := fun left right : ℕ => position left ≤ position right ∧
      (position left = position right → left < right)
    have beforeOrdered : before.Pairwise ordered := hb.imp_of_mem (by
      intro left right hl hr hh
      simp [ordered, position, beforeColor left hl, beforeColor right hr, hh])
    have afterOrdered : after.Pairwise ordered := ha.imp_of_mem (by
      intro left right hl hr hh
      simp [ordered, position, afterColor left hl, afterColor right hr, hh])
    have middleOrdered : middle.Pairwise ordered :=
      (List.pairwise_lt_range' _ (by omega) : middle.Pairwise (· < ·)).imp_of_mem (by
        intro left right hl hr hh
        simp [ordered, position, middleColor left hl, middleColor right hr, hh])
    have lowerOrdered : lower.Pairwise ordered :=
      (List.pairwise_lt_range' _ (by omega) : lower.Pairwise (· < ·)).imp_of_mem (by
        intro left right hl hr hh
        simp [ordered, position, lowerColor left hl, lowerColor right hr, hh])
    have orderedWord : word.Pairwise ordered := by
      simp only [word, List.cons_append, List.pairwise_cons, List.pairwise_append,
        List.pairwise_singleton, List.mem_append, List.mem_singleton, List.not_mem_nil,
        forall_false, or_imp, forall_and, forall_eq, and_true]
      and_intros
      all_goals first
        | exact beforeOrdered
        | exact afterOrdered
        | exact middleOrdered
        | exact lowerOrdered
        | trivial
        | exact List.Pairwise.nil
        | (intros; omega)
        | (intros; simp [ordered, position, firstColor, lastColor, beforeColor, afterColor,
            middleColor, lowerColor, slot, *])
    have profiles : ∀ firstShade secondShade thirdShade fourthShade : Fin 6,
        min firstShade.val 4 ≤ min secondShade.val 4 →
        min secondShade.val 4 ≤ min thirdShade.val 4 →
        min thirdShade.val 4 ≤ min fourthShade.val 4 →
        (slot firstShade ≤ slot fourthShade ∧ slot fourthShade < slot thirdShade ∧
          slot thirdShade < slot secondShade → firstShade = 1 ∧ secondShade = 3) ∧
        ¬ (slot fourthShade < slot thirdShade ∧ slot thirdShade < slot secondShade ∧
          slot secondShade < slot firstShade) ∧
        ¬ (slot thirdShade < slot secondShade ∧ slot secondShade < slot firstShade ∧
          slot firstShade ≤ slot fourthShade) ∧
        ¬ (slot secondShade < slot firstShade ∧ slot firstShade ≤ slot fourthShade ∧
          slot fourthShade < slot thirdShade) := by decide
    have edge (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (left right : ℕ) (hr : [left, right].Sublist pattern) :
        ordered (chosen left) (chosen right) :=
      List.pairwise_iff_forall_sublist.mp orderedWord
        ((hr.map chosen).trans (hs.trans hcontainer))
    have descentEdge (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hcontainer : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (left right : ℕ) (hr : [left, right].Sublist pattern)
        (hd : chosen right < chosen left) : position (chosen left) < position (chosen right) := by
      have hh := edge pattern container chosen hcontainer hs left right hr
      change position (chosen left) ≤ position (chosen right) ∧ _ at hh
      have hn : position (chosen left) ≠ position (chosen right) := by
        intro he; have := hh.2 he; omega
      omega
    have profile (chosen : ℕ → ℕ)
        (hi : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1)) :=
      profiles (color (chosen 1)) (color (chosen 2)) (color (chosen 3)) (color (chosen 4))
        (colorMono _ _ (hi 1 (by omega) (by omega)).le)
        (colorMono _ _ (hi 2 (by omega) (by omega)).le)
        (colorMono _ _ (hi 3 (by omega) (by omega)).le)
    have firstEndpoint (value : ℕ) (hc : color value = 1) : value = first := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he; split_ifs at he <;> omega
    have lastEndpoint (value : ℕ) (hc : color value = 3) : value = last := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he; split_ifs at he <;> omega
    have forcedEndpoints (container : List ℕ) (hc : container.Sublist word)
        (ho : Occurs [1, 4, 3, 2] container) : first ∈ container ∧ last ∈ container := by
      obtain ⟨chosen, hi, _, hs, _⟩ := ho
      have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
        simpa [letters] using hi
      have hp := (profile chosen hi').1
        ⟨(edge _ _ _ hc hs 1 4 (by decide)).1,
          descentEdge _ _ _ hc hs 4 3 (by decide) (hi' 3 (by omega) (by omega)),
          descentEdge _ _ _ hc hs 3 2 (by decide) (hi' 2 (by omega) (by omega))⟩
      exact ⟨firstEndpoint _ hp.1 ▸ hs.subset (by simp),
        lastEndpoint _ hp.2 ▸ hs.subset (by simp)⟩
    refine ⟨wordPerm, (unique_bad_cut_iff size (by omega) [1, 4, 3, 2] word
      (by decide) wordPerm).mpr ⟨?_, ?_, ?_, ?_⟩⟩
    · obtain ⟨upper, hub, bottom, hba, hd⟩ := hex
      have hbnd := upperBounds bottom (List.mem_append_right _ hba)
      let chosen := fun rank : ℕ => if rank = 1 then first else if rank = 2 then last
        else if rank = 3 then bottom else upper
      refine ⟨chosen, ?_, ?_, ?_, by simp⟩
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 := by simp [letters] at hhi; omega
        rcases hh with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · intro rank hlo hhi
        have hh : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by
          simp [letters] at hhi; omega
        rcases hh with rfl | rfl | rfl | rfl <;> simp [word, chosen, hub, hba]
      · change [first, upper, bottom, last].Sublist word
        have hp := (List.singleton_sublist.mpr hub).append
          ((List.singleton_sublist.mpr hba).trans (List.sublist_append_left after lower))
        have hp := hp.trans (by
          simpa only [List.append_assoc] using
            (List.Sublist.refl before).append
              (List.sublist_append_right middle (after ++ lower)))
        simpa [word, chosen, List.append_assoc] using
          (hp.append (List.Sublist.refl [last])).cons_cons first
    · intro shift hlo hhi ho
      have hh : shift = 1 ∨ shift = 2 ∨ shift = 3 := by omega
      rcases hh with rfl | rfl | rfl
      all_goals
        obtain ⟨chosen, hi, _, hs, _⟩ := ho
        have hi' : ∀ rank, 1 ≤ rank → rank < 4 → chosen rank < chosen (rank + 1) := by
          simpa [letters] using hi
        have h12 := hi' 1 (by omega) (by omega)
        have h23 := hi' 2 (by omega) (by omega)
        have h34 := hi' 3 (by omega) (by omega)
      · exact (profile chosen hi').2.1
          ⟨descentEdge _ _ _ (List.Sublist.refl _) hs 4 3 (by decide) h34,
            descentEdge _ _ _ (List.Sublist.refl _) hs 3 2 (by decide) h23,
            descentEdge _ _ _ (List.Sublist.refl _) hs 2 1 (by decide) h12⟩
      · exact (profile chosen hi').2.2.1
          ⟨descentEdge _ _ _ (List.Sublist.refl _) hs 3 2 (by decide) h23,
            descentEdge _ _ _ (List.Sublist.refl _) hs 2 1 (by decide) h12,
            (edge _ _ _ (List.Sublist.refl _) hs 1 4 (by decide)).1⟩
      · exact (profile chosen hi').2.2.2
          ⟨descentEdge _ _ _ (List.Sublist.refl _) hs 2 1 (by decide) h12,
            (edge _ _ _ (List.Sublist.refl _) hs 1 4 (by decide)).1,
            descentEdge _ _ _ (List.Sublist.refl _) hs 4 3 (by decide) h34⟩
    · intro ho
      have hh := (forcedEndpoints word.tail (List.tail_sublist _) ho).1
      exact (List.nodup_cons.mp wordNodup).1 hh
    · intro ho
      have hh := (forcedEndpoints word.dropLast (List.dropLast_sublist _) ho).2
      have ht : word = (first :: before ++ middle ++ after ++ lower) ++ [last] := by
        simp [word, List.append_assoc]
      have hn := List.nodup_append.mp (ht ▸ wordNodup)
      have he : word.dropLast = first :: before ++ middle ++ after ++ lower := by
        rw [ht, List.dropLast_append_cons]; simp
      exact hn.2.2 last (he ▸ hh) last (by simp) rfl
  let width := size - last
  let domain : Set (List ℕ) := {parent | parent.Perm (List.range' 1 width) ∧
    ¬ parent.Pairwise (· > ·) ∧ ∃ cut ≤ width,
      (parent.take cut).Pairwise (· > ·) ∧ (parent.drop cut).Pairwise (· > ·)}
  let target : Set (List ℕ) := {word | word.Perm (List.range' 1 size) ∧
    word.head? = some first ∧ word.getLast? = some last ∧
    ∀ cut < size, Occurs [1, 4, 3, 2] (word.rotate cut) ↔ cut = 0}
  let relabel := fun value : ℕ => size + 1 - value
  have relabelBounds (value : ℕ) (hv : value ∈ List.range' 1 width) :
      last < relabel value ∧ relabel value ≤ size := by
    have hh := List.mem_range'_1.mp hv; dsimp [relabel, width] at *; omega
  have relabelTwice (value : ℕ) (hv : value ≤ size + 1) :
      relabel (relabel value) = value := by dsimp [relabel]; omega
  have relabelPerm (parent : List ℕ) (hp : parent.Perm (List.range' 1 width)) :
      (parent.map relabel).Perm (List.range' (last + 1) width) := by
    have he : (List.range' 1 width).map relabel = (List.range' (last + 1) width).reverse := by
      have hr : List.range' 1 width = (List.range width).map (1 + ·) := by
        simpa only [List.range_eq_range', Nat.add_zero, Nat.mul_one] using
          (List.map_add_range' (a := 1) 0 width 1).symm
      rw [hr, List.map_map, List.reverse_range']
      apply List.map_congr_left
      intro value hv
      have hh := List.mem_range.mp hv
      dsimp [Function.comp_def, relabel, width] at *; omega
    exact (he ▸ hp.map relabel).trans (List.reverse_perm _)
  have uniqueCut (parent : List ℕ) (hp : parent ∈ domain) (cut other : ℕ)
      (hc : (parent.take cut).Pairwise (· > ·) ∧ (parent.drop cut).Pairwise (· > ·))
      (ho : (parent.take other).Pairwise (· > ·) ∧ (parent.drop other).Pairwise (· > ·)) :
      cut = other := by
    have hnotChain : ¬ parent.IsChain (· > ·) := fun hh =>
      hp.2.1 (List.isChain_iff_pairwise.mp hh)
    obtain ⟨index, hindex, hbad⟩ := List.exists_not_getElem_of_not_isChain hnotChain
    have forced (boundary : ℕ)
        (hb : (parent.take boundary).Pairwise (· > ·) ∧
          (parent.drop boundary).Pairwise (· > ·)) : boundary = index + 1 := by
      by_contra hne
      by_cases hbefore : index + 1 < boundary
      · have hlo : index < (parent.take boundary).length := by simp; omega
        have hhi : index + 1 < (parent.take boundary).length := by simp; omega
        have hh := List.pairwise_iff_getElem.mp hb.1 index (index + 1) hlo hhi (by omega)
        exact hbad (by simpa only [List.getElem_take] using hh)
      · have hafter : boundary ≤ index := by omega
        have hlo : index - boundary < (parent.drop boundary).length := by simp; omega
        have hhi : index + 1 - boundary < (parent.drop boundary).length := by simp; omega
        have hh := List.pairwise_iff_getElem.mp hb.2 (index - boundary)
          (index + 1 - boundary) hlo hhi (by omega)
        exact hbad (by
          simpa only [List.getElem_drop, Nat.add_comm boundary, Nat.sub_add_cancel hafter,
            Nat.sub_add_cancel (by omega : boundary ≤ index + 1)] using hh)
    exact (forced cut hc).trans (forced other ho).symm
  let emit := fun (parent : List ℕ) (hp : parent ∈ domain) =>
    first :: (parent.take (Classical.choose hp.2.2)).map relabel ++ middle ++
      (parent.drop (Classical.choose hp.2.2)).map relabel ++ lower ++ [last]
  have emitMember (parent : List ℕ) (hp : parent ∈ domain) : emit parent hp ∈ target := by
    let cut := Classical.choose hp.2.2
    have hc := Classical.choose_spec hp.2.2
    have hlength : parent.length = width := by simpa using hp.1.length_eq
    let before := (parent.take cut).map relabel
    let after := (parent.drop cut).map relabel
    have hu : (before ++ after).Perm (List.range' (last + 1) width) := by
      simpa [before, after, ← List.map_append] using relabelPerm parent hp.1
    have sorted (piece : List ℕ) (hs : piece.Sublist parent) (hd : piece.Pairwise (· > ·)) :
        (piece.map relabel).Pairwise (· < ·) := List.pairwise_map.mpr (hd.imp_of_mem (by
      intro left right hl hr hh
      have hbl := relabelBounds left (hp.1.mem_iff.mp (hs.subset hl))
      have hbr := relabelBounds right (hp.1.mem_iff.mp (hs.subset hr))
      dsimp [relabel] at *; omega))
    have beforeSorted := sorted _ (List.take_sublist _ _) hc.2.1
    have afterSorted := sorted _ (List.drop_sublist _ _) hc.2.2
    have parentPair : ∃ upper ∈ parent.take cut,
        ∃ bottom ∈ parent.drop cut, upper < bottom := by
      have hn : ¬ ∀ left ∈ parent.take cut, ∀ right ∈ parent.drop cut, left > right := by
        intro hh
        exact hp.2.1 ((List.take_append_drop cut parent).symm ▸
          List.pairwise_append.mpr ⟨hc.2.1, hc.2.2, hh⟩)
      push_neg at hn
      obtain ⟨left, hl, right, hr, hh⟩ := hn
      have hne : left ≠ right := (List.nodup_append.mp
        ((List.take_append_drop cut parent).symm ▸
          (hp.1.nodup_iff.mpr List.nodup_range'))).2.2 left hl right hr
      exact ⟨left, hl, right, hr, by omega⟩
    have hex : ∃ upper ∈ before, ∃ bottom ∈ after, bottom < upper := by
      obtain ⟨left, hl, right, hr, hh⟩ := parentPair
      have hbl := relabelBounds left (hp.1.mem_iff.mp ((List.take_sublist _ _).subset hl))
      have hbr := relabelBounds right (hp.1.mem_iff.mp ((List.drop_sublist _ _).subset hr))
      refine ⟨relabel left, List.mem_map_of_mem hl, relabel right, List.mem_map_of_mem hr, ?_⟩
      dsimp [relabel] at *; omega
    have hh := construction before after hu beforeSorted afterSorted hex
    refine ⟨hh.1, by simp [emit], ?_, hh.2⟩
    change ((first :: before ++ middle ++ after ++ lower) ++ [last]).getLast? = some last
    rw [List.getLast?_append_cons]; rfl
  have recover (parent : List ℕ) (hp : parent ∈ domain) :
      (emit parent hp).filter (fun value => decide (last < value)) = parent.map relabel := by
    let cut := Classical.choose hp.2.2
    have part (piece : List ℕ) (hs : piece.Sublist parent) :
        (piece.map relabel).filter (fun value => decide (last < value)) =
          piece.map relabel := List.filter_eq_self.mpr (by
      intro value hv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hv
      exact decide_eq_true (relabelBounds original (hp.1.mem_iff.mp (hs.subset ho))).1)
    have hm : middle.filter (fun value => decide (last < value)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv
        have hh := List.mem_range'_1.mp hv; simp; omega)
    have hl : lower.filter (fun value => decide (last < value)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv
        have hh := List.mem_range'_1.mp hv; simp; omega)
    simp only [emit, List.filter_cons, show ¬ last < first by omega, decide_false,
      Bool.false_eq_true, if_false, List.filter_append,
      part _ (List.take_sublist _ _), part _ (List.drop_sublist _ _), hm, hl,
      List.filter_singleton, lt_self_iff_false, decide_false, List.append_nil,
      List.filter_nil, ← List.map_append, List.take_append_drop]
  have emitInjective (left right : List ℕ) (hl : left ∈ domain) (hr : right ∈ domain)
      (he : emit left hl = emit right hr) : left = right := by
    have hh := congrArg (fun word : List ℕ =>
      word.filter (fun value => decide (last < value))) he
    rw [recover left hl, recover right hr] at hh
    have hh := congrArg (List.map relabel) hh
    have restore (parent : List ℕ) (hp : parent ∈ domain) :
        (parent.map relabel).map relabel = parent := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id parent]
      apply List.map_congr_left
      intro value hv
      have hb := List.mem_range'_1.mp (hp.1.mem_iff.mp hv)
      exact relabelTwice value (by dsimp [width] at hb; omega)
    simpa only [restore left hl, restore right hr] using hh
  have emitSurjective (word : List ℕ) (hw : word ∈ target) :
      ∃ parent, ∃ hp : parent ∈ domain, emit parent hp = word := by
    obtain ⟨front, hlast⟩ := List.getLast?_eq_some_iff.mp hw.2.2.1
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = first :: interior ++ [last] := by
      cases front with
      | nil => have := hw.1.length_eq; simp [hlast] at this; omega
      | cons head interior =>
        have hh : head = first := by simpa [hlast] using hw.2.1
        exact ⟨interior, by simpa [hh] using hlast⟩
    obtain ⟨_, before, after, hnormal, hu, hb, ha, upper, hub, bottom, hba, hd⟩ :=
      descending_positive_middle_normal_form size first last interior (by omega)
        hfirst hmiddle (hsplit ▸ hw.1) (hsplit ▸ hw.2.2.2)
    let upperWord := before ++ after
    let parent := upperWord.map relabel
    have ubounds (value : ℕ) (hv : value ∈ upperWord) : last < value ∧ value ≤ size := by
      have hh := List.mem_range'_1.mp (hu.mem_iff.mp hv); omega
    have parentPerm : parent.Perm (List.range' 1 width) := by
      have hh := (relabelPerm (List.range' 1 width) (List.Perm.refl _)).map relabel
      have he : ((List.range' 1 width).map relabel).map relabel = List.range' 1 width := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id (List.range' 1 width)]
        apply List.map_congr_left
        intro value hv
        have hh := List.mem_range'_1.mp hv
        exact relabelTwice value (by dsimp [width] at hh; omega)
      exact (hu.map relabel).trans (he ▸ hh).symm
    have restore : parent.map relabel = upperWord := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id upperWord]
      apply List.map_congr_left
      intro value hv
      exact relabelTwice value (by have := (ubounds value hv).2; omega)
    have decreasing (piece : List ℕ) (hs : piece.Sublist upperWord)
        (hi : piece.Pairwise (· < ·)) : (piece.map relabel).Pairwise (· > ·) :=
      List.pairwise_map.mpr (hi.imp_of_mem (by
        intro left right hl hr hh
        have := ubounds left (hs.subset hl)
        have := ubounds right (hs.subset hr)
        dsimp [relabel] at *; omega))
    have cutFacts : (parent.take before.length).Pairwise (· > ·) ∧
        (parent.drop before.length).Pairwise (· > ·) := by
      have hl : before.length = (before.map relabel).length :=
        (List.length_map (f := relabel) (as := before)).symm
      simpa only [parent, upperWord, List.map_append, hl, List.take_left, List.drop_left] using
        And.intro (decreasing before (List.sublist_append_left _ _) hb)
          (decreasing after (List.sublist_append_right _ _) ha)
    have hp : parent ∈ domain := by
      refine ⟨parentPerm, ?_, before.length, ?_, cutFacts⟩
      · intro hdec
        have hs : [upper, bottom].Sublist upperWord :=
          (List.singleton_sublist.mpr hub).append (List.singleton_sublist.mpr hba)
        have hh := List.pairwise_iff_forall_sublist.mp hdec (hs.map relabel)
        have := ubounds upper (List.mem_append_left _ hub)
        have := ubounds bottom (List.mem_append_right _ hba)
        dsimp [relabel] at *; omega
      · have hl := hu.length_eq
        simp [upperWord, List.length_append] at hl
        dsimp [width]; omega
    have chosenCut : Classical.choose hp.2.2 = before.length :=
      uniqueCut parent hp _ _ (Classical.choose_spec hp.2.2).2 cutFacts
    refine ⟨parent, hp, ?_⟩
    have parts : (parent.take before.length).map relabel = before ∧
        (parent.drop before.length).map relabel = after := by
      have htake := congrArg (List.take before.length) restore
      have hdrop := congrArg (List.drop before.length) restore
      simpa [upperWord, ← List.map_take, ← List.map_drop] using And.intro htake hdrop
    simp only [emit, chosenCut, parts.1, parts.2]
    simpa only [middle, lower, List.cons_append, List.append_assoc] using
      (hsplit.trans (congrArg (fun body => first :: body ++ [last]) hnormal)).symm
  have hcard := Set.ncard_congr (s := domain) (t := target) emit emitMember
    emitInjective (by
      intro word hw
      obtain ⟨parent, hp, he⟩ := emitSurjective word hw
      exact ⟨parent, hp, he⟩)
  have hcount := (RotationAvoidanceOneAscent.one_ascent_count width).1
  change domain.ncard = _ at hcount
  change target.ncard = _
  exact hcard.symm.trans hcount

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceDescendingSplit
