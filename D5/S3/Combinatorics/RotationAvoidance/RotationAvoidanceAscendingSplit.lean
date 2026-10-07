/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingSplit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscendingSplit
   mirror-E: none(waiver:non-extreme-ascending-slice-count)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The outside block marks the unique ascent of two decreasing middle runs. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscendingOutside
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceOneAscent
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscendingSplit

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCircular
open RotationAvoidanceAscendingOutside

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxSize 4096 in
theorem ascending_nonextreme_endpoint_count (size first last : ℕ)
    (hfirst : 1 ≤ first) (hmiddle : first + 2 < last) (hlast : last ≤ size)
    (houtside : 1 < first ∨ last < size) :
    ({word : List ℕ | word.Perm (List.range' 1 size) ∧
      word.head? = some first ∧ word.getLast? = some last ∧
      ∀ cut < size, Occurs [1, 2, 3, 4] (word.rotate cut) ↔ cut = 0} :
      Set (List ℕ)).ncard = 2 ^ (last - first - 1) - (last - first - 1) - 1 := by
  classical
  let lower := (List.range' 1 (first - 1)).reverse
  let upper := (List.range' (last + 1) (size - last)).reverse
  have construction (before after : List ℕ)
      (hm : (before ++ after).Perm (List.range' (first + 1) (last - first - 1)))
      (hb : before.Pairwise (· > ·)) (ha : after.Pairwise (· > ·))
      (hex : ∃ low ∈ before, ∃ high ∈ after, low < high) :
      let word := first :: before ++ lower ++ upper ++ after ++ [last]
      word.Perm (List.range' 1 size) ∧
        ∀ cut < size, Occurs [1, 2, 3, 4] (word.rotate cut) ↔ cut = 0 := by
    let word := first :: before ++ lower ++ upper ++ after ++ [last]
    have middleBounds (value : ℕ) (hv : value ∈ before ++ after) :
        first < value ∧ value < last := by
      have hh := List.mem_range'_1.mp (hm.mem_iff.mp hv); omega
    have lowerBounds (value : ℕ) (hv : value ∈ lower) : 1 ≤ value ∧ value < first := by
      have hh := List.mem_range'_1.mp (List.mem_reverse.mp hv); omega
    have upperBounds (value : ℕ) (hv : value ∈ upper) : last < value ∧ value ≤ size := by
      have hh := List.mem_range'_1.mp (List.mem_reverse.mp hv); omega
    have middleNodup := hm.nodup_iff.mpr List.nodup_range'
    have rangeSplit : List.range' 1 size =
        List.range' 1 (first - 1) ++ [first] ++
          List.range' (first + 1) (last - first - 1) ++ [last] ++
            List.range' (last + 1) (size - last) := by
      have hs : size = (first - 1) + 1 + (last - first - 1) + 1 + (size - last) := by
        omega
      conv_lhs => rw [hs]
      rw [← List.range'_append, ← List.range'_append, ← List.range'_append,
        ← List.range'_append]
      simp only [List.range'_one, Nat.one_mul,
        show 1 + (first - 1) = first by omega,
        show 1 + (first - 1 + 1) = first + 1 by omega,
        show 1 + (first - 1 + 1 + (last - first - 1)) = last by omega,
        show 1 + (first - 1 + 1 + (last - first - 1) + 1) = last + 1 by omega]
    have wordPerm : word.Perm (List.range' 1 size) := by
      apply List.perm_iff_count.mpr
      intro value
      have hh := hm.count_eq value
      rw [rangeSplit]
      simp only [word, lower, upper, List.count_append, List.count_cons,
        List.count_reverse, List.count_singleton, List.count_nil, List.count_append] at *
      omega
    have wordNodup := wordPerm.nodup_iff.mpr List.nodup_range'
    let bucket := fun value : ℕ => if value < first then 0 else if value = first then 1
      else if value < last then if value ∈ before then 2 else 3
      else if value = last then 4 else 5
    have bucketBound (value : ℕ) : bucket value < 6 := by
      dsimp [bucket]; split_ifs <;> omega
    let color := fun value : ℕ => (⟨bucket value, bucketBound value⟩ : Fin 6)
    let rank := fun shade : Fin 6 => if shade.val ≤ 2 then shade.val else shade.val - 1
    let slot : Fin 6 → ℕ := fun shade => if shade = 0 then 2 else if shade = 1 then 0
      else if shade = 2 then 1 else if shade = 3 then 4 else if shade = 4 then 5 else 3
    let position := fun value : ℕ => slot (color value)
    have firstColor : color first = 1 := by simp [color, bucket]
    have lastColor : color last = 4 := by
      simp [color, bucket, show ¬ last < first by omega, show last ≠ first by omega]
    have beforeColor (value : ℕ) (hv : value ∈ before) : color value = 2 := by
      have hh := middleBounds value (List.mem_append_left _ hv)
      simp [color, bucket, show ¬ value < first by omega, show value ≠ first by omega,
        hh.2, hv]
    have afterColor (value : ℕ) (hv : value ∈ after) : color value = 3 := by
      have hh := middleBounds value (List.mem_append_right _ hv)
      have hn : value ∉ before := fun hm =>
        (List.nodup_append.mp middleNodup).2.2 value hm value hv rfl
      simp [color, bucket, show ¬ value < first by omega, show value ≠ first by omega,
        hh.2, hn]
    have lowerColor (value : ℕ) (hv : value ∈ lower) : color value = 0 := by
      simp [color, bucket, (lowerBounds value hv).2]
    have upperColor (value : ℕ) (hv : value ∈ upper) : color value = 5 := by
      have hh := upperBounds value hv
      simp [color, bucket, show ¬ value < first by omega, show value ≠ first by omega,
        show ¬ value < last by omega, show value ≠ last by omega]
    have collapsed (value : ℕ) : rank (color value) =
        if value < first then 0 else if value = first then 1 else if value < last then 2
        else if value = last then 3 else 4 := by
      dsimp [rank, color, bucket]; split_ifs <;> omega
    have colorMono (left right : ℕ) (hh : left ≤ right) :
        rank (color left) ≤ rank (color right) := by
      rw [collapsed, collapsed]; split_ifs <;> omega
    let ordered := fun left right : ℕ => position left ≤ position right ∧
      (position left = position right → left > right)
    have beforeOrdered : before.Pairwise ordered := hb.imp_of_mem (by
      intro left right hl hr hh
      simp [ordered, position, beforeColor left hl, beforeColor right hr, hh])
    have afterOrdered : after.Pairwise ordered := ha.imp_of_mem (by
      intro left right hl hr hh
      simp [ordered, position, afterColor left hl, afterColor right hr, hh])
    have lowerSorted : lower.Pairwise (· > ·) := by
      simpa only [lower, List.pairwise_reverse] using
        (List.pairwise_lt_range' (s := 1) (n := first - 1))
    have upperSorted : upper.Pairwise (· > ·) := by
      simpa only [upper, List.pairwise_reverse] using
        (List.pairwise_lt_range' (s := last + 1) (n := size - last))
    have lowerOrdered : lower.Pairwise ordered := lowerSorted.imp_of_mem (by
      intro left right hl hr hh
      simp [ordered, position, lowerColor left hl, lowerColor right hr, hh])
    have upperOrdered : upper.Pairwise ordered := upperSorted.imp_of_mem (by
      intro left right hl hr hh
      simp [ordered, position, upperColor left hl, upperColor right hr, hh])
    have endpointsSeparate : position first ≠ position last := by
      simp [position, firstColor, lastColor, slot]
    have orderedWord : word.Pairwise ordered := by
      simp only [word, List.cons_append, List.pairwise_cons, List.pairwise_append,
        List.pairwise_singleton, List.mem_append, List.mem_singleton, List.not_mem_nil,
        forall_false, or_imp, forall_and, forall_eq, and_true]
      and_intros
      all_goals first
        | exact beforeOrdered
        | exact afterOrdered
        | exact lowerOrdered
        | exact upperOrdered
        | trivial
        | exact List.Pairwise.nil
        | (intros; omega)
        | (intros; simp [ordered, position, firstColor, lastColor, beforeColor, afterColor,
            lowerColor, upperColor, slot, *])
    have profiles : ∀ firstShade secondShade thirdShade fourthShade : Fin 6,
        rank firstShade ≤ rank secondShade → rank secondShade ≤ rank thirdShade →
        rank thirdShade ≤ rank fourthShade →
        (slot firstShade < slot secondShade ∧ slot secondShade < slot thirdShade ∧
          slot thirdShade < slot fourthShade → firstShade = 1 ∧ fourthShade = 4) ∧
        ¬ (slot secondShade < slot thirdShade ∧ slot thirdShade < slot fourthShade ∧
          slot fourthShade ≤ slot firstShade) ∧
        ¬ (slot thirdShade < slot fourthShade ∧ slot fourthShade ≤ slot firstShade ∧
          slot firstShade < slot secondShade) ∧
        ¬ (slot fourthShade ≤ slot firstShade ∧ slot firstShade < slot secondShade ∧
          slot secondShade < slot thirdShade) := by decide
    have edge (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hc : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (left right : ℕ) (hr : [left, right].Sublist pattern) :
        ordered (chosen left) (chosen right) :=
      List.pairwise_iff_forall_sublist.mp orderedWord ((hr.map chosen).trans (hs.trans hc))
    have ascentEdge (pattern container : List ℕ) (chosen : ℕ → ℕ)
        (hc : container.Sublist word) (hs : (pattern.map chosen).Sublist container)
        (left right : ℕ) (hr : [left, right].Sublist pattern)
        (hh : chosen left < chosen right) : position (chosen left) < position (chosen right) := by
      have he := edge pattern container chosen hc hs left right hr
      change position (chosen left) ≤ position (chosen right) ∧ _ at he
      have hn : position (chosen left) ≠ position (chosen right) := by
        intro heq; have := he.2 heq; omega
      omega
    have profile (chosen : ℕ → ℕ)
        (hi : ∀ value, 1 ≤ value → value < 4 → chosen value < chosen (value + 1)) :=
      profiles (color (chosen 1)) (color (chosen 2)) (color (chosen 3)) (color (chosen 4))
        (colorMono _ _ (hi 1 (by omega) (by omega)).le)
        (colorMono _ _ (hi 2 (by omega) (by omega)).le)
        (colorMono _ _ (hi 3 (by omega) (by omega)).le)
    have firstEndpoint (value : ℕ) (hc : color value = 1) : value = first := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he; split_ifs at he <;> omega
    have lastEndpoint (value : ℕ) (hc : color value = 4) : value = last := by
      have he := congrArg Fin.val hc
      dsimp [color, bucket] at he; split_ifs at he <;> omega
    have forcedEndpoints (container : List ℕ) (hc : container.Sublist word)
        (ho : Occurs [1, 2, 3, 4] container) : first ∈ container ∧ last ∈ container := by
      obtain ⟨chosen, hi, _, hs, _⟩ := ho
      have hi' : ∀ value, 1 ≤ value → value < 4 → chosen value < chosen (value + 1) := by
        simpa [letters] using hi
      have hp := (profile chosen hi').1
        ⟨ascentEdge _ _ _ hc hs 1 2 (by decide) (hi' 1 (by omega) (by omega)),
          ascentEdge _ _ _ hc hs 2 3 (by decide) (hi' 2 (by omega) (by omega)),
          ascentEdge _ _ _ hc hs 3 4 (by decide) (hi' 3 (by omega) (by omega))⟩
      exact ⟨firstEndpoint _ hp.1 ▸ hs.subset (by simp),
        lastEndpoint _ hp.2 ▸ hs.subset (by simp)⟩
    refine ⟨wordPerm, (unique_bad_cut_iff size (by omega) [1, 2, 3, 4] word
      (by decide) wordPerm).mpr ⟨?_, ?_, ?_, ?_⟩⟩
    · obtain ⟨low, hl, high, hh, ha⟩ := hex
      have hbl := middleBounds low (List.mem_append_left _ hl)
      have hbh := middleBounds high (List.mem_append_right _ hh)
      let chosen := fun value : ℕ => if value = 1 then first else if value = 2 then low
        else if value = 3 then high else last
      refine ⟨chosen, ?_, ?_, ?_, by simp⟩
      · intro value hlo hhi
        have he : value = 1 ∨ value = 2 ∨ value = 3 := by simp [letters] at hhi; omega
        rcases he with rfl | rfl | rfl <;> simp [chosen] <;> omega
      · intro value hlo hhi
        have he : value = 1 ∨ value = 2 ∨ value = 3 ∨ value = 4 := by
          simp [letters] at hhi; omega
        rcases he with rfl | rfl | rfl | rfl <;> simp [word, chosen, hl, hh]
      · change [first, low, high, last].Sublist word
        have hs := (List.singleton_sublist.mpr hl).append
          ((List.singleton_sublist.mpr hh).trans (List.sublist_append_right (lower ++ upper) _))
        simpa [word, List.append_assoc] using
          (hs.append (List.Sublist.refl [last])).cons_cons first
    · intro shift hlo hhi ho
      have hh : shift = 1 ∨ shift = 2 ∨ shift = 3 := by omega
      rcases hh with rfl | rfl | rfl
      all_goals
        obtain ⟨chosen, hi, _, hs, _⟩ := ho
        have hi' : ∀ value, 1 ≤ value → value < 4 → chosen value < chosen (value + 1) := by
          simpa [letters] using hi
      · exact (profile chosen hi').2.1
          ⟨ascentEdge _ _ _ (List.Sublist.refl _) hs 2 3 (by decide)
              (hi' 2 (by omega) (by omega)),
            ascentEdge _ _ _ (List.Sublist.refl _) hs 3 4 (by decide)
              (hi' 3 (by omega) (by omega)),
            (edge _ _ _ (List.Sublist.refl _) hs 4 1 (by decide)).1⟩
      · exact (profile chosen hi').2.2.1
          ⟨ascentEdge _ _ _ (List.Sublist.refl _) hs 3 4 (by decide)
              (hi' 3 (by omega) (by omega)),
            (edge _ _ _ (List.Sublist.refl _) hs 4 1 (by decide)).1,
            ascentEdge _ _ _ (List.Sublist.refl _) hs 1 2 (by decide)
              (hi' 1 (by omega) (by omega))⟩
      · exact (profile chosen hi').2.2.2
          ⟨(edge _ _ _ (List.Sublist.refl _) hs 4 1 (by decide)).1,
            ascentEdge _ _ _ (List.Sublist.refl _) hs 1 2 (by decide)
              (hi' 1 (by omega) (by omega)),
            ascentEdge _ _ _ (List.Sublist.refl _) hs 2 3 (by decide)
              (hi' 2 (by omega) (by omega))⟩
    · intro ho
      have hh := (forcedEndpoints word.tail (List.tail_sublist _) ho).1
      exact (List.nodup_cons.mp wordNodup).1 hh
    · intro ho
      have hh := (forcedEndpoints word.dropLast (List.dropLast_sublist _) ho).2
      have ht : word = (first :: before ++ lower ++ upper ++ after) ++ [last] := by
        simp [word, List.append_assoc]
      have hn := List.nodup_append.mp (ht ▸ wordNodup)
      have he : word.dropLast = first :: before ++ lower ++ upper ++ after := by
        rw [ht, List.dropLast_append_cons]; simp
      exact hn.2.2 last (he ▸ hh) last (by simp) rfl
  let width := last - first - 1
  let domain : Set (List ℕ) := {parent | parent.Perm (List.range' 1 width) ∧
    ¬ parent.Pairwise (· > ·) ∧ ∃ cut ≤ width,
      (parent.take cut).Pairwise (· > ·) ∧ (parent.drop cut).Pairwise (· > ·)}
  let target : Set (List ℕ) := {word | word.Perm (List.range' 1 size) ∧
    word.head? = some first ∧ word.getLast? = some last ∧
    ∀ cut < size, Occurs [1, 2, 3, 4] (word.rotate cut) ↔ cut = 0}
  let relabel := fun value : ℕ => first + value
  let unlabel := fun value : ℕ => value - first
  have relabelBounds (value : ℕ) (hv : value ∈ List.range' 1 width) :
      first < relabel value ∧ relabel value < last := by
    have hh := List.mem_range'_1.mp hv; dsimp [relabel, width] at *; omega
  have relabelPerm (parent : List ℕ) (hp : parent.Perm (List.range' 1 width)) :
      (parent.map relabel).Perm (List.range' (first + 1) width) := by
    have he : (List.range' 1 width).map relabel = List.range' (first + 1) width := by
      simpa [relabel] using (List.map_add_range' (a := first) 1 width 1)
    exact he ▸ hp.map relabel
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
    first :: (parent.take (Classical.choose hp.2.2)).map relabel ++ lower ++ upper ++
      (parent.drop (Classical.choose hp.2.2)).map relabel ++ [last]
  have emitMember (parent : List ℕ) (hp : parent ∈ domain) : emit parent hp ∈ target := by
    let cut := Classical.choose hp.2.2
    have hc := Classical.choose_spec hp.2.2
    let before := (parent.take cut).map relabel
    let after := (parent.drop cut).map relabel
    have hm : (before ++ after).Perm (List.range' (first + 1) width) := by
      simpa [before, after, ← List.map_append] using relabelPerm parent hp.1
    have sorted (piece : List ℕ) (hs : piece.Pairwise (· > ·)) :
        (piece.map relabel).Pairwise (· > ·) := List.pairwise_map.mpr (hs.imp (by
      intro left right hh; dsimp [relabel]; omega))
    have parentPair : ∃ low ∈ parent.take cut, ∃ high ∈ parent.drop cut, low < high := by
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
    have hex : ∃ low ∈ before, ∃ high ∈ after, low < high := by
      obtain ⟨left, hl, right, hr, hh⟩ := parentPair
      exact ⟨relabel left, List.mem_map_of_mem hl, relabel right, List.mem_map_of_mem hr,
        by dsimp [relabel]; omega⟩
    have hh := construction before after hm (sorted _ hc.2.1) (sorted _ hc.2.2) hex
    refine ⟨hh.1, by simp [emit], ?_, hh.2⟩
    change ((first :: before ++ lower ++ upper ++ after) ++ [last]).getLast? = some last
    rw [List.getLast?_append_cons]; rfl
  have recover (parent : List ℕ) (hp : parent ∈ domain) :
      (emit parent hp).filter (fun value => decide (first < value ∧ value < last)) =
        parent.map relabel := by
    have part (piece : List ℕ) (hs : piece.Sublist parent) :
        (piece.map relabel).filter (fun value => decide (first < value ∧ value < last)) =
          piece.map relabel := List.filter_eq_self.mpr (by
      intro value hv
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hv
      simp [relabelBounds original (hp.1.mem_iff.mp (hs.subset ho))])
    have hl : lower.filter (fun value => decide (first < value ∧ value < last)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv
        have hh := List.mem_range'_1.mp (List.mem_reverse.mp hv); simp; omega)
    have hu : upper.filter (fun value => decide (first < value ∧ value < last)) = [] :=
      List.filter_eq_nil_iff.mpr (by
        intro value hv
        have hh := List.mem_range'_1.mp (List.mem_reverse.mp hv); simp; omega)
    simp only [emit, List.filter_cons, lt_self_iff_false, false_and, and_false, decide_false,
      Bool.false_eq_true, if_false, List.filter_append,
      part _ (List.take_sublist _ _), part _ (List.drop_sublist _ _), hl, hu,
      List.filter_singleton, List.append_nil, List.filter_nil, ← List.map_append,
      List.take_append_drop]
  have emitInjective (left right : List ℕ) (hl : left ∈ domain) (hr : right ∈ domain)
      (he : emit left hl = emit right hr) : left = right := by
    have hh := congrArg (fun word : List ℕ =>
      word.filter (fun value => decide (first < value ∧ value < last))) he
    rw [recover left hl, recover right hr] at hh
    have hh := congrArg (List.map unlabel) hh
    have restore (parent : List ℕ) : (parent.map relabel).map unlabel = parent := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id parent]
      exact List.map_congr_left (by intro value hv; dsimp [unlabel, relabel]; omega)
    simpa only [restore] using hh
  have emitSurjective (word : List ℕ) (hw : word ∈ target) :
      ∃ parent, ∃ hp : parent ∈ domain, emit parent hp = word := by
    obtain ⟨front, hlast⟩ := List.getLast?_eq_some_iff.mp hw.2.2.1
    obtain ⟨interior, hsplit⟩ : ∃ interior, word = first :: interior ++ [last] := by
      cases front with
      | nil => have := hw.1.length_eq; simp [hlast] at this; omega
      | cons head interior =>
        have hh : head = first := by simpa [hlast] using hw.2.1
        exact ⟨interior, by simpa [hh] using hlast⟩
    obtain ⟨_, before, after, hnormal, hm, hb, ha, low, hl, high, hh, hass⟩ :=
      ascending_nonextreme_normal_form size first last interior (by omega)
        hfirst (by omega) houtside (hsplit ▸ hw.1) (hsplit ▸ hw.2.2.2)
    let middleWord := before ++ after
    let parent := middleWord.map unlabel
    have mbounds (value : ℕ) (hv : value ∈ middleWord) : first < value ∧ value < last := by
      have hh := List.mem_range'_1.mp (hm.mem_iff.mp hv); omega
    have unlabelRelabel (value : ℕ) : unlabel (relabel value) = value := by
      dsimp [unlabel, relabel]; omega
    have relabelUnlabel (value : ℕ) (hv : first ≤ value) : relabel (unlabel value) = value := by
      dsimp [unlabel, relabel]; omega
    have parentPerm : parent.Perm (List.range' 1 width) := by
      have hh := (relabelPerm (List.range' 1 width) (List.Perm.refl _)).map unlabel
      have he : ((List.range' 1 width).map relabel).map unlabel = List.range' 1 width := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id (List.range' 1 width)]
        exact List.map_congr_left (by intro value hv; exact unlabelRelabel value)
      exact (hm.map unlabel).trans (he ▸ hh).symm
    have restore : parent.map relabel = middleWord := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id middleWord]
      exact List.map_congr_left (by
        intro value hv; exact relabelUnlabel value (mbounds value hv).1.le)
    have decreasing (piece : List ℕ) (hs : piece.Sublist middleWord)
        (hd : piece.Pairwise (· > ·)) : (piece.map unlabel).Pairwise (· > ·) :=
      List.pairwise_map.mpr (hd.imp_of_mem (by
        intro left right hl hr hh
        have := mbounds left (hs.subset hl)
        have := mbounds right (hs.subset hr)
        dsimp [unlabel]; omega))
    have cutFacts : (parent.take before.length).Pairwise (· > ·) ∧
        (parent.drop before.length).Pairwise (· > ·) := by
      have hl : before.length = (before.map unlabel).length :=
        (List.length_map (f := unlabel) (as := before)).symm
      simpa only [parent, middleWord, List.map_append, hl, List.take_left, List.drop_left] using
        And.intro (decreasing before (List.sublist_append_left _ _) hb)
          (decreasing after (List.sublist_append_right _ _) ha)
    have hp : parent ∈ domain := by
      refine ⟨parentPerm, ?_, before.length, ?_, cutFacts⟩
      · intro hdec
        have hs : [low, high].Sublist middleWord :=
          (List.singleton_sublist.mpr hl).append (List.singleton_sublist.mpr hh)
        have hd := List.pairwise_iff_forall_sublist.mp hdec (hs.map unlabel)
        have := mbounds low (List.mem_append_left _ hl)
        have := mbounds high (List.mem_append_right _ hh)
        dsimp [unlabel] at hd; omega
      · have hn := hm.length_eq
        simp [List.length_append] at hn
        dsimp [width]; omega
    have chosenCut : Classical.choose hp.2.2 = before.length :=
      uniqueCut parent hp _ _ (Classical.choose_spec hp.2.2).2 cutFacts
    have parts : (parent.take before.length).map relabel = before ∧
        (parent.drop before.length).map relabel = after := by
      have htake := congrArg (List.take before.length) restore
      have hdrop := congrArg (List.drop before.length) restore
      simpa [middleWord, ← List.map_take, ← List.map_drop] using And.intro htake hdrop
    refine ⟨parent, hp, ?_⟩
    simp only [emit, chosenCut, parts.1, parts.2]
    simpa only [lower, upper, List.cons_append, List.append_assoc] using
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

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscendingSplit
