/- GID: D5/S3/Combinatorics/PopStack/PopStackReconstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackReconstruction
   mirror-E: none(waiver:interval-contraction-inverse)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Interval contraction constructs inverse inflation and a simple covered quotient. -/

import D5.S3.Combinatorics.PopStack.PopStackInflation
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackReconstruction

open PopStackDefs PopStackInflation

theorem reconstruct_interval (before values after : List ℕ) (lower : ℕ)
    (hperm : (before ++ values ++ after).Perm
      (List.range' 1 (before ++ values ++ after).length))
    (hvalues : values.Perm (List.range' lower values.length)) (hnonempty : 1 ≤ values.length) :
    ∃ skeleton block : List ℕ,
      skeleton.Perm (List.range' 1 skeleton.length) ∧
      block.Perm (List.range' 1 block.length) ∧
      skeleton.length = before.length + 1 + after.length ∧
      block.length = values.length ∧
      inflate skeleton before.length block = before ++ values ++ after ∧
      ((∀ index size bottom, 2 ≤ size → size < (before ++ values ++ after).length →
        index + size ≤ (before ++ values ++ after).length →
        (((before ++ values ++ after).drop index).take size).Perm
          (List.range' bottom size) →
        before.length ≤ index ∧ index + size ≤ before.length + values.length) →
        Occurs skeleton (before ++ values ++ after) ∧ IsSimple skeleton ∧
          (InC (before ++ values ++ after) → InC skeleton)) := by
  have hcontract (skeleton block : List ℕ) (blockIndex : ℕ)
      (hperm : skeleton.Perm (List.range' 1 skeleton.length))
      (hindex : blockIndex < skeleton.length)
      (hblock : block.Perm (List.range' 1 block.length)) (hnonempty : 1 ≤ block.length)
      (hcovered : ∀ index size lower, 2 ≤ size →
        size < (inflate skeleton blockIndex block).length →
        index + size ≤ (inflate skeleton blockIndex block).length →
        (((inflate skeleton blockIndex block).drop index).take size).Perm
          (List.range' lower size) →
        blockIndex ≤ index ∧ index + size ≤ blockIndex + block.length) :
      Occurs skeleton (inflate skeleton blockIndex block) ∧ IsSimple skeleton := by
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    let pivot := skeleton.getD blockIndex 0
    let shift := fun value => if pivot < value then value + block.length - 1 else value
    let blockValues := block.map (fun value => pivot + value - 1)
    let replace := fun value => if value = pivot then blockValues else [shift value]
    let sortedReplace := fun value =>
      if value = pivot then List.range' pivot block.length else [shift value]
    have hblockValues : blockValues.Perm (List.range' pivot block.length) := by
      have hmap := hblock.map (fun value => pivot + value - 1)
      have hrange : ∀ size,
          (List.range' 1 size).map (fun value => pivot + value - 1) =
            List.range' pivot size := by
        intro size
        have hh : (List.range' 1 size).map (fun value => pivot + value - 1) =
            (List.range size).map (fun value => pivot + value) := by
          rw [List.range'_eq_map_range, List.map_map]
          apply List.map_congr_left
          intro value _
          simp only [Function.comp_apply]
          omega
        rw [hh, List.range'_eq_map_range]
      simpa only [blockValues, hrange] using hmap
    have hreplacePerm : ∀ value, (replace value).Perm (sortedReplace value) := by
      intro value
      dsimp [replace, sortedReplace]
      split
      · exact hblockValues
      · exact List.Perm.refl _
    have hsingletons : ∀ segment : List ℕ, pivot ∉ segment →
        segment.flatMap replace = segment.map shift := by
      intro segment hmissing
      induction segment with
      | nil => rfl
      | cons value segment ih =>
        have hn : value ≠ pivot := by intro heq; apply hmissing; simp [heq]
        simp only [List.flatMap_cons, replace, if_neg hn, List.singleton_append,
          List.map_cons, ih (fun hm => hmissing (List.mem_cons_of_mem value hm))]
    have hdecompose : skeleton = skeleton.take blockIndex ++
        pivot :: skeleton.drop (blockIndex + 1) := by
      have hget : skeleton[blockIndex]? = some pivot := by
        simp [pivot, List.getD_eq_getElem?_getD, hindex]
      calc
        skeleton = skeleton.take blockIndex ++ skeleton.drop blockIndex :=
          (List.take_append_drop blockIndex skeleton).symm
        _ = skeleton.take blockIndex ++ pivot :: skeleton.drop (blockIndex + 1) := by
          conv_lhs => rhs; rw [List.drop_eq_getElem?_toList_append, hget]
          simp
    have hmissing : pivot ∉ skeleton.take blockIndex ∧
        pivot ∉ skeleton.drop (blockIndex + 1) := by
      rw [hdecompose] at hnodup
      simp only [List.nodup_append, List.nodup_cons] at hnodup
      exact ⟨fun hm => hnodup.2.2 pivot hm pivot (by simp) rfl, hnodup.2.1.1⟩
    have hflat : skeleton.flatMap replace = inflate skeleton blockIndex block := by
      conv_lhs => rw [hdecompose]
      simp only [List.flatMap_append, List.flatMap_cons, replace, ite_true,
        hsingletons _ hmissing.1, hsingletons _ hmissing.2]
      simp only [inflate, shift, pivot, blockValues, List.append_assoc]
    have hnonshrinking : ∀ segment : List ℕ,
        segment.length ≤ (segment.flatMap replace).length := by
      intro segment
      induction segment with
      | nil => simp
      | cons value segment ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have hh : 1 ≤ (replace value).length := by
          dsimp [replace]
          split
          · simpa only [blockValues, List.length_map] using hnonempty
          · simp
        omega
    have hnormalized : ∀ lower size,
        (List.range' lower size).flatMap sortedReplace =
          List.range' (if pivot < lower then lower + block.length - 1 else lower)
            (size + if lower ≤ pivot ∧ pivot < lower + size then block.length - 1 else 0) := by
      intro lower size
      induction size generalizing lower with
      | zero => simp
      | succ size ih =>
        rw [List.range'_succ, List.flatMap_cons, ih]
        by_cases hbelow : lower < pivot
        · have hsame : (lower + 1 ≤ pivot ∧ pivot < lower + 1 + size) ↔
              (lower ≤ pivot ∧ pivot < lower + (size + 1)) := by omega
          simp only [sortedReplace, if_neg (show lower ≠ pivot by omega), shift,
            if_neg (show ¬ pivot < lower by omega),
            if_neg (show ¬ pivot < lower + 1 by omega), hsame, List.singleton_append]
          rw [Nat.add_right_comm size 1, List.range'_succ]
        · by_cases heq : lower = pivot
          · subst lower
            simp only [sortedReplace, if_pos rfl,
              if_pos (show pivot < pivot + 1 by omega),
              if_neg (show ¬ pivot < pivot by omega),
              if_neg (show ¬ (pivot + 1 ≤ pivot ∧ pivot < pivot + 1 + size) by omega),
              if_pos (show pivot ≤ pivot ∧ pivot < pivot + (size + 1) by omega),
              Nat.add_zero]
            rw [show pivot + 1 + block.length - 1 = pivot + block.length by omega,
              List.range'_append_1]
            congr 1
            omega
          · have habove : pivot < lower := by omega
            simp only [sortedReplace, if_neg heq, shift, if_pos habove,
              if_pos (show pivot < lower + 1 by omega),
              if_neg (show ¬ (lower + 1 ≤ pivot ∧ pivot < lower + 1 + size) by omega),
              if_neg (show ¬ (lower ≤ pivot ∧ pivot < lower + (size + 1)) by omega),
              Nat.add_zero, List.singleton_append]
            rw [List.range'_succ]
            congr 2
            omega
    constructor
    · have hpivot : pivot ∈ blockValues := hblockValues.mem_iff.mpr
        (List.mem_range'_1.mpr ⟨le_rfl, by omega⟩)
      have hmap : skeleton.map shift = (skeleton.take blockIndex).map shift ++
          [pivot] ++ (skeleton.drop (blockIndex + 1)).map shift := by
        conv_lhs => rw [hdecompose]
        simp [List.map_append, shift, List.append_assoc]
      have hsub : (skeleton.map shift).Sublist (inflate skeleton blockIndex block) := by
        rw [hmap]
        change ((skeleton.take blockIndex).map shift ++ [pivot] ++
          (skeleton.drop (blockIndex + 1)).map shift).Sublist
            ((skeleton.take blockIndex).map shift ++ blockValues ++
              (skeleton.drop (blockIndex + 1)).map shift)
        exact ((List.Sublist.refl _).append (List.singleton_sublist.mpr hpivot)).append
          (List.Sublist.refl _)
      refine ⟨shift, ?_, ?_, hsub, by simp⟩
      · intro rank _ _
        dsimp [shift]
        split_ifs <;> omega
      · intro rank hlower hupper
        have hm : rank ∈ skeleton :=
          hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hlower, by omega⟩)
        exact hsub.subset (List.mem_map_of_mem hm)
    intro index size lower hsize hproper hbound hinterval
    let beforeList := skeleton.take index
    let segment := (skeleton.drop index).take size
    let afterList := skeleton.drop (index + size)
    have hsplit : skeleton = beforeList ++ segment ++ afterList := by
      dsimp [beforeList, segment, afterList]
      rw [← List.drop_drop]
      conv_lhs => rw [← List.take_append_drop index skeleton]
      conv_lhs => rhs; rw [← List.take_append_drop size (skeleton.drop index)]
      rw [List.append_assoc]
    have hsplitFlat : inflate skeleton blockIndex block =
        beforeList.flatMap replace ++ segment.flatMap replace ++ afterList.flatMap replace := by
      rw [← hflat]
      conv_lhs => rw [hsplit]
      simp only [List.flatMap_append, List.append_assoc]
    have hsegmentLength : segment.length = size := by
      simp only [segment, List.length_take, List.length_drop]
      omega
    have hsizeNew : 2 ≤ (segment.flatMap replace).length := by
      have hh := hnonshrinking segment
      omega
    have hproperNew : (segment.flatMap replace).length <
        (inflate skeleton blockIndex block).length := by
      have hb := hnonshrinking beforeList
      have ha := hnonshrinking afterList
      have htotal := congrArg List.length hsplit
      simp only [List.length_append] at htotal
      rw [hsplitFlat]
      simp only [List.length_append]
      omega
    have hboundNew : (beforeList.flatMap replace).length + (segment.flatMap replace).length ≤
        (inflate skeleton blockIndex block).length := by
      rw [hsplitFlat]
      simp only [List.length_append]
      omega
    have hslice : ((inflate skeleton blockIndex block).drop
        (beforeList.flatMap replace).length).take (segment.flatMap replace).length =
        segment.flatMap replace := by
      rw [hsplitFlat]
      simp [List.append_assoc]
    have hnewInterval : (segment.flatMap replace).Perm
        (List.range' (if pivot < lower then lower + block.length - 1 else lower)
          (size + if lower ≤ pivot ∧ pivot < lower + size then block.length - 1 else 0)) := by
      have hh := hinterval.flatMap (fun value _ => hreplacePerm value)
      simpa only [hnormalized] using hh
    have hnewLength := hnewInterval.length_eq
    simp only [List.length_range'] at hnewLength
    have hh := hcovered (beforeList.flatMap replace).length (segment.flatMap replace).length
      (if pivot < lower then lower + block.length - 1 else lower) hsizeNew hproperNew
      hboundNew (by rw [hslice, hnewLength]; exact hnewInterval)
    have hinside : ∀ value ∈ segment.flatMap replace,
        pivot ≤ value ∧ value < pivot + block.length := by
      intro value hmem
      rw [← hslice] at hmem
      obtain ⟨offset, hget⟩ := List.mem_iff_getElem?.mp hmem
      have hoffset : offset < (segment.flatMap replace).length := by
        obtain ⟨hgetbound, _⟩ := List.getElem?_eq_some_iff.mp hget
        have hb : offset < min (segment.flatMap replace).length
            ((inflate skeleton blockIndex block).length -
              (beforeList.flatMap replace).length) := by simpa using hgetbound
        omega
      rw [List.getElem?_take_of_lt hoffset, List.getElem?_drop] at hget
      let position := (beforeList.flatMap replace).length + offset
      change (((skeleton.take blockIndex).map shift) ++
        blockValues ++ (skeleton.drop (blockIndex + 1)).map shift)[position]? = some value at hget
      rw [List.append_assoc, List.getElem?_append_right (by
        simp only [List.length_map, List.length_take]
        dsimp [position]
        omega)] at hget
      have hbefore : ((skeleton.take blockIndex).map shift).length = blockIndex := by
        simp only [List.length_map, List.length_take]
        omega
      rw [hbefore, List.getElem?_append_left (by
        simp only [blockValues, List.length_map]
        dsimp [position]
        omega)] at hget
      exact List.mem_range'_1.mp (hblockValues.mem_iff.mp (List.mem_of_getElem? hget))
    let newLower := if pivot < lower then lower + block.length - 1 else lower
    have hbottom : newLower ∈ segment.flatMap replace := hnewInterval.mem_iff.mpr
      (List.mem_range'_1.mpr ⟨by omega, by rw [← hnewLength]; omega⟩)
    have htop : newLower + (segment.flatMap replace).length - 1 ∈
        segment.flatMap replace := hnewInterval.mem_iff.mpr
      (List.mem_range'_1.mpr ⟨by omega, by rw [← hnewLength]; omega⟩)
    have hbottomBound := hinside newLower hbottom
    have htopBound := hinside _ htop
    dsimp [newLower] at hbottomBound htopBound
    rw [hnewLength] at htopBound
    split_ifs at hbottomBound htopBound <;> omega
  let whole := before ++ values ++ after
  let outside := before ++ after
  let down := fun value => if value < lower then value else value + 1 - values.length
  let skeleton := before.map down ++ lower :: after.map down
  let block := values.map (fun value => value - lower + 1)
  change whole.Perm (List.range' 1 whole.length) at hperm
  have hwholeLength : whole.length = before.length + values.length + after.length := by
    simp [whole, Nat.add_assoc]
  have hnodup : whole.Nodup := hperm.nodup_iff.mpr (List.nodup_range' _)
  have houtsideSub : outside.Sublist whole := by
    simpa only [outside, whole, List.append_assoc] using
      (List.Sublist.refl before).append (List.sublist_append_right values after)
  have hvaluesSub : values.Sublist whole := by
    exact (List.sublist_append_left values after).trans
      (by simpa only [whole, List.append_assoc] using
        List.sublist_append_right before (values ++ after))
  have hwholeBounds : ∀ value ∈ whole, 1 ≤ value ∧ value ≤ whole.length := by
    intro value hvalue
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hvalue)
    omega
  have hlowerMem : lower ∈ values :=
    hvalues.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
  have hlastMem : lower + values.length - 1 ∈ values :=
    hvalues.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
  have hlowerBound := hwholeBounds lower (hvaluesSub.subset hlowerMem)
  have hlastBound := hwholeBounds _ (hvaluesSub.subset hlastMem)
  have hseparate : ∀ value ∈ outside, value < lower ∨ lower + values.length ≤ value := by
    intro value hvalue
    by_contra hnot
    have hin : value ∈ values := hvalues.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
    have hsplit := List.nodup_append.mp hnodup
    rcases List.mem_append.mp hvalue with hbefore | hafter
    · exact (List.nodup_append.mp hsplit.1).2.2 value hbefore value hin rfl
    · exact hsplit.2.2 value (List.mem_append_right before hin) value hafter rfl
  have hinjective : ∀ first ∈ outside, ∀ second ∈ outside,
      down first = down second → first = second := by
    intro first hfirst second hsecond heq
    have hfirstRange := hseparate first hfirst
    have hsecondRange := hseparate second hsecond
    dsimp [down] at heq
    split_ifs at heq <;> omega
  have hnotPivot : ∀ value ∈ outside, down value ≠ lower := by
    intro value hvalue heq
    have hh := hseparate value hvalue
    dsimp [down] at heq
    split_ifs at heq <;> omega
  have houtsideNodup := List.nodup_append.mp (hnodup.sublist houtsideSub)
  have hbeforeNodup : (before.map down).Nodup :=
    houtsideNodup.1.map_on (fun first hfirst second hsecond =>
      hinjective first (List.mem_append_left after hfirst)
        second (List.mem_append_left after hsecond))
  have hafterNodup : (after.map down).Nodup :=
    houtsideNodup.2.1.map_on (fun first hfirst second hsecond =>
      hinjective first (List.mem_append_right before hfirst)
        second (List.mem_append_right before hsecond))
  have hskeletonNodup : skeleton.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hbeforeNodup, List.nodup_cons.mpr ⟨?_, hafterNodup⟩, ?_⟩
    · intro hpivot
      obtain ⟨value, hvalue, heq⟩ := List.mem_map.mp hpivot
      exact hnotPivot value (List.mem_append_right before hvalue) heq
    · intro first hfirst second hsecond heq
      obtain ⟨oldFirst, hOldFirst, rfl⟩ := List.mem_map.mp hfirst
      rcases List.mem_cons.mp hsecond with rfl | hsecond
      · exact hnotPivot oldFirst (List.mem_append_left after hOldFirst) heq
      · obtain ⟨oldSecond, hOldSecond, rfl⟩ := List.mem_map.mp hsecond
        exact houtsideNodup.2.2 oldFirst hOldFirst oldSecond hOldSecond
          (hinjective oldFirst (List.mem_append_left after hOldFirst)
            oldSecond (List.mem_append_right before hOldSecond) heq)
  have hlength : skeleton.length = before.length + 1 + after.length := by
    simp [skeleton]
    omega
  have hdownBounds : ∀ value ∈ outside,
      1 ≤ down value ∧ down value ≤ skeleton.length := by
    intro value hvalue
    have hh := hwholeBounds value (houtsideSub.subset hvalue)
    have hsep := hseparate value hvalue
    dsimp [down]
    split_ifs <;> simp only [whole, List.length_append] at hh hlowerBound hlastBound <;> omega
  have hsurjective : ∀ value, 1 ≤ value → value ≤ skeleton.length →
      value ∈ skeleton := by
    intro value hpositive hbound
    by_cases heq : value = lower
    · simp [skeleton, heq]
    · let old := if value < lower then value else value + values.length - 1
      have holdBounds : 1 ≤ old ∧ old ≤ whole.length := by
        dsimp [old, whole]
        simp only [List.length_append]
        split_ifs <;> omega
      have holdMem : old ∈ whole :=
        hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      have holdNotValues : old ∉ values := by
        intro hmem
        have hh := List.mem_range'_1.mp (hvalues.mem_iff.mp hmem)
        dsimp [old] at hh
        split_ifs at hh <;> omega
      have holdOutside : old ∈ outside := by
        simp only [whole, List.mem_append] at holdMem
        simp only [outside, List.mem_append]
        tauto
      have hdownOld : down old = value := by
        dsimp [down, old]
        split_ifs <;> omega
      have hmapMem : value ∈ outside.map down := by
        exact List.mem_map.mpr ⟨old, holdOutside, hdownOld⟩
      simp only [outside, List.map_append, List.mem_append] at hmapMem
      simp only [skeleton, List.mem_append, List.mem_cons]
      tauto
  have hskeletonPerm : skeleton.Perm (List.range' 1 skeleton.length) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hskeletonNodup (List.nodup_range' _)
    apply Finset.ext
    intro value
    simp only [List.mem_toFinset, List.mem_range'_1]
    constructor
    · intro hvalue
      simp only [skeleton, List.mem_append, List.mem_cons] at hvalue
      rcases hvalue with hbefore | rfl | hafter
      · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hbefore
        have hh := hdownBounds old (List.mem_append_left after hold)
        omega
      · omega
      · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hafter
        have hh := hdownBounds old (List.mem_append_right before hold)
        omega
    · intro hvalue
      exact hsurjective value hvalue.1 (by omega)
  have hblockPerm : block.Perm (List.range' 1 block.length) := by
    have hh := hvalues.map (fun value => value - lower + 1)
    have hrange : (List.range' lower values.length).map (fun value => value - lower + 1) =
        List.range' 1 values.length := by
      simp only [List.range'_eq_map_range, List.map_map]
      apply List.map_congr_left
      intro value _
      simp only [Function.comp_apply]
      omega
    simpa only [block, List.length_map, hrange] using hh
  have hpivot : skeleton.getD before.length 0 = lower := by
    simp [skeleton, List.getD_eq_getElem?_getD]
  have htake : skeleton.take before.length = before.map down := by
    simp [skeleton]
  have hdrop : skeleton.drop (before.length + 1) = after.map down := by
    simp [skeleton, List.drop_append]
  have hrecover : ∀ value ∈ outside,
      (if lower < down value then down value + block.length - 1 else down value) = value := by
    intro value hvalue
    have hh := hseparate value hvalue
    simp only [block, List.length_map]
    dsimp [down]
    split_ifs <;> omega
  have hblockRecover : block.map (fun value => lower + value - 1) = values := by
    simp only [block, List.map_map]
    calc
      _ = values.map id := by
        apply List.map_congr_left
        intro value hvalue
        have hh := List.mem_range'_1.mp (hvalues.mem_iff.mp hvalue)
        simp only [Function.comp_apply, id_eq]
        omega
      _ = values := List.map_id _
  have hinflate : inflate skeleton before.length block = whole := by
    simp only [inflate, hpivot, htake, hdrop, List.map_map, hblockRecover,
      Function.comp_def]
    have hbefore : before.map
        (fun value => if lower < down value then down value + block.length - 1
          else down value) = before := by
      calc
        _ = before.map id := by
          apply List.map_congr_left
          intro value hvalue
          exact hrecover value (List.mem_append_left after hvalue)
        _ = before := List.map_id _
    have hafter : after.map
        (fun value => if lower < down value then down value + block.length - 1
          else down value) = after := by
      calc
        _ = after.map id := by
          apply List.map_congr_left
          intro value hvalue
          exact hrecover value (List.mem_append_right before hvalue)
        _ = after := List.map_id _
    simp only [hbefore, hafter, whole, List.append_assoc]
  refine ⟨skeleton, block, hskeletonPerm, hblockPerm, hlength,
    by simp [block], hinflate, ?_⟩
  intro hcovered
  have hblockLength : block.length = values.length := by simp [block]
  have hcoveredInflation : ∀ index size bottom, 2 ≤ size →
      size < (inflate skeleton before.length block).length →
      index + size ≤ (inflate skeleton before.length block).length →
      (((inflate skeleton before.length block).drop index).take size).Perm
        (List.range' bottom size) →
      before.length ≤ index ∧ index + size ≤ before.length + block.length := by
    simpa only [hinflate, hblockLength] using hcovered
  obtain ⟨hoccurs, hsimple⟩ := hcontract skeleton block before.length
    hskeletonPerm (by omega) hblockPerm (by omega) hcoveredInflation
  rw [hinflate] at hoccurs
  refine ⟨hoccurs, hsimple, ?_⟩
  intro hclass
  obtain ⟨outer, houterInc, houterMem, houterSub, _⟩ := hoccurs
  have houterStrict : ∀ upper bottom, 1 ≤ bottom → bottom < upper →
      upper ≤ skeleton.length → outer bottom < outer upper := by
    intro upper
    induction upper with
    | zero => intro bottom _ hlt _; omega
    | succ upper ih =>
      intro bottom hpositive hlt hbound
      by_cases heq : bottom = upper
      · subst bottom
        exact houterInc upper hpositive (by omega)
      · exact lt_trans (ih bottom hpositive (by omega) (by omega))
          (houterInc upper (by omega) (by omega))
  intro forbidden hforbidden hcontained
  obtain ⟨inner, hinnerInc, hinnerMem, hinnerSub, _⟩ := hcontained
  have hinnerBounds : ∀ rank, 1 ≤ rank → rank ≤ forbidden.length →
      1 ≤ inner rank ∧ inner rank ≤ skeleton.length := by
    intro rank hpositive hbound
    have hh := List.mem_range'_1.mp
      (hskeletonPerm.mem_iff.mp (hinnerMem rank hpositive hbound))
    omega
  apply hclass forbidden hforbidden
  refine ⟨fun rank => outer (inner rank), ?_, ?_, ?_, by simp⟩
  · intro rank hpositive hbound
    have hfirst := hinnerBounds rank hpositive hbound.le
    have hsecond := hinnerBounds (rank + 1) (by omega) (by omega)
    exact houterStrict (inner (rank + 1)) (inner rank) hfirst.1
      (hinnerInc rank hpositive hbound) hsecond.2
  · intro rank hpositive hbound
    have hh := hinnerBounds rank hpositive hbound
    exact houterMem (inner rank) hh.1 hh.2
  · simpa only [List.map_map, Function.comp_def] using
      (hinnerSub.map outer).trans houterSub

end D5.S3.Combinatorics.PopStack.PopStackReconstruction
