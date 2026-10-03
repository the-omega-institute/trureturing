/- GID: D5/S3/Combinatorics/PopStack/PopStackPrime
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackPrime
   mirror-E: none(waiver:prime-inflation-interval-classification)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: Every proper nontrivial interval of a prime inflation lies inside its inflated block. -/

import D5.S3.Combinatorics.PopStack.PopStackInflation
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackPrime

open PopStackDefs PopStackInflation

theorem inflation_intervals (skeleton block : List ℕ) (blockIndex : ℕ)
    (hperm : skeleton.Perm (List.range' 1 skeleton.length))
    (hsimple : IsSimple skeleton) (hlength : 4 ≤ skeleton.length)
    (hindex : blockIndex < skeleton.length)
    (hblock : block.Perm (List.range' 1 block.length)) (hblockLength : 1 ≤ block.length) :
    (∀ index size lower, 2 ≤ size → size < (inflate skeleton blockIndex block).length →
      index + size ≤ (inflate skeleton blockIndex block).length →
      (((inflate skeleton blockIndex block).drop index).take size).Perm
        (List.range' lower size) →
      blockIndex ≤ index ∧ index + size ≤ blockIndex + block.length) ∧
    (∀ start size lower, start + size ≤ block.length → 1 ≤ lower →
      ((block.drop start).take size).Perm (List.range' lower size) →
      (((inflate skeleton blockIndex block).drop (blockIndex + start)).take size).Perm
        (List.range' (skeleton.getD blockIndex 0 + lower - 1) size)) := by
  refine ⟨?_, ?_⟩
  swap
  · intro start size lower hbound hpositive hinterval
    let pivot := skeleton.getD blockIndex 0
    let shift := fun value => pivot + value - 1
    let up := fun value => if pivot < value then value + block.length - 1 else value
    let before := (skeleton.take blockIndex).map up
    let after := (skeleton.drop (blockIndex + 1)).map up
    have hbefore : before.length = blockIndex := by
      simp only [before, List.length_map, List.length_take]
      omega
    have hsegment : (((inflate skeleton blockIndex block).drop
        (blockIndex + start)).take size) = ((block.drop start).take size).map shift := by
      change (((before ++ block.map shift ++ after).drop
        (blockIndex + start)).take size) = _
      rw [List.append_assoc, List.drop_append,
        List.drop_eq_nil_iff.mpr (by omega), List.nil_append, hbefore,
        Nat.add_sub_cancel_left,
        List.drop_append_of_le_length (by simp only [List.length_map]; omega),
        List.take_append_of_le_length (by
          simp only [List.length_drop, List.length_map]; omega),
        ← List.map_drop, ← List.map_take]
    have hrange : (List.range' lower size).map shift =
        List.range' (pivot + lower - 1) size := by
      simp only [List.range'_eq_map_range, List.map_map]
      apply List.map_congr_left
      intro offset _
      dsimp only [Function.comp_def, shift]
      omega
    rw [hsegment]
    simpa only [hrange] using hinterval.map shift
  let pivot := skeleton.getD blockIndex 0
  let up := fun value => if pivot < value then value + block.length - 1 else value
  let down := fun value => if value < pivot then value
    else if value < pivot + block.length then pivot else value + 1 - block.length
  let positionQ := fun position => if position < blockIndex then position
    else if position < blockIndex + block.length then blockIndex
    else position + 1 - block.length
  let expanded := inflate skeleton blockIndex block
  have hnodup := hperm.nodup_iff.mpr (List.nodup_range' _)
  have hgetMem : ∀ position, position < skeleton.length →
      skeleton.getD position 0 ∈ skeleton := by
    intro position hposition
    rw [List.getD_eq_getElem _ _ hposition]
    exact List.getElem_mem hposition
  have hvalueBounds : ∀ value ∈ skeleton, 1 ≤ value ∧ value ≤ skeleton.length := by
    intro value hvalue
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hvalue)
    omega
  have hpivotBounds := hvalueBounds pivot (hgetMem blockIndex hindex)
  have hbeforeLength : ((skeleton.take blockIndex).map up).length = blockIndex := by
    simp only [List.length_map, List.length_take]
    omega
  have hexpandedLength : expanded.length = skeleton.length + block.length - 1 := by
    simp only [expanded, inflate, List.length_append, List.length_map,
      List.length_take, List.length_drop]
    omega
  have hget : ∀ position, position < expanded.length → expanded[position]? =
      if position < blockIndex then (skeleton[position]?).map up
      else if position < blockIndex + block.length then
        (block[position - blockIndex]?).map (fun value => pivot + value - 1)
      else (skeleton[position + 1 - block.length]?).map up := by
    intro position hposition
    change (((skeleton.take blockIndex).map up) ++
      block.map (fun value => pivot + value - 1) ++
      (skeleton.drop (blockIndex + 1)).map up)[position]? = _
    rw [List.append_assoc]
    by_cases hbefore : position < blockIndex
    · rw [if_pos hbefore, List.getElem?_append_left (by omega), List.getElem?_map,
        List.getElem?_take_of_lt hbefore]
    · rw [if_neg hbefore, List.getElem?_append_right (by omega), hbeforeLength]
      by_cases hinside : position < blockIndex + block.length
      · rw [if_pos hinside, List.getElem?_append_left (by simp; omega), List.getElem?_map]
      · rw [if_neg hinside, List.getElem?_append_right (by simp; omega)]
        simp only [List.length_map, List.getElem?_map, List.getElem?_drop]
        congr 2
        omega
  have hpositionBound : ∀ position, position < expanded.length →
      positionQ position < skeleton.length := by
    intro position hposition
    dsimp [positionQ]
    split_ifs <;> omega
  have hpositionMono : ∀ first second, first ≤ second →
      positionQ first ≤ positionQ second := by
    intro first second hle
    dsimp [positionQ]
    split_ifs <;> omega
  have hdownUp : ∀ value, down (up value) = value := by
    intro value
    dsimp [up, down]
    split_ifs <;> omega
  have hgetProjection : ∀ position, position < expanded.length →
      down (expanded.getD position 0) = skeleton.getD (positionQ position) 0 := by
    intro position hposition
    rw [List.getD_eq_getElem?_getD, hget position hposition]
    by_cases hbefore : position < blockIndex
    · rw [if_pos hbefore]
      have hbound : position < skeleton.length := by omega
      have hsome : skeleton[position]? = some (skeleton.getD position 0) := by
        rw [List.getD_eq_getElem _ _ hbound, List.getElem?_eq_getElem hbound]
      simp only [hsome, Option.map_some, Option.getD_some, hdownUp]
      simp only [positionQ, if_pos hbefore]
    · rw [if_neg hbefore]
      by_cases hinside : position < blockIndex + block.length
      · rw [if_pos hinside]
        have hbound : position - blockIndex < block.length := by omega
        have hsome : block[position - blockIndex]? =
            some (block.getD (position - blockIndex) 0) := by
          rw [List.getD_eq_getElem _ _ hbound, List.getElem?_eq_getElem hbound]
        have hmem : block.getD (position - blockIndex) 0 ∈ block := by
          rw [List.getD_eq_getElem _ _ hbound]
          exact List.getElem_mem hbound
        have hh := List.mem_range'_1.mp (hblock.mem_iff.mp hmem)
        simp only [hsome, Option.map_some, Option.getD_some,
          positionQ, if_neg hbefore, if_pos hinside]
        change down (pivot + block.getD (position - blockIndex) 0 - 1) = pivot
        dsimp [down]
        split_ifs <;> omega
      · rw [if_neg hinside]
        have hbound : position + 1 - block.length < skeleton.length := by omega
        have hsome : skeleton[position + 1 - block.length]? =
            some (skeleton.getD (position + 1 - block.length) 0) := by
          rw [List.getD_eq_getElem _ _ hbound, List.getElem?_eq_getElem hbound]
        simp only [hsome, Option.map_some, Option.getD_some, hdownUp,
          positionQ, if_neg hbefore, if_neg hinside]
  have hgetOutside : ∀ position, position < expanded.length →
      positionQ position ≠ blockIndex →
      expanded.getD position 0 = up (skeleton.getD (positionQ position) 0) := by
    intro position hposition hnotPivot
    rw [List.getD_eq_getElem?_getD, hget position hposition]
    dsimp [positionQ] at hnotPivot ⊢
    split_ifs at hnotPivot ⊢
    · have hbound : position < skeleton.length := by omega
      rw [List.getD_eq_getElem _ _ hbound, List.getElem?_eq_getElem hbound]
      rfl
    · contradiction
    · have hbound : position + 1 - block.length < skeleton.length := by omega
      rw [List.getD_eq_getElem _ _ hbound, List.getElem?_eq_getElem hbound]
      rfl
  have hsliceMem : ∀ (permutation : List ℕ) start count,
      start + count ≤ permutation.length →
      ∀ value, value ∈ (permutation.drop start).take count ↔
        ∃ position, start ≤ position ∧ position < start + count ∧
          permutation.getD position 0 = value := by
    intro permutation start count hbound value
    have hsliceLength : ((permutation.drop start).take count).length = count := by
      simp only [List.length_take, List.length_drop]
      omega
    constructor
    · intro hmem
      obtain ⟨offset, hgetValue⟩ := List.mem_iff_getElem?.mp hmem
      have hoffset : offset < count := by
        have hh := (List.getElem?_eq_some_iff.mp hgetValue).1
        omega
      rw [List.getElem?_take_of_lt hoffset, List.getElem?_drop] at hgetValue
      refine ⟨start + offset, by omega, by omega, ?_⟩
      simp only [List.getD_eq_getElem?_getD, hgetValue, Option.getD_some]
    · rintro ⟨position, hstart, hend, hgetValue⟩
      apply List.mem_iff_getElem?.mpr
      refine ⟨position - start, ?_⟩
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        Nat.add_sub_of_le hstart]
      have hposition : position < permutation.length := by omega
      rw [List.getElem?_eq_getElem hposition]
      congr 1
      exact (List.getD_eq_getElem _ _ hposition).symm.trans hgetValue
  have hdownMono : ∀ first second, first ≤ second → down first ≤ down second := by
    intro first second hle
    dsimp [down]
    split_ifs <;> omega
  have hdownFiber : ∀ bottom top value, bottom ≤ top →
      down bottom ≤ value → value ≤ down top →
      ∃ original, bottom ≤ original ∧ original ≤ top ∧ down original = value := by
    intro bottom top value hle hbottom htop
    by_cases hsmall : value < pivot
    · refine ⟨value, ?_, ?_, ?_⟩
      · dsimp [down] at hbottom
        split_ifs at hbottom <;> omega
      · dsimp [down] at htop
        split_ifs at htop <;> omega
      · simp [down, hsmall]
    · by_cases heq : value = pivot
      · subst value
        refine ⟨max bottom pivot, by omega, ?_, ?_⟩
        · dsimp [down] at htop
          split_ifs at htop <;> omega
        · dsimp [down] at hbottom ⊢
          split_ifs at hbottom ⊢ <;> omega
      · refine ⟨value + block.length - 1, ?_, ?_, ?_⟩
        · dsimp [down] at hbottom
          split_ifs at hbottom <;> omega
        · dsimp [down] at htop
          split_ifs at htop <;> omega
        · dsimp [down]
          split_ifs <;> omega
  intro index size lower hsize hproper hbound hinterval
  change size < expanded.length at hproper
  change index + size ≤ expanded.length at hbound
  change ((expanded.drop index).take size).Perm (List.range' lower size) at hinterval
  by_contra hnotInside
  let startQ := positionQ index
  let endQ := positionQ (index + size - 1) + 1
  let countQ := endQ - startQ
  have hstartEnd : startQ < endQ := by
    have hh := hpositionMono index (index + size - 1) (by omega)
    dsimp [startQ, endQ]
    omega
  have hendBound : endQ ≤ skeleton.length := by
    have hh := hpositionBound (index + size - 1) (by omega)
    dsimp [endQ]
    omega
  have hcountBound : startQ + countQ ≤ skeleton.length := by
    dsimp [countQ]
    omega
  have hpositionFiber : ∀ original, startQ ≤ original → original < endQ →
      ∃ position, index ≤ position ∧ position < index + size ∧
        positionQ position = original := by
    intro original hstart hend
    dsimp [startQ, endQ, positionQ] at hstart hend
    by_cases hbefore : original < blockIndex
    · refine ⟨original, ?_, ?_, ?_⟩
      · split_ifs at hstart <;> omega
      · split_ifs at hend <;> omega
      · simp [positionQ, hbefore]
    · by_cases heq : original = blockIndex
      · subst original
        refine ⟨max index blockIndex, by omega, ?_, ?_⟩
        · split_ifs at hend <;> omega
        · dsimp [positionQ]
          split_ifs at hstart ⊢ <;> omega
      · refine ⟨original + block.length - 1, ?_, ?_, ?_⟩
        · split_ifs at hstart <;> omega
        · split_ifs at hend <;> omega
        · dsimp [positionQ]
          split_ifs <;> omega
  have hprojectionMem : ∀ value, value ∈ (skeleton.drop startQ).take countQ ↔
      value ∈ ((expanded.drop index).take size).map down := by
    intro value
    constructor
    · intro hmem
      obtain ⟨original, hstart, hend, hvalue⟩ :=
        (hsliceMem skeleton startQ countQ hcountBound value).mp hmem
      obtain ⟨position, hfirst, hlast, hproject⟩ := hpositionFiber original hstart (by
        dsimp [countQ] at hend
        omega)
      apply List.mem_map.mpr
      refine ⟨expanded.getD position 0, ?_, ?_⟩
      · exact (hsliceMem expanded index size hbound _).mpr ⟨position, hfirst, hlast, rfl⟩
      · rw [hgetProjection position (by omega), hproject, hvalue]
    · intro hmem
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨position, hfirst, hlast, hvalue⟩ :=
        (hsliceMem expanded index size hbound old).mp hold
      apply (hsliceMem skeleton startQ countQ hcountBound _).mpr
      refine ⟨positionQ position, ?_, ?_, ?_⟩
      · exact hpositionMono index position hfirst
      · have hh := hpositionMono position (index + size - 1) (by omega)
        dsimp [countQ, endQ]
        omega
      · rw [← hgetProjection position (by omega), hvalue]
  let lowerQ := down lower
  let upperQ := down (lower + size - 1) + 1
  have hvalueImage : ∀ value, value ∈ ((expanded.drop index).take size).map down ↔
      lowerQ ≤ value ∧ value < upperQ := by
    intro value
    constructor
    · intro hmem
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hmem
      have hh := List.mem_range'_1.mp (hinterval.mem_iff.mp hold)
      have hlow := hdownMono lower old hh.1
      have hhigh := hdownMono old (lower + size - 1) (by omega)
      dsimp [lowerQ, upperQ]
      omega
    · intro hvalue
      obtain ⟨old, hlow, hhigh, heq⟩ := hdownFiber lower (lower + size - 1)
        value (by omega) hvalue.1 (by dsimp [upperQ] at hvalue; omega)
      apply List.mem_map.mpr
      exact ⟨old, hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega)), heq⟩
  have hquotientPerm : ((skeleton.drop startQ).take countQ).Perm
      (List.range' lowerQ (upperQ - lowerQ)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
      ((hnodup.sublist (List.drop_sublist startQ skeleton)).sublist
        (List.take_sublist countQ _)) (List.nodup_range' _)
    apply Finset.ext
    intro value
    simp only [List.mem_toFinset, hprojectionMem, hvalueImage, List.mem_range'_1]
    have hh := hdownMono lower (lower + size - 1) (by omega)
    dsimp [lowerQ, upperQ]
    omega
  have hquotientLength : upperQ - lowerQ = countQ := by
    have hh := hquotientPerm.length_eq
    simp only [List.length_range', List.length_take, List.length_drop] at hh
    omega
  have hcount : 2 ≤ countQ := by
    by_contra hsmall
    have heq : positionQ index = positionQ (index + size - 1) := by
      dsimp [countQ, startQ, endQ] at hsmall
      have hh := hpositionMono index (index + size - 1) (by omega)
      omega
    dsimp [positionQ] at heq
    split_ifs at heq <;> omega
  have hfull : countQ = skeleton.length := by
    by_contra hne
    exact hsimple startQ countQ lowerQ hcount (by omega) hcountBound
      (by simpa only [hquotientLength] using hquotientPerm)
  have hstartZero : startQ = 0 := by omega
  have hendFull : endQ = skeleton.length := by dsimp [countQ] at hfull; omega
  have hendpoint : blockIndex = 0 ∨ blockIndex + 1 = skeleton.length := by
    dsimp [startQ, endQ, positionQ] at hstartZero hendFull
    split_ifs at hstartZero hendFull <;> omega
  have hpivotNonextreme : pivot ≠ 1 ∧ pivot ≠ skeleton.length := by
    have hdecompose : skeleton = skeleton.take blockIndex ++
        pivot :: skeleton.drop (blockIndex + 1) := by
      have hsome : skeleton[blockIndex]? = some pivot := by
        dsimp [pivot]
        rw [List.getD_eq_getElem _ _ hindex, List.getElem?_eq_getElem hindex]
      calc
        skeleton = skeleton.take blockIndex ++ skeleton.drop blockIndex :=
          (List.take_append_drop blockIndex skeleton).symm
        _ = _ := by
          conv_lhs => rhs; rw [List.drop_eq_getElem?_toList_append, hsome]
          simp
    have hnotIn : pivot ∉ skeleton.take blockIndex ∧
        pivot ∉ skeleton.drop (blockIndex + 1) := by
      rw [hdecompose] at hnodup
      simp only [List.nodup_append, List.nodup_cons] at hnodup
      exact ⟨fun hm => hnodup.2.2 pivot hm pivot (by simp) rfl, hnodup.2.1.1⟩
    let complement := if blockIndex = 0 then skeleton.drop 1 else skeleton.take blockIndex
    have hmemDecompose : ∀ value, value ∈ skeleton ↔
        value ∈ skeleton.take blockIndex ∨ value = pivot ∨
          value ∈ skeleton.drop (blockIndex + 1) := by
      intro value
      conv_lhs => rw [hdecompose]
      simp only [List.mem_append, List.mem_cons]
    have hcomplement : ∀ value,
        value ∈ complement ↔ value ∈ skeleton ∧ value ≠ pivot := by
      intro value
      rcases hendpoint with hfirst | hlast
      · simp only [complement, hfirst, ite_true]
        have hh := hnotIn.2
        simp only [hfirst, Nat.zero_add] at hh
        have hm := hmemDecompose value
        simp only [hfirst, Nat.zero_add, List.take_zero, List.not_mem_nil, false_or] at hm
        rw [hm]
        have hne : value ∈ skeleton.drop 1 → value ≠ pivot := by
          intro hvalue heq
          exact hh (heq ▸ hvalue)
        constructor
        · intro hvalue
          exact ⟨Or.inr hvalue, hne hvalue⟩
        · rintro ⟨heq | hvalue, hnotEqual⟩
          · exact False.elim (hnotEqual heq)
          · exact hvalue
      · have hnotFirst : blockIndex ≠ 0 := by omega
        have htail : skeleton.drop (blockIndex + 1) = [] := by
          apply List.drop_eq_nil_iff.mpr
          omega
        simp only [complement, if_neg hnotFirst]
        have hh := hnotIn.1
        have hm := hmemDecompose value
        simp only [htail, List.not_mem_nil, or_false] at hm
        rw [hm]
        have hne : value ∈ skeleton.take blockIndex → value ≠ pivot := by
          intro hvalue heq
          exact hh (heq ▸ hvalue)
        constructor
        · intro hvalue
          exact ⟨Or.inl hvalue, hne hvalue⟩
        · rintro ⟨hvalue | heq, hnotEqual⟩
          · exact hvalue
          · exact False.elim (hnotEqual heq)
    have hcomplementNodup : complement.Nodup := by
      dsimp [complement]
      split
      · exact hnodup.sublist (List.drop_sublist 1 skeleton)
      · exact hnodup.sublist (List.take_sublist blockIndex skeleton)
    have hcomplementLength : complement.length = skeleton.length - 1 := by
      dsimp [complement]
      split
      · simp only [List.length_drop]
      · simp only [List.length_take]
        rcases hendpoint with hfirst | hlast
        · contradiction
        · omega
    have hcomplementSlice : complement =
        (skeleton.drop (if blockIndex = 0 then 1 else 0)).take (skeleton.length - 1) := by
      dsimp [complement]
      split
      · simp [List.take_of_length_le]
      · simp only [List.drop_zero]
        rcases hendpoint with hfirst | hlast
        · contradiction
        · congr 1
          omega
    constructor <;> intro hextreme
    · have hbad : complement.Perm (List.range' 2 (skeleton.length - 1)) := by
        apply List.perm_of_nodup_nodup_toFinset_eq hcomplementNodup (List.nodup_range' _)
        apply Finset.ext
        intro value
        simp only [List.mem_toFinset, hcomplement, List.mem_range'_1,
          hperm.mem_iff, hextreme]
        omega
      apply hsimple (if blockIndex = 0 then 1 else 0) (skeleton.length - 1) 2
        (by omega) (by omega) (by split_ifs <;> omega)
      rw [← hcomplementSlice]
      exact hbad
    · have hbad : complement.Perm (List.range' 1 (skeleton.length - 1)) := by
        apply List.perm_of_nodup_nodup_toFinset_eq hcomplementNodup (List.nodup_range' _)
        apply Finset.ext
        intro value
        simp only [List.mem_toFinset, hcomplement, List.mem_range'_1,
          hperm.mem_iff, hextreme]
        omega
      apply hsimple (if blockIndex = 0 then 1 else 0) (skeleton.length - 1) 1
        (by omega) (by omega) (by split_ifs <;> omega)
      rw [← hcomplementSlice]
      exact hbad
  have houterSelected : ∀ value, value ∈ skeleton → value ≠ pivot →
      up value ∈ (expanded.drop index).take size := by
    intro value hvalue hne
    obtain ⟨original, horiginal, hgetValue⟩ := List.mem_iff_getElem.mp hvalue
    have hgetD : skeleton.getD original 0 = value := by
      simpa only [List.getD_eq_getElem _ _ horiginal] using hgetValue
    have hnotPivot : original ≠ blockIndex := by
      intro heq
      subst original
      exact hne hgetD.symm
    obtain ⟨position, hfirst, hlast, hproject⟩ :=
      hpositionFiber original (by omega) (by omega)
    apply (hsliceMem expanded index size hbound _).mpr
    refine ⟨position, hfirst, hlast, ?_⟩
    rw [hgetOutside position (by omega) (by omega), hproject, hgetD]
  have hminimum : 1 ∈ skeleton := hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
  have hmaximum : skeleton.length ∈ skeleton :=
    hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
  have hlowSelected := houterSelected 1 hminimum (Ne.symm hpivotNonextreme.1)
  have hhighSelected := houterSelected skeleton.length hmaximum (Ne.symm hpivotNonextreme.2)
  have hupLow : up 1 = 1 := by simp only [up]; split_ifs <;> omega
  have hupHigh : up skeleton.length = expanded.length := by
    dsimp [up]
    split_ifs <;> omega
  rw [hupLow] at hlowSelected
  rw [hupHigh] at hhighSelected
  have hlow := List.mem_range'_1.mp (hinterval.mem_iff.mp hlowSelected)
  have hhigh := List.mem_range'_1.mp (hinterval.mem_iff.mp hhighSelected)
  omega

end D5.S3.Combinatorics.PopStack.PopStackPrime
