/- GID: D5/S3/Combinatorics/PopStack/PopStackCrossing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackCrossing
   mirror-E: none(waiver:maximal-crossing-interval-decomposition)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Overlapping intervals avoiding the minimum give a maximal block and simple quotient. -/

import D5.S3.Combinatorics.PopStack.PopStackReconstruction
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackCrossing

open PopStackDefs PopStackInflation PopStackReconstruction

theorem crossing_decomposition (permutation : List ℕ) (gap : ℕ)
    (hperm : permutation.Perm (List.range' 1 permutation.length))
    (hclass : InC permutation) (hnonsimple : ¬ IsSimple permutation)
    (hcross : ∀ start count lower, 2 ≤ count → count < permutation.length →
      start + count ≤ permutation.length →
      ((permutation.drop start).take count).Perm (List.range' lower count) →
      start < gap ∧ gap < start + count ∧ 1 < lower) :
    ∃ start count lower skeleton block,
      2 ≤ count ∧ count < permutation.length ∧ start + count ≤ permutation.length ∧
      start < gap ∧ gap < start + count ∧ 1 < lower ∧
      ((permutation.drop start).take count).Perm (List.range' lower count) ∧
      skeleton.Perm (List.range' 1 skeleton.length) ∧
      block.Perm (List.range' 1 count) ∧ block.length = count ∧
      skeleton.length = permutation.length - count + 1 ∧
      inflate skeleton start block = permutation ∧
      Occurs skeleton permutation ∧ IsSimple skeleton ∧ InC skeleton ∧
      (∀ index size bottom, 2 ≤ size → size < permutation.length →
        index + size ≤ permutation.length →
        ((permutation.drop index).take size).Perm (List.range' bottom size) →
        start ≤ index ∧ index + size ≤ start + count) := by
  classical
  have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hsliceMem : ∀ start count, start + count ≤ permutation.length →
      ∀ entry, entry ∈ ((permutation.drop start).take count) ↔
        ∃ position, start ≤ position ∧ position < start + count ∧
          permutation.getD position 0 = entry := by
    intro start count hbound entry
    have hlength : ((permutation.drop start).take count).length = count := by
      simp only [List.length_take, List.length_drop]
      omega
    constructor
    · intro hentry
      obtain ⟨offset, hget⟩ := List.mem_iff_getElem?.mp hentry
      have hoffset : offset < count := by
        have hh := (List.getElem?_eq_some_iff.mp hget).1
        omega
      rw [List.getElem?_take_of_lt hoffset, List.getElem?_drop] at hget
      refine ⟨start + offset, by omega, by omega, ?_⟩
      simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]
    · rintro ⟨position, hstart, hend, hget⟩
      apply List.mem_iff_getElem?.mpr
      refine ⟨position - start, ?_⟩
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        Nat.add_sub_of_le hstart]
      rw [List.getD_eq_getElem _ _ (by omega)] at hget
      rw [List.getElem?_eq_getElem (by omega), hget]
  have hunion : ∀ start count lower index size bottom,
      2 ≤ count → count < permutation.length → start + count ≤ permutation.length →
      ((permutation.drop start).take count).Perm (List.range' lower count) →
      2 ≤ size → size < permutation.length → index + size ≤ permutation.length →
      ((permutation.drop index).take size).Perm (List.range' bottom size) →
      let first := min start index
      let last := max (start + count) (index + size)
      2 ≤ last - first ∧ last - first < permutation.length ∧
        ((permutation.drop first).take (last - first)).Perm
          (List.range' (min lower bottom) (last - first)) := by
    intro start count lower index size bottom hcount hproper hbound hinterval
      hsize hsizeProper hsizeBound hother
    obtain ⟨hstartGap, hgapEnd, hlower⟩ :=
      hcross start count lower hcount hproper hbound hinterval
    obtain ⟨hindexGap, hgapOther, hbottom⟩ :=
      hcross index size bottom hsize hsizeProper hsizeBound hother
    let first := min start index
    let last := max (start + count) (index + size)
    let low := min lower bottom
    let high := max (lower + count) (bottom + size)
    have hfirst : first ≤ start ∧ first ≤ index := by dsimp [first]; omega
    have hlast : start + count ≤ last ∧ index + size ≤ last := by dsimp [last]; omega
    have hlastBound : last ≤ permutation.length := by dsimp [last]; omega
    have hfirstLast : first ≤ last := by omega
    have hboundUnion : first + (last - first) ≤ permutation.length := by omega
    have hshared : lower ≤ permutation.getD (gap - 1) 0 ∧
        permutation.getD (gap - 1) 0 < lower + count ∧
        bottom ≤ permutation.getD (gap - 1) 0 ∧
        permutation.getD (gap - 1) 0 < bottom + size := by
      have hleft := hinterval.mem_iff.mp
        ((hsliceMem start count hbound _).mpr ⟨gap - 1, by omega, by omega, rfl⟩)
      have hright := hother.mem_iff.mp
        ((hsliceMem index size hsizeBound _).mpr ⟨gap - 1, by omega, by omega, rfl⟩)
      have hh := List.mem_range'_1.mp hleft
      have hh' := List.mem_range'_1.mp hright
      omega
    have hmemUnion : ∀ entry,
        entry ∈ ((permutation.drop first).take (last - first)) ↔
        entry ∈ ((permutation.drop start).take count) ∨
          entry ∈ ((permutation.drop index).take size) := by
      intro entry
      rw [hsliceMem first (last - first) hboundUnion,
        hsliceMem start count hbound, hsliceMem index size hsizeBound]
      constructor
      · rintro ⟨position, hfirstPosition, hpositionLast, hget⟩
        have hposition : (start ≤ position ∧ position < start + count) ∨
            (index ≤ position ∧ position < index + size) := by
          dsimp [first, last] at hfirstPosition hpositionLast
          omega
        rcases hposition with hleft | hright
        · exact Or.inl ⟨position, hleft.1, hleft.2, hget⟩
        · exact Or.inr ⟨position, hright.1, hright.2, hget⟩
      · rintro (⟨position, hstartPosition, hpositionEnd, hget⟩ |
          ⟨position, hindexPosition, hpositionEnd, hget⟩)
        · exact ⟨position, by omega, by omega, hget⟩
        · exact ⟨position, by omega, by omega, hget⟩
    have hvalueUnion : ((permutation.drop first).take (last - first)).Perm
        (List.range' low (high - low)) := by
      apply (List.perm_ext_iff_of_nodup (hnodup.drop.take)
        (List.nodup_range' _)).mpr
      intro entry
      rw [hmemUnion, hinterval.mem_iff, hother.mem_iff]
      simp only [List.mem_range'_1]
      dsimp [low, high]
      omega
    have hlength : last - first = high - low := by
      have hh := hvalueUnion.length_eq
      simp only [List.length_take, List.length_drop, List.length_range'] at hh
      omega
    have hnoMinimum : 1 ∉ ((permutation.drop first).take (last - first)) := by
      intro hminimum
      have hh := List.mem_range'_1.mp (hvalueUnion.mem_iff.mp hminimum)
      dsimp [low] at hh
      omega
    have hproperUnion : last - first < permutation.length := by
      by_contra hnot
      have hfirstZero : first = 0 := by omega
      have hwhole : last - first = permutation.length := by omega
      apply hnoMinimum
      rw [hwhole, hfirstZero, List.drop_zero, List.take_length]
      exact hperm.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
    refine ⟨by omega, hproperUnion, ?_⟩
    dsimp only [low] at hvalueUnion
    rw [← hlength] at hvalueUnion
    exact hvalueUnion
  have hexists : ∃ start count lower, 2 ≤ count ∧ count < permutation.length ∧
      start + count ≤ permutation.length ∧
      ((permutation.drop start).take count).Perm (List.range' lower count) := by
    simp only [IsSimple, not_forall, not_not] at hnonsimple
    obtain ⟨start, count, lower, hcount, hproper, hbound, hinterval⟩ := hnonsimple
    exact ⟨start, count, lower, hcount, hproper, hbound, hinterval⟩
  obtain ⟨oldStart, oldCount, oldLower, holdCount, holdProper, holdBound, holdInterval⟩ :=
    hexists
  let candidates := (Finset.range permutation.length).filter fun count =>
    2 ≤ count ∧ ∃ start lower, start + count ≤ permutation.length ∧
      ((permutation.drop start).take count).Perm (List.range' lower count)
  have holdMem : oldCount ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr holdProper,
      holdCount, oldStart, oldLower, holdBound, holdInterval⟩
  obtain ⟨count, hcountMem, hmax⟩ :=
    Finset.exists_max_image candidates id ⟨oldCount, holdMem⟩
  obtain ⟨hcountRange, hcount, start, lower, hbound, hinterval⟩ :=
    Finset.mem_filter.mp hcountMem
  have hproper := Finset.mem_range.mp hcountRange
  obtain ⟨hstartGap, hgapEnd, hlower⟩ :=
    hcross start count lower hcount hproper hbound hinterval
  have hcovered : ∀ index size bottom, 2 ≤ size → size < permutation.length →
      index + size ≤ permutation.length →
      ((permutation.drop index).take size).Perm (List.range' bottom size) →
      start ≤ index ∧ index + size ≤ start + count := by
    intro index size bottom hsize hsizeProper hsizeBound hother
    obtain ⟨hunionSize, hunionProper, hunionInterval⟩ :=
      hunion start count lower index size bottom hcount hproper hbound hinterval
        hsize hsizeProper hsizeBound hother
    have hunionBound : min start index +
        (max (start + count) (index + size) - min start index) ≤ permutation.length := by
      omega
    have hunionMem : max (start + count) (index + size) - min start index ∈
        candidates := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hunionProper, hunionSize,
        min start index, min lower bottom, hunionBound, hunionInterval⟩
    have hh := hmax _ hunionMem
    dsimp only [id] at hh
    omega
  let before := permutation.take start
  let values := (permutation.drop start).take count
  let after := permutation.drop (start + count)
  have hsplit : before ++ values ++ after = permutation := by
    dsimp [before, values, after]
    rw [← List.drop_drop, List.append_assoc, List.take_append_drop,
      List.take_append_drop]
  have hvaluesLength : values.length = count := by
    simp only [values, List.length_take, List.length_drop]
    omega
  have hbeforeLength : before.length = start := by
    simp only [before, List.length_take]
    omega
  have hafterLength : after.length = permutation.length - (start + count) := by
    simp only [after, List.length_drop]
  obtain ⟨skeleton, block, hskeleton, hblock, hskeletonLength, hblockLength,
    hinverse, hquotient⟩ := reconstruct_interval before values after lower
      (by simpa only [hsplit] using hperm) (by simpa only [hvaluesLength] using hinterval)
      (by omega)
  have hquotient' := hquotient (by simpa only [hsplit, hbeforeLength, hvaluesLength]
    using hcovered)
  rw [hsplit] at hquotient' hinverse
  rw [hbeforeLength] at hinverse
  refine ⟨start, count, lower, skeleton, block, hcount, hproper, hbound,
    hstartGap, hgapEnd, hlower, hinterval, hskeleton, ?_, by omega,
    by omega, hinverse, hquotient'.1, hquotient'.2.1, hquotient'.2.2 hclass, hcovered⟩
  simpa only [hblockLength, hvaluesLength] using hblock

end D5.S3.Combinatorics.PopStack.PopStackCrossing
