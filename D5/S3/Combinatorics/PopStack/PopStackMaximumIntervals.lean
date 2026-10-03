/- GID: D5/S3/Combinatorics/PopStack/PopStackMaximumIntervals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackMaximumIntervals
   mirror-E: none(waiver:maximum-second-bond-free-intervals)
   anchors: []
   utility: none
   digest: A bond-free maximum-second shape is simple unless it is the odd extra family. -/

import D5.S3.Combinatorics.PopStack.PopStackMaximumPrefix
import D5.S3.Combinatorics.PopStack.PopStackExtra

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackMaximumIntervals

open PopStackDefs PopStackExtra PopStackParallel PopStackMaximumPrefix

theorem maximum_second_intervals (permutation : List ℕ)
    (hperm : permutation.Perm (List.range' 1 permutation.length))
    (hlength : 4 ≤ permutation.length) (hmaximum : permutation.getD 1 0 = permutation.length)
    (hupper : ∀ first second, 2 ≤ first → first < second → second < permutation.length →
      permutation.getD 0 0 < permutation.getD first 0 →
      permutation.getD 0 0 < permutation.getD second 0 →
      permutation.getD second 0 < permutation.getD first 0)
    (hlower : ∀ first smaller larger, 2 ≤ first → first < smaller → first < larger →
      smaller < permutation.length → larger < permutation.length →
      permutation.getD first 0 < permutation.getD 0 0 →
      permutation.getD smaller 0 < permutation.getD 0 0 →
      permutation.getD larger 0 < permutation.getD 0 0 →
      ¬ (permutation.getD smaller 0 < permutation.getD first 0 ∧
        permutation.getD first 0 < permutation.getD larger 0)) :
    InC permutation ∧ ((∀ index, index + 1 < permutation.length →
      permutation.getD index 0 ≠ permutation.getD (index + 1) 0 + 1 ∧
      permutation.getD (index + 1) 0 ≠ permutation.getD index 0 + 1) ↔
      IsSimple permutation ∨ ∃ half, 2 ≤ half ∧ permutation = E half) := by
  classical
  refine ⟨(PopStackMaximumShape.maximum_second_shape permutation hperm hlength hmaximum).1
    ⟨hupper, hlower⟩, ?_⟩
  let value := fun index => permutation.getD index 0
  let alpha := value 0
  let maximum := permutation.length
  have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hmaximumValue : value 1 = maximum := hmaximum
  have hbounds : ∀ index, index < maximum → 1 ≤ value index ∧ value index ≤ maximum := by
    intro index hindex
    have hmem : value index ∈ permutation := by
      rw [show value index = permutation[index] from List.getD_eq_getElem _ 0 hindex]
      exact List.getElem_mem hindex
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
    omega
  have hinjective : ∀ first second, first < maximum → second < maximum →
      value first = value second → first = second := by
    intro first second hfirst hsecond heq
    exact (List.getD_inj hfirst hsecond hnodup).mp heq
  have hlocate : ∀ rank, 1 ≤ rank → rank ≤ maximum →
      ∃ index, index < maximum ∧ value index = rank := by
    intro rank hpositive hbound
    have hmem := hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hpositive, by omega⟩)
    obtain ⟨index, hindex, hentry⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨index, hindex, (List.getD_eq_getElem _ 0 hindex).trans hentry⟩
  have halphaBounds := hbounds 0 (by omega)
  have hpairBond : ∀ left, left + 1 < maximum →
      ((value left < alpha ∧ value (left + 1) < alpha) ∨
        (alpha < value left ∧ alpha < value (left + 1))) →
      (∀ rank, (value left < rank ∧ rank < value (left + 1)) ∨
        (value (left + 1) < rank ∧ rank < value left) →
        ∃ middle, 2 ≤ middle ∧ middle < left ∧ value middle = rank) →
      value left = value (left + 1) + 1 ∨ value (left + 1) = value left + 1 := by
    intro left hbound hside hbetween
    have hleftBounds := hbounds left (by omega)
    have hrightBounds := hbounds (left + 1) hbound
    have hne : value left ≠ value (left + 1) := by
      intro heq
      have hh := hinjective left (left + 1) (by omega) hbound heq
      omega
    by_contra hnot
    have hno : value left ≠ value (left + 1) + 1 ∧
        value (left + 1) ≠ value left + 1 := by simpa only [not_or] using hnot
    by_cases horder : value left < value (left + 1)
    · obtain ⟨middle, hmiddleTail, hmiddleBefore, hmiddle⟩ :=
        hbetween (value left + 1) (Or.inl ⟨by omega, by omega⟩)
      rcases hside with hlowerSide | hupperSide
      · exact hlower middle left (left + 1) hmiddleTail hmiddleBefore (by omega)
          (by omega) hbound (show value middle < alpha by omega)
          hlowerSide.1 hlowerSide.2
          ⟨by change value left < value middle; omega,
            by change value middle < value (left + 1); omega⟩
      · have hh := hupper middle (left + 1) hmiddleTail (by omega) hbound
          (show alpha < value middle by omega) hupperSide.2
        change value (left + 1) < value middle at hh
        omega
    · obtain ⟨middle, hmiddleTail, hmiddleBefore, hmiddle⟩ :=
        hbetween (value (left + 1) + 1) (Or.inr ⟨by omega, by omega⟩)
      rcases hside with hlowerSide | hupperSide
      · exact hlower middle (left + 1) left hmiddleTail (by omega) hmiddleBefore
          hbound (by omega) (show value middle < alpha by omega)
          hlowerSide.2 hlowerSide.1
          ⟨by change value (left + 1) < value middle; omega,
            by change value middle < value left; omega⟩
      · have hh := hupper middle left hmiddleTail hmiddleBefore (by omega)
          (show alpha < value middle by omega) hupperSide.1
        change value left < value middle at hh
        omega
  have hlastLowerBond : value (maximum - 2) < alpha → value (maximum - 1) < alpha →
      value (maximum - 2) = value (maximum - 1) + 1 ∨
        value (maximum - 1) = value (maximum - 2) + 1 := by
    intro hleft hright
    have hnext : maximum - 2 + 1 = maximum - 1 := by omega
    have hh := hpairBond (maximum - 2) (by omega) (by rw [hnext]; exact Or.inl ⟨hleft, hright⟩)
    rw [hnext] at hh
    apply hh
    intro rank hrank
    have hleftBounds := hbounds (maximum - 2) (by omega)
    have hrightBounds := hbounds (maximum - 1) (by omega)
    obtain ⟨middle, hmiddleBound, hmiddle⟩ := hlocate rank
      (by rcases hrank with h | h <;> omega)
      (by rcases hrank with h | h <;> omega)
    have hmiddleTail : 2 ≤ middle := by
      by_cases hzero : middle = 0
      · subst middle; change alpha = rank at hmiddle; rcases hrank with h | h <;> omega
      by_cases hone : middle = 1
      · subst middle; rcases hrank with h | h <;> omega
      omega
    have hmiddleBefore : middle < maximum - 2 := by
      by_cases hleftEq : middle = maximum - 2
      · subst middle; rcases hrank with h | h <;> omega
      by_cases hrightEq : middle = maximum - 1
      · subst middle; rcases hrank with h | h <;> omega
      omega
    exact ⟨middle, hmiddleTail, hmiddleBefore, hmiddle⟩
  have hslice : ∀ start size, start + size ≤ maximum →
      ∀ offset, offset < size →
        ((permutation.drop start).take size).getD offset 0 = value (start + offset) := by
    intro start size hbound offset hoffset
    rw [List.getD_eq_getElem _ 0 (by simp only [List.length_take, List.length_drop]; omega)]
    simp only [List.getElem_take, List.getElem_drop]
    exact (List.getD_eq_getElem _ 0 (by omega)).symm
  constructor
  · intro hbonds
    by_cases hsimple : IsSimple permutation
    · exact Or.inl hsimple
    right
    obtain ⟨start, size, lower, hsize, hproper, hbound, hinterval⟩ := by
      simpa only [IsSimple, not_forall, not_not, Classical.not_imp] using hsimple
    have hsegmentBounds : ∀ offset, offset < size →
        lower ≤ value (start + offset) ∧ value (start + offset) < lower + size := by
      intro offset hoffset
      have hmem : value (start + offset) ∈ (permutation.drop start).take size := by
        rw [← hslice start size hbound offset hoffset,
          List.getD_eq_getElem _ 0 (by simp only [List.length_take, List.length_drop]; omega)]
        exact List.getElem_mem _
      exact List.mem_range'_1.mp (hinterval.mem_iff.mp hmem)
    have hsegmentLocate : ∀ rank, lower ≤ rank → rank < lower + size →
        ∃ index, start ≤ index ∧ index < start + size ∧ value index = rank := by
      intro rank hlowerRank hupperRank
      have hmem := hinterval.mem_iff.mpr (List.mem_range'_1.mpr ⟨hlowerRank, hupperRank⟩)
      obtain ⟨offset, hoffset, hentry⟩ := List.mem_iff_getElem.mp hmem
      have hoffsetSize : offset < size := by
        simp only [List.length_take, List.length_drop] at hoffset
        omega
      refine ⟨start + offset, by omega, by omega, ?_⟩
      rw [← hslice start size hbound offset hoffsetSize,
        List.getD_eq_getElem _ 0 hoffset]
      exact hentry
    have hprefix : start = 0 := by
      by_contra hnot
      let left := start + size - 2
      have hnext : left + 1 = start + size - 1 := by dsimp only [left]; omega
      have hleftBounds := hsegmentBounds (size - 2) (by omega)
      have hrightBounds := hsegmentBounds (size - 1) (by omega)
      have hleftEq : start + (size - 2) = left := by dsimp only [left]; omega
      have hrightEq : start + (size - 1) = left + 1 := by dsimp only [left]; omega
      rw [hleftEq] at hleftBounds
      rw [hrightEq] at hrightBounds
      have halphaOutside : ¬ (lower ≤ alpha ∧ alpha < lower + size) := by
        rintro ⟨hlow, hupp⟩
        obtain ⟨index, hindexLower, hindexUpper, hvalue⟩ := hsegmentLocate alpha hlow hupp
        have hh := hinjective index 0 (by omega) (by omega) hvalue
        omega
      have hside : (value left < alpha ∧ value (left + 1) < alpha) ∨
          (alpha < value left ∧ alpha < value (left + 1)) := by omega
      have hbond := hpairBond left (by dsimp only [left]; omega) hside
      have hbetween : ∀ rank, (value left < rank ∧ rank < value (left + 1)) ∨
          (value (left + 1) < rank ∧ rank < value left) →
          ∃ middle, 2 ≤ middle ∧ middle < left ∧ value middle = rank := by
        intro rank hrank
        have hrankLower : lower ≤ rank := by rcases hrank with h | h <;> omega
        have hrankUpper : rank < lower + size := by rcases hrank with h | h <;> omega
        obtain ⟨middle, hmiddleStart, hmiddleEnd, hmiddle⟩ :=
          hsegmentLocate rank hrankLower hrankUpper
        have hleftGlobal := hbounds left (by dsimp only [left]; omega)
        have hrightGlobal := hbounds (left + 1) (by dsimp only [left]; omega)
        have hmiddleTail : 2 ≤ middle := by
          by_cases hone : middle = 1
          · subst middle; rcases hrank with h | h <;> omega
          omega
        have hmiddleBefore : middle < left := by
          by_cases hleftSame : middle = left
          · subst middle; rcases hrank with h | h <;> omega
          by_cases hrightSame : middle = left + 1
          · subst middle; rcases hrank with h | h <;> omega
          dsimp only [left] at *
          omega
        exact ⟨middle, hmiddleTail, hmiddleBefore, hmiddle⟩
      have hn := hbonds left (by dsimp only [left]; omega)
      rcases hbond hbetween with h | h
      · exact hn.1 h
      · exact hn.2 h
    subst start
    have hsizeMaximum := hsegmentBounds 1 (by omega)
    have hsizeAlpha := hsegmentBounds 0 (by omega)
    simp only [Nat.zero_add] at hsizeMaximum hsizeAlpha
    have htopRange : lower + size = maximum + 1 := by
      have hh := hsegmentBounds (size - 1) (by omega)
      have hlastRange : lower + size - 1 ≤ maximum := by
        obtain ⟨index, _, hindex, hvalue⟩ := hsegmentLocate (lower + size - 1) (by omega)
          (by omega)
        have hb := hbounds index (by omega)
        omega
      omega
    have hafterLower : ∀ index, size ≤ index → index < maximum → value index < alpha := by
      intro index hafter hindex
      have hb := hbounds index hindex
      by_contra hnot
      have hrank : lower ≤ value index ∧ value index < lower + size := by omega
      obtain ⟨earlier, _, hearlierSize, hvalue⟩ := hsegmentLocate (value index) hrank.1 hrank.2
      have hh := hinjective earlier index (by omega) hindex hvalue
      omega
    have hsizeLast : size = maximum - 1 := by
      by_contra hnot
      have hl := hafterLower (maximum - 2) (by omega) (by omega)
      have hr := hafterLower (maximum - 1) (by omega) (by omega)
      have hh := hlastLowerBond hl hr
      have hn := hbonds (maximum - 2) (by omega)
      have hnext : maximum - 2 + 1 = maximum - 1 := by omega
      rw [hnext] at hn
      rcases hh with hh | hh
      · exact hn.1 hh
      · exact hn.2 hh
    obtain ⟨minimumIndex, hminimumBound, hminimum⟩ := hlocate 1 (by omega) (by omega)
    have hminimumLast : minimumIndex = maximum - 1 := by
      have hlower : lower = 2 := by omega
      by_contra hnot
      have hentry := hsegmentBounds minimumIndex (by omega)
      simp only [Nat.zero_add] at hentry
      omega
    subst minimumIndex
    have hformula := maximum_second_prefix permutation hperm hlength hmaximum hupper hlower
      hbonds (maximum - 1) (by omega) hminimum
    change ∀ index, index < maximum - 1 → value index =
      if index % 2 = 0 then alpha - index / 2 else maximum - index / 2 at hformula
    have hbeforePositive : ∀ index, index < maximum - 1 → 1 < value index := by
      intro index hindex
      have hb := hbounds index (by omega)
      have hn : value index ≠ 1 := by
        intro heq
        have hh := hinjective index (maximum - 1) (by omega) (by omega)
          (heq.trans hminimum.symm)
        omega
      omega
    let lastEven := 2 * ((maximum - 2) / 2)
    have hlastEvenBound : lastEven < maximum - 1 := by dsimp only [lastEven]; omega
    have hlastEvenMod : lastEven % 2 = 0 := by dsimp only [lastEven]; omega
    have hlastEvenValue := hformula lastEven hlastEvenBound
    rw [if_pos hlastEvenMod] at hlastEvenValue
    have hlastEvenPositive := hbeforePositive lastEven hlastEvenBound
    obtain ⟨twoIndex, htwoBound, htwoValue⟩ := hlocate 2 (by omega) (by omega)
    have htwoBefore : twoIndex < maximum - 1 := by
      by_cases heq : twoIndex = maximum - 1
      · subst twoIndex; omega
      omega
    have htwoFormula := hformula twoIndex htwoBefore
    have htwoEven : twoIndex % 2 = 0 := by
      by_contra hnot
      rw [if_neg hnot] at htwoFormula
      omega
    rw [if_pos htwoEven] at htwoFormula
    have htwoHalf : twoIndex / 2 ≤ lastEven / 2 := by dsimp only [lastEven]; omega
    have hlastEvenTwo : value lastEven = 2 := by omega
    have hodd : maximum % 2 = 1 := by
      by_contra hnot
      have heven : maximum % 2 = 0 := by omega
      have hlast : lastEven = maximum - 2 := by dsimp only [lastEven]; omega
      have hn := (hbonds (maximum - 2) (by omega)).1
      have hnext : maximum - 2 + 1 = maximum - 1 := by omega
      rw [hnext] at hn
      rw [hlast] at hlastEvenTwo
      exact hn (by change value (maximum - 2) = value (maximum - 1) + 1; omega)
    let half := (maximum - 1) / 2
    have hlengthOdd : maximum = 2 * half + 1 := by dsimp only [half]; omega
    have hhalf : 2 ≤ half := by omega
    have halpha : alpha = half + 1 := by dsimp only [half, lastEven] at *; omega
    refine ⟨half, hhalf, ?_⟩
    have hElength : (E half).length = maximum := by
      simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
        List.length_singleton]
      omega
    apply List.ext_getElem
    · exact hElength.symm
    · intro index hindex hEindex
      rw [← List.getD_eq_getElem permutation 0 hindex]
      by_cases hlast : index = maximum - 1
      · subst index
        have hElast : (E half)[maximum - 1]'hEindex = 1 := by
          simp only [E, List.getElem_append, List.length_map, P, List.length_ofFn]
          rw [dif_neg (by omega)]
          simp [show maximum - 1 - 2 * half = 0 by omega]
        exact hminimum.trans hElast.symm
      · have hindexBefore : index < maximum - 1 := by omega
        have hh := hformula index hindexBefore
        simp only [E, List.getElem_append, List.length_map, P, List.length_ofFn]
        rw [dif_pos (by omega), List.getElem_map, List.getElem_ofFn]
        simp only [Nat.succ_eq_add_one]
        change value index = (if index % 2 = 0 then half - index / 2
          else 2 * half - index / 2) + 1
        split_ifs with heven
        · rw [if_pos heven] at hh
          have hp := hbeforePositive index hindexBefore
          omega
        · rw [if_neg heven] at hh
          omega
  · intro hsimpleOrExtra
    rcases hsimpleOrExtra with hsimple | ⟨half, hhalf, heq⟩
    · intro index hindex
      have hsegment : ((permutation.drop index).take 2) =
          [value index, value (index + 1)] := by
        apply List.ext_getElem
        · simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil]
          omega
        · intro offset _ hoffset
          have hcases : offset = 0 ∨ offset = 1 := by simp at hoffset; omega
          rcases hcases with rfl | rfl <;>
            simp only [List.getElem_take, List.getElem_drop, List.getElem_cons_zero,
              List.getElem_cons_succ, Nat.add_zero] <;>
            exact (List.getD_eq_getElem _ 0 (by omega)).symm
      constructor
      · intro hbond
        change value index = value (index + 1) + 1 at hbond
        apply hsimple index 2 (value (index + 1)) (by omega) (by omega) (by omega)
        rw [hsegment, hbond]
        simpa only [List.range'_succ, List.range'_zero] using List.Perm.swap _ _ []
      · intro hbond
        change value (index + 1) = value index + 1 at hbond
        apply hsimple index 2 (value index) (by omega) (by omega) (by omega)
        rw [hsegment, hbond]
        simpa only [List.range'_succ, List.range'_zero] using List.Perm.refl
          [value index, value index + 1]
    · obtain ⟨_, _, _, hintervals⟩ := odd_extra half (by omega)
      intro index hindex
      rw [heq] at *
      have hlengthE : (E half).length = 2 * half + 1 := by
        simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
          List.length_singleton]
      have hsegment : (((E half).drop index).take 2) =
          [(E half).getD index 0, (E half).getD (index + 1) 0] := by
        apply List.ext_getElem
        · simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil]
          omega
        · intro offset _ hoffset
          have hcases : offset = 0 ∨ offset = 1 := by simp at hoffset; omega
          rcases hcases with rfl | rfl <;>
            simp only [List.getElem_take, List.getElem_drop, List.getElem_cons_zero,
              List.getElem_cons_succ, Nat.add_zero] <;>
            exact (List.getD_eq_getElem _ 0 (by omega)).symm
      constructor
      · intro hbond
        have hh := (hintervals index 2 ((E half).getD (index + 1) 0) (by omega) (by omega)
          (by omega)).mp
        have hp : (((E half).drop index).take 2).Perm
            (List.range' ((E half).getD (index + 1) 0) 2) := by
          rw [hsegment, hbond]
          simpa only [List.range'_succ, List.range'_zero] using List.Perm.swap _ _ []
        have hh := hh hp
        omega
      · intro hbond
        have hh := (hintervals index 2 ((E half).getD index 0) (by omega) (by omega)
          (by omega)).mp
        have hp : (((E half).drop index).take 2).Perm
            (List.range' ((E half).getD index 0) 2) := by
          rw [hsegment, hbond]
          simpa only [List.range'_succ, List.range'_zero] using List.Perm.refl
            [(E half).getD index 0, (E half).getD index 0 + 1]
        have hh := hh hp
        omega

end D5.S3.Combinatorics.PopStack.PopStackMaximumIntervals
