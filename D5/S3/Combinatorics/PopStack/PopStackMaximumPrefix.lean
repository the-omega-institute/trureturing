/- GID: D5/S3/Combinatorics/PopStack/PopStackMaximumPrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackMaximumPrefix
   mirror-E: none(waiver:maximum-second-alternating-prefix)
   anchors: []
   utility: none
   digest: Successive extrema and bond exclusion force an alternating prefix before the minimum. -/

import D5.S3.Combinatorics.PopStack.PopStackMaximumShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackMaximumPrefix

open PopStackDefs

theorem maximum_second_prefix (permutation : List ℕ)
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
        permutation.getD first 0 < permutation.getD larger 0))
    (hbonds : ∀ index, index + 1 < permutation.length →
      permutation.getD index 0 ≠ permutation.getD (index + 1) 0 + 1 ∧
      permutation.getD (index + 1) 0 ≠ permutation.getD index 0 + 1)
    (minimumIndex : ℕ) (hminimumBound : minimumIndex < permutation.length)
    (hminimum : permutation.getD minimumIndex 0 = 1) :
    ∀ index, index < minimumIndex → permutation.getD index 0 =
      if index % 2 = 0 then permutation.getD 0 0 - index / 2
      else permutation.length - index / 2 := by
  let value := fun index => permutation.getD index 0
  let alpha := value 0
  let maximum := permutation.length
  have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hmaximumValue : value 1 = maximum := hmaximum
  have hminimumValue : value minimumIndex = 1 := hminimum
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
  have halphaBounds := hbounds 0 (by omega)
  have halphaBelow : alpha < maximum := by
    have hne : alpha ≠ maximum := by
      intro heq
      have hh := hinjective 0 1 (by omega) (by omega) (heq.trans hmaximumValue.symm)
      omega
    omega
  have hlocate : ∀ rank, 1 ≤ rank → rank ≤ maximum →
      ∃ index, index < maximum ∧ value index = rank := by
    intro rank hpositive hbound
    have hmem := hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hpositive, by omega⟩)
    obtain ⟨index, hindex, hentry⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨index, hindex, (List.getD_eq_getElem _ 0 hindex).trans hentry⟩
  have hbeforePositive : ∀ index, index < minimumIndex → 1 < value index := by
    intro index hbefore
    have hb := hbounds index (by omega)
    have hn : value index ≠ 1 := by
      intro heq
      have hi := hinjective index minimumIndex (by omega) hminimumBound
        (heq.trans hminimumValue.symm)
      omega
    omega
  have hprefix : ∀ index, index < minimumIndex →
      (value index = if index % 2 = 0 then alpha - index / 2 else maximum - index / 2) ∧
      (index % 2 = 1 → alpha < value index) := by
    intro index
    induction index using Nat.strong_induction_on with
    | h index ih =>
      intro hbefore
      by_cases hzero : index = 0
      · subst index; simp [alpha]
      by_cases hone : index = 1
      · subst index; simpa using
          (show value 1 = maximum ∧ (1 = 1 → alpha < value 1) from
            ⟨hmaximumValue, fun _ => by omega⟩)
      have hindex : 2 ≤ index := by omega
      have hvaluePositive := hbeforePositive index hbefore
      have hvalueBound := hbounds index (by omega)
      have hnotAlpha : value index ≠ alpha := by
        intro heq
        have hh := hinjective index 0 (by omega) (by omega) heq
        omega
      have hlowerChoice : value index < alpha → value index = alpha - (index + 1) / 2 := by
        intro hlow
        let count := (index + 1) / 2
        have hle : value index ≤ alpha - count := by
          by_contra hnot
          let old := 2 * (alpha - value index)
          have holdBefore : old < index := by dsimp only [old, count] at *; omega
          have holdEven : old % 2 = 0 := by dsimp only [old]; omega
          have holdHalf : old / 2 = alpha - value index := by dsimp only [old]; omega
          have hh := (ih old holdBefore (by omega)).1
          rw [if_pos holdEven, holdHalf] at hh
          have heq : value old = value index := by omega
          have hi := hinjective old index (by omega) (by omega) heq
          omega
        have hcount : 1 ≤ count ∧ count < alpha := by dsimp only [count] at *; omega
        obtain ⟨candidateIndex, hcandidateBound, hcandidate⟩ :=
          hlocate (alpha - count) (by omega) (by omega)
        have hcandidateAfter : index ≤ candidateIndex := by
          by_contra hnot
          obtain ⟨hh, hu⟩ := ih candidateIndex (by omega) (by omega)
          by_cases heven : candidateIndex % 2 = 0
          · rw [if_pos heven] at hh
            have hhalf : candidateIndex / 2 < count := by dsimp only [count]; omega
            omega
          · have hodd : candidateIndex % 2 = 1 := by omega
            have hh := hu hodd
            omega
        have hge : alpha - count ≤ value index := by
          by_contra hnot
          have hstrict : index < candidateIndex := by
            by_cases heq : index = candidateIndex
            · subst candidateIndex; omega
            omega
          have hh := hlower index minimumIndex candidateIndex hindex hbefore hstrict
            hminimumBound hcandidateBound hlow
            (show value minimumIndex < alpha by omega)
            (show value candidateIndex < alpha by omega)
            ⟨by change value minimumIndex < value index; omega,
              by change value index < value candidateIndex; omega⟩
          exact hh
        change value index = alpha - count
        omega
      have hupperChoice : alpha < value index → value index = maximum - index / 2 := by
        intro hupp
        let count := index / 2
        have hle : value index ≤ maximum - count := by
          by_contra hnot
          let old := 2 * (maximum - value index) + 1
          have holdBefore : old < index := by dsimp only [old, count] at *; omega
          have holdOdd : old % 2 ≠ 0 := by dsimp only [old]; omega
          have holdHalf : old / 2 = maximum - value index := by dsimp only [old]; omega
          have hh := (ih old holdBefore (by omega)).1
          rw [if_neg holdOdd, holdHalf] at hh
          have heq : value old = value index := by omega
          have hi := hinjective old index (by omega) (by omega) heq
          omega
        have hcandidateUpper : alpha < maximum - count := by omega
        obtain ⟨candidateIndex, hcandidateBound, hcandidate⟩ :=
          hlocate (maximum - count) (by omega) (by omega)
        have hcandidateAfter : index ≤ candidateIndex := by
          by_contra hnot
          obtain ⟨hh, _⟩ := ih candidateIndex (by omega) (by omega)
          by_cases heven : candidateIndex % 2 = 0
          · rw [if_pos heven] at hh; omega
          · rw [if_neg heven] at hh
            have hhalf : candidateIndex / 2 < count := by dsimp only [count]; omega
            omega
        have hge : maximum - count ≤ value index := by
          by_contra hnot
          have hstrict : index < candidateIndex := by
            by_cases heq : index = candidateIndex
            · subst candidateIndex; omega
            omega
          have hh := hupper index candidateIndex hindex hstrict hcandidateBound hupp
            (show alpha < value candidateIndex by omega)
          change value candidateIndex < value index at hh
          omega
        change value index = maximum - count
        omega
      have hpreviousBefore : index - 1 < index := by omega
      obtain ⟨hprevious, hpreviousUpper⟩ := ih (index - 1) hpreviousBefore (by omega)
      have hbond := (hbonds (index - 1) (by omega)).1
      have hbond' : value (index - 1) ≠ value index + 1 := by
        simpa only [show index - 1 + 1 = index by omega] using hbond
      by_cases heven : index % 2 = 0
      · have hpreviousOdd : (index - 1) % 2 ≠ 0 := by omega
        rw [if_neg hpreviousOdd] at hprevious
        have hlow : value index < alpha := by
          by_contra hnot
          have hupp : alpha < value index := by omega
          have hh := hupperChoice hupp
          have heq : value (index - 1) = value index + 1 := by omega
          exact hbond' heq
        have hh := hlowerChoice hlow
        refine ⟨?_, ?_⟩
        · rw [if_pos heven]; omega
        · intro hodd; omega
      · have hpreviousEven : (index - 1) % 2 = 0 := by omega
        rw [if_pos hpreviousEven] at hprevious
        have hupp : alpha < value index := by
          by_contra hnot
          have hlow : value index < alpha := by omega
          have hh := hlowerChoice hlow
          have heq : value (index - 1) = value index + 1 := by omega
          exact hbond' heq
        exact ⟨by rw [if_neg heven]; exact hupperChoice hupp, fun _ => hupp⟩
  intro index hindex
  exact (hprefix index hindex).1

end D5.S3.Combinatorics.PopStack.PopStackMaximumPrefix
