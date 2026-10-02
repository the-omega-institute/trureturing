/- GID: D5/S3/Combinatorics/PopStack/PopStackMaximumTerminal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackMaximumTerminal
   mirror-E: none(waiver:exhausted-lower-prefix-exceptions)
   anchors: []
   utility: none
   digest: Exhausting the lower ranks before the minimum forces exactly the P or E exception. -/

import D5.S3.Combinatorics.PopStack.PopStackMaximumPrefix
import D5.S3.Combinatorics.PopStack.PopStackExtra

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackMaximumTerminal

open PopStackDefs PopStackParallel PopStackExtra PopStackMaximumPrefix

theorem exhausted_lower_prefix (permutation : List ℕ)
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
    (minimumIndex : ℕ) (hminimumLater : 2 ≤ minimumIndex)
    (hminimumBound : minimumIndex < permutation.length)
    (hminimum : permutation.getD minimumIndex 0 = 1)
    (heven : minimumIndex % 2 = 0)
    (hexhausted : permutation.getD 0 0 = minimumIndex / 2 + 1) :
    (permutation.length = minimumIndex + 1 ∧ permutation = E (minimumIndex / 2)) ∨
      (permutation.length = minimumIndex + 2 ∧ permutation = P (minimumIndex / 2 + 1)) := by
  let value := fun index => permutation.getD index 0
  let half := minimumIndex / 2
  change (permutation.length = minimumIndex + 1 ∧ permutation = E half) ∨
    (permutation.length = minimumIndex + 2 ∧ permutation = P (half + 1))
  have hhalf : 1 ≤ half := by dsimp [half]; omega
  have hminimumEq : minimumIndex = 2 * half := by dsimp [half]; omega
  have halpha : value 0 = half + 1 := hexhausted
  have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hdistinct : ∀ first second, first < permutation.length →
      second < permutation.length → value first = value second → first = second := by
    intro first second hfirst hsecond heq
    exact (List.getD_inj hfirst hsecond hnodup).mp heq
  have hbounds : ∀ index, index < permutation.length →
      1 ≤ value index ∧ value index ≤ permutation.length := by
    intro index hindex
    have hmem : value index ∈ permutation := by
      rw [show value index = permutation[index] from List.getD_eq_getElem _ 0 hindex]
      exact List.getElem_mem hindex
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
    omega
  have hprefix := maximum_second_prefix permutation hperm hlength hmaximum hupper hlower
    hbonds minimumIndex hminimumBound hminimum
  have hprefixValue : ∀ index, index < minimumIndex → value index =
      if index % 2 = 0 then half + 1 - index / 2
      else permutation.length - index / 2 := by
    intro index hindex
    simpa only [value, hexhausted] using hprefix index hindex
  have htailUpper : ∀ index, minimumIndex < index → index < permutation.length →
      half + 1 < value index := by
    intro index hafter hindex
    have hbound := hbounds index hindex
    by_contra hnot
    have hsmall : value index ≤ half + 1 := by omega
    by_cases hone : value index = 1
    · have heq : value index = value minimumIndex := by simpa only [value, hminimum]
      have hh := hdistinct index minimumIndex hindex hminimumBound heq
      omega
    have hposition : 2 * (half + 1 - value index) < minimumIndex := by omega
    have hentry : value (2 * (half + 1 - value index)) = value index := by
      rw [hprefixValue _ hposition]
      split_ifs <;> omega
    have hh := hdistinct _ index (by omega) hindex hentry
    omega
  have htailBound : ∀ index, minimumIndex < index → index < permutation.length →
      value index ≤ permutation.length - half := by
    intro index hafter hindex
    have hupperValue := htailUpper index hafter hindex
    by_cases hsmall : minimumIndex = 2
    · have hhalfOne : half = 1 := by omega
      have hbound := hbounds index hindex
      have hne : value index ≠ permutation.length := by
        intro heq
        have hh := hdistinct index 1 hindex (by omega)
          (by change permutation.getD index 0 = permutation.getD 1 0; rw [hmaximum]; exact heq)
        omega
      omega
    have hlastPrefix : value (minimumIndex - 1) = permutation.length - half + 1 := by
      rw [hprefixValue _ (by omega)]
      split_ifs <;> omega
    have hlastUpper : half + 1 < value (minimumIndex - 1) := by
      have hnotEqual : value (minimumIndex - 1) ≠ value 0 := by
        intro heq
        have hh := hdistinct (minimumIndex - 1) 0 (by omega) (by omega) heq
        omega
      omega
    have hh := hupper (minimumIndex - 1) index (by omega) (by omega) hindex
      (by simpa only [value, halpha] using hlastUpper)
      (by simpa only [value, halpha] using hupperValue)
    change value index < value (minimumIndex - 1) at hh
    omega
  have htailShort : permutation.length ≤ minimumIndex + 2 := by
    by_contra hlong
    have hfirstBound : minimumIndex + 1 < permutation.length := by omega
    have hsecondBound : minimumIndex + 2 < permutation.length := by omega
    have hfirstUpper := htailUpper (minimumIndex + 1) (by omega) hfirstBound
    have hsecondUpper := htailUpper (minimumIndex + 2) (by omega) hsecondBound
    have hfirstLimit := htailBound (minimumIndex + 1) (by omega) hfirstBound
    have hdecrease := hupper (minimumIndex + 1) (minimumIndex + 2) (by omega)
      (by omega) hsecondBound (by simpa only [value, halpha] using hfirstUpper)
      (by simpa only [value, halpha] using hsecondUpper)
    change value (minimumIndex + 2) < value (minimumIndex + 1) at hdecrease
    have hnotBond := (hbonds (minimumIndex + 1) (by omega)).1
    change value (minimumIndex + 1) ≠ value (minimumIndex + 2) + 1 at hnotBond
    have hmissingRange : value (minimumIndex + 1) - 1 ∈
        List.range' 1 permutation.length := List.mem_range'_1.mpr (by omega)
    obtain ⟨position, hposition, hmissing⟩ :=
      List.mem_iff_getElem.mp (hperm.mem_iff.mpr hmissingRange)
    have hmissingValue : value position = value (minimumIndex + 1) - 1 := by
      change permutation.getD position 0 = _
      rw [List.getD_eq_getElem _ _ hposition]
      exact hmissing
    by_cases hbefore : position < minimumIndex
    · have hh := hprefixValue position hbefore
      split_ifs at hh <;> omega
    by_cases hatMinimum : position = minimumIndex
    · subst position
      change permutation.getD minimumIndex 0 = _ at hmissingValue
      rw [hminimum] at hmissingValue
      omega
    by_cases hatFirst : position = minimumIndex + 1
    · subst position; omega
    by_cases hatSecond : position = minimumIndex + 2
    · subst position; omega
    have hmissingUpper := htailUpper position (by omega) hposition
    have hh := hupper (minimumIndex + 2) position (by omega) (by omega) hposition
      (by simpa only [value, halpha] using hsecondUpper)
      (by simpa only [value, halpha] using hmissingUpper)
    change value position < value (minimumIndex + 2) at hh
    omega
  by_cases hterminal : permutation.length = minimumIndex + 1
  · refine Or.inl ⟨hterminal, ?_⟩
    have hElen : (E half).length = minimumIndex + 1 := by
      simp only [E, P, List.length_append, List.length_map, List.length_ofFn,
        List.length_singleton]
      omega
    apply List.ext_getElem
    · omega
    · intro index hindex hEindex
      rw [← List.getD_eq_getElem permutation 0 hindex]
      change value index = (E half)[index]
      by_cases hbefore : index < minimumIndex
      · have hPindex : index < (P half).length := by
          simp only [P, List.length_ofFn]; omega
        have hmapped : index < ((P half).map Nat.succ).length := by simpa
        simp only [E]
        rw [List.getElem_append_left hmapped, List.getElem_map]
        simp only [P, List.getElem_ofFn]
        rw [hprefixValue index hbefore]
        split_ifs <;> omega
      · have heq : index = minimumIndex := by omega
        subst index
        simp only [E]
        rw [List.getElem_append_right (by
          simp only [List.length_map, P, List.length_ofFn]; omega)]
        have hoffset : minimumIndex - ((P half).map Nat.succ).length = 0 := by
          simp only [List.length_map, P, List.length_ofFn]; omega
        simp only [hoffset, List.getElem_cons_zero]
        exact hminimum
  · have hlastLength : permutation.length = minimumIndex + 2 := by omega
    refine Or.inr ⟨hlastLength, ?_⟩
    have hPlen : (P (half + 1)).length = minimumIndex + 2 := by
      simp only [P, List.length_ofFn]; omega
    have hlastValue : value (minimumIndex + 1) = half + 2 := by
      have hupperValue := htailUpper (minimumIndex + 1) (by omega) (by omega)
      have hlimit := htailBound (minimumIndex + 1) (by omega) (by omega)
      omega
    apply List.ext_getElem
    · omega
    · intro index hindex hPindex
      rw [← List.getD_eq_getElem permutation 0 hindex]
      change value index = (P (half + 1))[index]
      simp only [P, List.getElem_ofFn]
      by_cases hbefore : index < minimumIndex
      · rw [hprefixValue index hbefore]
        split_ifs <;> omega
      by_cases hatMinimum : index = minimumIndex
      · subst index
        change permutation.getD minimumIndex 0 = _
        rw [hminimum]
        split_ifs; omega
      · have heq : index = minimumIndex + 1 := by omega
        subst index
        rw [hlastValue]
        split_ifs <;> omega

end D5.S3.Combinatorics.PopStack.PopStackMaximumTerminal
