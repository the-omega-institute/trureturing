/- GID: D5/S3/Combinatorics/PopStack/PopStackThirdEntry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackThirdEntry
   mirror-E: none(waiver:later-minimum-prefix-obstruction)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Forbidden occurrences force the third entry to be one less than the first. -/

import D5.S3.Combinatorics.PopStack.PopStackDefs
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackThirdEntry

open PopStackDefs

theorem third_entry_before_minimum (permutation : List ℕ)
    (hperm : permutation.Perm (List.range' 1 permutation.length))
    (hC : InC permutation) (hsimple : IsSimple permutation)
    (minimumIndex : ℕ) (hlater : 3 ≤ minimumIndex)
    (hminimumBound : minimumIndex < permutation.length)
    (hminimum : permutation.getD minimumIndex 0 = 1) :
    permutation.getD 0 0 = permutation.getD 2 0 + 1 := by
  classical
  let value := fun index => permutation.getD index 0
  let alpha := value 0
  let beta := value 1
  let gamma := value 2
  have hminimumValue : value minimumIndex = 1 := hminimum
  have hnodup : permutation.Nodup := hperm.nodup_iff.mpr (List.nodup_range' _)
  have hbounds : ∀ index, index < permutation.length →
      1 ≤ value index ∧ value index ≤ permutation.length := by
    intro index hindex
    have hmem : value index ∈ permutation := by
      change permutation.getD index 0 ∈ permutation
      rw [List.getD_eq_getElem _ 0 hindex]
      exact List.getElem_mem hindex
    have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
    omega
  have hinjective : ∀ first second, first < permutation.length →
      second < permutation.length → value first = value second → first = second := by
    intro first second hfirst hsecond heq
    exact (List.getD_inj hfirst hsecond hnodup).mp heq
  have hheadPositive : ∀ index, index < minimumIndex → 1 < value index := by
    intro index hindex
    have hlow := (hbounds index (by omega)).1
    have hnot : value index ≠ 1 := by
      intro heq
      have hh := hinjective index minimumIndex (by omega) hminimumBound
        (heq.trans hminimum.symm)
      omega
    omega
  have halpha := hbounds 0 (by omega)
  have hbeta := hbounds 1 (by omega)
  have hgamma := hbounds 2 (by omega)
  have halphaPositive : 1 < alpha := hheadPositive 0 (by omega)
  have hbetaPositive : 1 < beta := hheadPositive 1 (by omega)
  have hgammaPositive : 1 < gamma := hheadPositive 2 (by omega)
  have habDistinct : alpha ≠ beta := by
    intro heq
    have hh := hinjective 0 1 (by omega) (by omega) heq
    omega
  have hagDistinct : alpha ≠ gamma := by
    intro heq
    have hh := hinjective 0 2 (by omega) (by omega) heq
    omega
  have hbgDistinct : beta ≠ gamma := by
    intro heq
    have hh := hinjective 1 2 (by omega) (by omega) heq
    omega
  have hbonds : ∀ index, index + 2 ≤ permutation.length →
      value index + 1 ≠ value (index + 1) ∧ value (index + 1) + 1 ≠ value index := by
    intro index hindex
    have hsegment : ((permutation.drop index).take 2) =
        [value index, value (index + 1)] := by
      apply List.ext_getElem
      · simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil]
        omega
      · intro offset _ hoffset
        have hsmall : offset = 0 ∨ offset = 1 := by simp at hoffset; omega
        rcases hsmall with rfl | rfl
        · simp only [List.getElem_take, List.getElem_drop, Nat.add_zero,
            List.getElem_cons_zero, value]
          exact (List.getD_eq_getElem permutation 0 (by omega)).symm
        · simp only [List.getElem_take, List.getElem_drop, List.getElem_cons_succ,
            List.getElem_cons_zero, value]
          exact (List.getD_eq_getElem permutation 0 (by omega)).symm
    constructor
    · intro heq
      apply hsimple index 2 (value index) (by omega) (by omega) hindex
      rw [hsegment, ← heq]
      simp only [List.range'_succ, List.range'_zero]
      exact List.Perm.refl _
    · intro heq
      apply hsimple index 2 (value (index + 1)) (by omega) (by omega) hindex
      rw [hsegment, ← heq]
      simp only [List.range'_succ, List.range'_zero]
      exact List.Perm.swap _ _ _
  have habBond := hbonds 0 (by omega)
  have hbgBond := hbonds 1 (by omega)
  have locate : ∀ rank, 1 < rank → rank ≤ permutation.length →
      rank ≠ alpha → rank ≠ beta → rank ≠ gamma →
      ∃ index, 3 ≤ index ∧ index < permutation.length ∧ index ≠ minimumIndex ∧
        value index = rank := by
    intro rank hpositive hupper hna hnb hng
    have hmem : rank ∈ permutation :=
      hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    obtain ⟨index, hindex, hget⟩ := List.mem_iff_getElem.mp hmem
    have hvalue : value index = rank := by
      simpa only [value, List.getD_eq_getElem _ 0 hindex] using hget
    have hnotZero : index ≠ 0 := by
      intro heq
      subst index
      exact hna hvalue.symm
    have hnotOne : index ≠ 1 := by
      intro heq
      subst index
      exact hnb hvalue.symm
    have hnotTwo : index ≠ 2 := by
      intro heq
      subst index
      exact hng hvalue.symm
    refine ⟨index, by omega, hindex, ?_, hvalue⟩
    intro heq
    subst index
    change permutation.getD minimumIndex 0 = rank at hvalue
    omega
  have hselected : ∀ positions : List ℕ, positions.Pairwise (· < ·) →
      (∀ position ∈ positions, position < permutation.length) →
      (positions.map value).Sublist permutation := by
    intro positions horder hbound
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    let select : Fin (positions.map value).length → Fin permutation.length := fun index =>
      ⟨positions[index.val]'(by simpa using index.isLt),
        hbound _ (List.getElem_mem (by simpa using index.isLt))⟩
    have hmono : StrictMono select := by
      intro first second hlt
      exact List.pairwise_iff_getElem.mp horder first.val second.val
        (by simpa using first.isLt) (by simpa using second.isLt) hlt
    refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
    intro index
    simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono]
    change value positions[index.val] = permutation[(select index).val]
    dsimp only [select, value]
    exact List.getD_eq_getElem _ _ (hbound _ (List.getElem_mem (by simpa using index.isLt)))
  have htemplates : ∀ pattern ∈ basis, pattern.Perm (List.range' 1 pattern.length) :=
    by decide
  have forbid : ∀ pattern ∈ basis, ∀ positions ranks : List ℕ,
      positions.Pairwise (· < ·) →
      (∀ position ∈ positions, position < permutation.length) →
      ranks.Pairwise (· < ·) → ranks.length = pattern.length →
      pattern.map (fun rank => ranks.getD (rank - 1) 0) = positions.map value → False := by
    intro pattern hpattern positions ranks hpositions hpositionBounds hranks hlength hmatch
    let witness := fun rank => ranks.getD (rank - 1) 0
    have hsub := hselected positions hpositions hpositionBounds
    apply hC pattern hpattern
    refine ⟨witness, ?_, ?_, ?_, by simp⟩
    · intro rank hrank hlast
      have hleft : rank - 1 < ranks.length := by omega
      have hright : rank < ranks.length := by omega
      dsimp only [witness]
      rw [Nat.add_sub_cancel, List.getD_eq_getElem _ 0 hleft,
        List.getD_eq_getElem _ 0 hright]
      exact List.pairwise_iff_getElem.mp hranks (rank - 1) rank hleft hright (by omega)
    · intro rank hrank hlast
      have hmem : rank ∈ pattern :=
        (htemplates pattern hpattern).mem_iff.mpr
          (List.mem_range'_1.mpr ⟨hrank, by omega⟩)
      apply hsub.subset
      rw [← hmatch]
      exact List.mem_map.mpr ⟨rank, hmem, rfl⟩
    · rw [show pattern.map witness = positions.map value from hmatch]
      exact hsub
  change alpha = gamma + 1
  by_contra hnot
  by_cases hab : alpha < beta
  · by_cases hbg : beta < gamma
    · exact forbid [2, 3, 4, 1] (by simp [basis])
        [0, 1, 2, minimumIndex] [1, alpha, beta, gamma]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [alpha, beta, gamma, hminimumValue])
    have hgb : gamma < beta := by omega
    by_cases hag : alpha < gamma
    · have hgap : gamma + 1 < beta := by change _ ∧ gamma + 1 ≠ beta at hbgBond; omega
      obtain ⟨deltaIndex, hdLower, hdBound, hdNot, hdelta⟩ :=
        locate (gamma + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      by_cases hdBefore : deltaIndex < minimumIndex
      · exact forbid [2, 3, 4, 1] (by simp [basis])
          [0, 2, deltaIndex, minimumIndex] [1, alpha, gamma, gamma + 1]
          (by simp [List.pairwise_cons]; omega)
          (by intro position hp; simp at hp; omega)
          (by simp [List.pairwise_cons]; omega) rfl
          (by simp [alpha, gamma, hminimumValue, hdelta])
      · exact forbid [2, 5, 3, 1, 4] (by simp [basis])
          [0, 1, 2, minimumIndex, deltaIndex] [1, alpha, gamma, gamma + 1, beta]
          (by simp [List.pairwise_cons]; omega)
          (by intro position hp; simp at hp; omega)
          (by simp [List.pairwise_cons]; omega) rfl
          (by simp [alpha, beta, gamma, hminimumValue, hdelta])
    have hga : gamma < alpha := by omega
    have hgap : gamma + 1 < alpha := by omega
    obtain ⟨deltaIndex, hdLower, hdBound, hdNot, hdelta⟩ :=
      locate (gamma + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    by_cases hdBefore : deltaIndex < minimumIndex
    · exact forbid [4, 5, 2, 3, 1] (by simp [basis])
        [0, 1, 2, deltaIndex, minimumIndex] [1, gamma, gamma + 1, alpha, beta]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [alpha, beta, gamma, hminimumValue, hdelta])
    · exact forbid [4, 5, 2, 1, 3] (by simp [basis])
        [0, 1, 2, minimumIndex, deltaIndex] [1, gamma, gamma + 1, alpha, beta]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [alpha, beta, gamma, hminimumValue, hdelta])
  have hba : beta < alpha := by omega
  by_cases hag : alpha < gamma
  · have hgap : beta + 1 < alpha := by change _ ∧ beta + 1 ≠ alpha at habBond; omega
    obtain ⟨deltaIndex, hdLower, hdBound, hdNot, hdelta⟩ :=
      locate (beta + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    by_cases hdBefore : deltaIndex < minimumIndex
    · exact forbid [4, 2, 5, 3, 1] (by simp [basis])
        [0, 1, 2, deltaIndex, minimumIndex] [1, beta, beta + 1, alpha, gamma]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [alpha, beta, gamma, hminimumValue, hdelta])
    · exact forbid [4, 2, 5, 1, 3] (by simp [basis])
        [0, 1, 2, minimumIndex, deltaIndex] [1, beta, beta + 1, alpha, gamma]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [alpha, beta, gamma, hminimumValue, hdelta])
  have hga : gamma < alpha := by omega
  by_cases hbg : beta < gamma
  · have hgap : gamma + 1 < alpha := by omega
    obtain ⟨deltaIndex, hdLower, hdBound, hdNot, hdelta⟩ :=
      locate (gamma + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    by_cases hdBefore : deltaIndex < minimumIndex
    · exact forbid [2, 3, 4, 1] (by simp [basis])
        [1, 2, deltaIndex, minimumIndex] [1, beta, gamma, gamma + 1]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [beta, gamma, hminimumValue, hdelta])
    · exact forbid [5, 2, 3, 1, 4] (by simp [basis])
        [0, 1, 2, minimumIndex, deltaIndex] [1, beta, gamma, gamma + 1, alpha]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [alpha, beta, gamma, hminimumValue, hdelta])
  have hgb : gamma < beta := by omega
  have hdeltaGap : gamma + 1 < beta := by change _ ∧ gamma + 1 ≠ beta at hbgBond; omega
  have hepsilonGap : beta + 1 < alpha := by change _ ∧ beta + 1 ≠ alpha at habBond; omega
  obtain ⟨deltaIndex, hdLower, hdBound, hdNot, hdelta⟩ :=
    locate (gamma + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨epsilonIndex, heLower, heBound, heNot, hepsilon⟩ :=
    locate (beta + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hindicesDistinct : deltaIndex ≠ epsilonIndex := by
    intro heq
    rw [heq] at hdelta
    omega
  by_cases hdBefore : deltaIndex < minimumIndex <;>
    by_cases heBefore : epsilonIndex < minimumIndex
  · by_cases hde : deltaIndex < epsilonIndex
    · exact forbid [2, 3, 4, 1] (by simp [basis])
        [2, deltaIndex, epsilonIndex, minimumIndex] [1, gamma, gamma + 1, beta + 1]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [beta, gamma, hminimumValue, hdelta, hepsilon])
    · exact forbid [4, 2, 5, 3, 1] (by simp [basis])
        [1, 2, epsilonIndex, deltaIndex, minimumIndex] [1, gamma, gamma + 1, beta, beta + 1]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [beta, gamma, hminimumValue, hdelta, hepsilon])
  · exact forbid [5, 2, 3, 1, 4] (by simp [basis])
      [0, 2, deltaIndex, minimumIndex, epsilonIndex] [1, gamma, gamma + 1, beta + 1, alpha]
      (by simp [List.pairwise_cons]; omega)
      (by intro position hp; simp at hp; omega)
      (by simp [List.pairwise_cons]; omega) rfl
      (by simp [alpha, beta, gamma, hminimumValue, hdelta, hepsilon])
  · exact forbid [4, 2, 5, 1, 3] (by simp [basis])
      [1, 2, epsilonIndex, minimumIndex, deltaIndex] [1, gamma, gamma + 1, beta, beta + 1]
      (by simp [List.pairwise_cons]; omega)
      (by intro position hp; simp at hp; omega)
      (by simp [List.pairwise_cons]; omega) rfl
      (by simp [beta, gamma, hminimumValue, hdelta, hepsilon])
  · by_cases hde : deltaIndex < epsilonIndex
    · exact forbid [6, 4, 2, 1, 3, 5] (by simp [basis])
        [0, 1, 2, minimumIndex, deltaIndex, epsilonIndex]
        [1, gamma, gamma + 1, beta, beta + 1, alpha]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [alpha, beta, gamma, hminimumValue, hdelta, hepsilon])
    · exact forbid [6, 4, 2, 1, 5, 3] (by simp [basis])
        [0, 1, 2, minimumIndex, epsilonIndex, deltaIndex]
        [1, gamma, gamma + 1, beta, beta + 1, alpha]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hp; simp at hp; omega)
        (by simp [List.pairwise_cons]; omega) rfl
        (by simp [alpha, beta, gamma, hminimumValue, hdelta, hepsilon])

end D5.S3.Combinatorics.PopStack.PopStackThirdEntry
