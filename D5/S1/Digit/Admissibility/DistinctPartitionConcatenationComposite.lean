/- GID: D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite
   generality: G
   mirror-B: D5/B/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.Finset, mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Data.List.Permutation, mathlib/module/Mathlib.Data.Nat.Digits.Defs, mathlib/module/Mathlib.Data.Nat.Prime.Basic, mathlib/module/Mathlib.Tactic.NormNum]
   utility: none
   digest: Every nonexceptional positive index has an eligible composite concatenation of distinct partition parts. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Distinct-partition concatenations

OEIS A110454 asks whether the only positive indices without a composite greater
than four among the decimal concatenations of distinct partition parts are
`1`, `2`, and `4`. The entry's Maple program includes one-part compositions and
explicitly tests `m > 4`.
-/

namespace D5.S1.Digit.Admissibility.DistinctPartitionConcatenationComposite

/-- Concatenate positive decimal blocks in their listed order. -/
def decimalConcatenation (parts : List ℕ) : ℕ :=
  Nat.ofDigits 10 (parts.reverse.flatMap (Nat.digits 10))

/-- All decimal concatenations of pairwise-distinct positive parts summing to `n`. -/
def C (n : ℕ) : Finset ℕ :=
  ((((Finset.range (n + 1)).erase 0).powerset.filter fun parts => parts.sum id = n).biUnion
    fun parts => parts.sort.permutations.toFinset.image decimalConcatenation)

/-- Murthy's 2005 conjecture for OEIS A110454, together with its finite data side. -/
theorem murthy_conjecture :
    (∀ n : ℕ, 1 ≤ n → n ∉ ({1, 2, 4} : Finset ℕ) →
      ∃ m ∈ C n, 4 < m ∧ ¬ Nat.Prime m) ∧
      ∀ n ∈ ({1, 2, 4} : Finset ℕ),
        (C n).filter (fun m => 4 < m ∧ ¬ Nat.Prime m) = ∅ := by
  constructor
  · intro n hn hnExceptional
    by_cases hn3 : n = 3
    · subst n
      refine ⟨21, ?_, by norm_num, ?_⟩
      · refine Finset.mem_biUnion.mpr ⟨{2, 1}, ?_, ?_⟩
        · rw [Finset.mem_filter]
          constructor
          · rw [Finset.mem_powerset]
            intro x hx
            simp at hx ⊢
            omega
          · norm_num
        · refine Finset.mem_image.mpr ⟨[2, 1], ?_, ?_⟩
          · rw [List.mem_toFinset, List.mem_permutations]
            exact (List.perm_ext_iff_of_nodup (by simp) (Finset.sort_nodup _ _)).2 (by simp)
          · rw [decimalConcatenation]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
              List.singleton_append, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, Nat.ofDigits_digits_append_digits]
            rw [Nat.digits_of_lt 10 1 (by norm_num) (by norm_num)]
            norm_num
      · apply Nat.not_prime_of_dvd_of_lt (m := 3)
        · norm_num
        · norm_num
        · norm_num
    · have hn5 : 5 ≤ n := by
        simp at hnExceptional
        omega
      have hne : n - 2 ≠ 2 := by omega
      have hconcat : decimalConcatenation [n - 2, 2] = 10 * (n - 2) + 2 := by
        rw [decimalConcatenation]
        simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          Nat.ofDigits_digits_append_digits]
        rw [Nat.digits_of_lt 10 2 (by norm_num) (by norm_num)]
        norm_num
        omega
      refine ⟨10 * (n - 2) + 2, ?_, by omega, ?_⟩
      · refine Finset.mem_biUnion.mpr ⟨{n - 2, 2}, ?_, ?_⟩
        · rw [Finset.mem_filter]
          constructor
          · rw [Finset.mem_powerset]
            intro x hx
            simp at hx ⊢
            omega
          · simp [hne]
            omega
        · refine Finset.mem_image.mpr ⟨[n - 2, 2], ?_, hconcat⟩
          rw [List.mem_toFinset, List.mem_permutations]
          exact (List.perm_ext_iff_of_nodup (by simp [hne]) (Finset.sort_nodup _ _)).2
            (by simp)
      · apply Nat.not_prime_of_dvd_of_lt (m := 2)
        · use 5 * (n - 2) + 1
          omega
        · norm_num
        · omega
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · apply Finset.filter_eq_empty_iff.mpr
      intro m hm hEligible
      rw [C] at hm
      rcases Finset.mem_biUnion.mp hm with ⟨parts, hparts, hm⟩
      have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hparts).1
      have hsum : ∑ x ∈ parts, x = 1 := by
        simpa only [id_eq] using (Finset.mem_filter.mp hparts).2
      rcases Finset.mem_image.mp hm with ⟨ordered, hordered, hvalue⟩
      rw [List.mem_toFinset, List.mem_permutations] at hordered
      have hpartsSubset : parts ⊆ {1} := by
        intro x hx
        have hxBound := hsub hx
        simp at hxBound ⊢
        omega
      have hpartsEq : parts = {1} := by
        rcases Finset.subset_singleton_iff.mp hpartsSubset with hempty | hone
        · rw [hempty] at hsum
          norm_num at hsum
        · exact hone
      have hcanonical : ([1] : List ℕ).Perm parts.sort :=
        (List.perm_ext_iff_of_nodup (by simp) (Finset.sort_nodup _ _)).2
          (by simp [hpartsEq])
      have horderedEq : ordered = [1] :=
        List.perm_singleton.mp (hordered.trans hcanonical.symm)
      subst ordered
      norm_num [decimalConcatenation, Nat.ofDigits] at hvalue
      omega
    · apply Finset.filter_eq_empty_iff.mpr
      intro m hm hEligible
      rw [C] at hm
      rcases Finset.mem_biUnion.mp hm with ⟨parts, hparts, hm⟩
      have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hparts).1
      have hsum : ∑ x ∈ parts, x = 2 := by
        simpa only [id_eq] using (Finset.mem_filter.mp hparts).2
      rcases Finset.mem_image.mp hm with ⟨ordered, hordered, hvalue⟩
      rw [List.mem_toFinset, List.mem_permutations] at hordered
      have htwo : 2 ∈ parts := by
        by_contra htwo
        have hpartsSubset : parts ⊆ {1} := by
          intro x hx
          have hxBound := hsub hx
          have hxTwo : x ≠ 2 := by
            intro hxEq
            subst x
            exact htwo hx
          simp at hxBound ⊢
          omega
        have hle : (∑ x ∈ parts, x) ≤ ∑ x ∈ ({1} : Finset ℕ), x :=
          Finset.sum_le_sum_of_subset hpartsSubset
        norm_num at hle
        omega
      have hrest : ∑ x ∈ parts.erase 2, x = 0 := by
        have hdecomp : (∑ x ∈ parts.erase 2, x) + 2 = ∑ x ∈ parts, x := by
          simpa only [id_eq] using Finset.sum_erase_add parts id htwo
        omega
      have hrestEmpty : parts.erase 2 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxZero := (Finset.sum_eq_zero_iff.mp hrest) x hx
        have hxParts := Finset.mem_of_mem_erase hx
        have hxBound := hsub hxParts
        simp at hxZero hxBound
        omega
      have hpartsEq : parts = {2} := by
        ext x
        simp only [Finset.mem_singleton]
        constructor
        · intro hx
          by_contra hxTwo
          have hxErase : x ∈ parts.erase 2 := Finset.mem_erase.mpr ⟨hxTwo, hx⟩
          rw [hrestEmpty] at hxErase
          simp at hxErase
        · intro hx
          subst x
          exact htwo
      have hcanonical : ([2] : List ℕ).Perm parts.sort :=
        (List.perm_ext_iff_of_nodup (by simp) (Finset.sort_nodup _ _)).2
          (by simp [hpartsEq])
      have horderedEq : ordered = [2] :=
        List.perm_singleton.mp (hordered.trans hcanonical.symm)
      subst ordered
      norm_num [decimalConcatenation, Nat.ofDigits] at hvalue
      omega
    · apply Finset.filter_eq_empty_iff.mpr
      intro m hm hEligible
      rw [C] at hm
      rcases Finset.mem_biUnion.mp hm with ⟨parts, hparts, hm⟩
      have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hparts).1
      have hsum : ∑ x ∈ parts, x = 4 := by
        simpa only [id_eq] using (Finset.mem_filter.mp hparts).2
      rcases Finset.mem_image.mp hm with ⟨ordered, hordered, hvalue⟩
      rw [List.mem_toFinset, List.mem_permutations] at hordered
      by_cases hfour : 4 ∈ parts
      · have hrest : ∑ x ∈ parts.erase 4, x = 0 := by
          have hdecomp : (∑ x ∈ parts.erase 4, x) + 4 = ∑ x ∈ parts, x := by
            simpa only [id_eq] using Finset.sum_erase_add parts id hfour
          omega
        have hrestEmpty : parts.erase 4 = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hxZero := (Finset.sum_eq_zero_iff.mp hrest) x hx
          have hxParts := Finset.mem_of_mem_erase hx
          have hxBound := hsub hxParts
          simp at hxZero hxBound
          omega
        have hpartsEq : parts = {4} := by
          ext x
          simp only [Finset.mem_singleton]
          constructor
          · intro hx
            by_contra hxFour
            have hxErase : x ∈ parts.erase 4 := Finset.mem_erase.mpr ⟨hxFour, hx⟩
            rw [hrestEmpty] at hxErase
            simp at hxErase
          · intro hx
            subst x
            exact hfour
        have hcanonical : ([4] : List ℕ).Perm parts.sort :=
          (List.perm_ext_iff_of_nodup (by simp) (Finset.sort_nodup _ _)).2
            (by simp [hpartsEq])
        have horderedEq : ordered = [4] :=
          List.perm_singleton.mp (hordered.trans hcanonical.symm)
        subst ordered
        norm_num [decimalConcatenation, Nat.ofDigits] at hvalue
        omega
      · have hthree : 3 ∈ parts := by
          by_contra hthree
          have hpartsSubset : parts ⊆ {1, 2} := by
            intro x hx
            have hxBound := hsub hx
            have hxThree : x ≠ 3 := by
              intro hxEq
              subst x
              exact hthree hx
            have hxFour : x ≠ 4 := by
              intro hxEq
              subst x
              exact hfour hx
            simp at hxBound ⊢
            omega
          have hle : (∑ x ∈ parts, x) ≤ ∑ x ∈ ({1, 2} : Finset ℕ), x :=
            Finset.sum_le_sum_of_subset hpartsSubset
          norm_num at hle
          omega
        have hrest : ∑ x ∈ parts.erase 3, x = 1 := by
          have hdecomp : (∑ x ∈ parts.erase 3, x) + 3 = ∑ x ∈ parts, x := by
            simpa only [id_eq] using Finset.sum_erase_add parts id hthree
          omega
        have htwo : 2 ∉ parts := by
          intro htwo
          have hsingleton : ({2} : Finset ℕ) ⊆ parts.erase 3 := by
            intro x hx
            simp at hx
            subst x
            simp [htwo]
          have hle : (∑ x ∈ ({2} : Finset ℕ), x) ≤ ∑ x ∈ parts.erase 3, x :=
            Finset.sum_le_sum_of_subset hsingleton
          norm_num at hle
          omega
        have hone : 1 ∈ parts := by
          by_contra hone
          have hrestEmpty : parts.erase 3 = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro x hx
            have hxParts := Finset.mem_of_mem_erase hx
            have hxThree := (Finset.mem_erase.mp hx).1
            have hxBound := hsub hxParts
            have hxOne : x ≠ 1 := by
              intro hxEq
              subst x
              exact hone hxParts
            have hxTwo : x ≠ 2 := by
              intro hxEq
              subst x
              exact htwo hxParts
            have hxFour : x ≠ 4 := by
              intro hxEq
              subst x
              exact hfour hxParts
            simp at hxBound
            omega
          rw [hrestEmpty] at hrest
          norm_num at hrest
        have hpartsEq : parts = {1, 3} := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hx
            have hxBound := hsub hx
            have hxTwo : x ≠ 2 := by
              intro hxEq
              subst x
              exact htwo hx
            have hxFour : x ≠ 4 := by
              intro hxEq
              subst x
              exact hfour hx
            simp at hxBound
            omega
          · rintro (rfl | rfl)
            · exact hone
            · exact hthree
        have hcanonical : ([1, 3] : List ℕ).Perm parts.sort :=
          (List.perm_ext_iff_of_nodup (by simp) (Finset.sort_nodup _ _)).2
            (by simp [hpartsEq])
        have horderedPair : ordered.Perm [1, 3] := hordered.trans hcanonical.symm
        rcases List.perm_pair.mp horderedPair with horderedEq | horderedEq
        · subst ordered
          norm_num [decimalConcatenation, Nat.ofDigits] at hvalue
          subst m
          exact hEligible.2 (by decide)
        · subst ordered
          norm_num [decimalConcatenation, Nat.ofDigits] at hvalue
          subst m
          exact hEligible.2 (by decide)

#print axioms murthy_conjecture

end D5.S1.Digit.Admissibility.DistinctPartitionConcatenationComposite
