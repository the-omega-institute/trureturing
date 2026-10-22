import D5.S3.VertexAlgebra.BcGhostFockSupport

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostConformalFiniteComparison

noncomputable section

variable {Space : Type*} [AddCommGroup Space]

theorem descending_common_interval (terms : ℤ → Space) (lower upper split : ℤ)
    (lowerSplit : lower ≤ split) (splitUpper : split ≤ upper)
    (support : Function.support terms ⊆ Set.Icc lower upper) :
    (∑ᶠ offset : ℕ, terms (split - offset)) =
      ∑ index ∈ Finset.Icc lower upper, if index ≤ split then terms index else 0 := by
  classical
  have bound : 0 ≤ split - lower := by omega
  have boundCast := Int.toNat_of_nonneg bound
  rw [finsum_eq_sum_of_support_subset _
    (s := Finset.range ((split - lower).toNat + 1)) (by
      intro offset member
      have interval := support member
      simp only [Set.mem_Icc] at interval
      simp only [Finset.mem_coe, Finset.mem_range]
      omega)]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (offset : ℕ) _ => split - (offset : ℤ))
  · intro offset member
    simp only [Finset.mem_range] at member
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro first firstMember second secondMember equality
    omega
  · intro index member
    simp only [Finset.mem_filter, Finset.mem_Icc] at member
    refine ⟨(split - index).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      have indexCast := Int.toNat_of_nonneg (show 0 ≤ split - index by omega)
      omega
    · rw [Int.toNat_of_nonneg (by omega : 0 ≤ split - index)]
      omega
  · intro offset member
    rfl

theorem ascending_common_interval (terms : ℤ → Space) (lower upper split : ℤ)
    (lowerSplit : lower ≤ split) (splitUpper : split ≤ upper)
    (support : Function.support terms ⊆ Set.Icc lower upper) :
    (∑ᶠ offset : ℕ, terms (split + 1 + offset)) =
      ∑ index ∈ Finset.Icc lower upper, if split < index then terms index else 0 := by
  classical
  have bound : 0 ≤ upper - split := by omega
  have boundCast := Int.toNat_of_nonneg bound
  rw [finsum_eq_sum_of_support_subset _
    (s := Finset.range (upper - split).toNat) (by
      intro offset member
      have interval := support member
      simp only [Set.mem_Icc] at interval
      simp only [Finset.mem_coe, Finset.mem_range]
      omega)]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (offset : ℕ) _ => split + 1 + (offset : ℤ))
  · intro offset member
    simp only [Finset.mem_range] at member
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro first firstMember second secondMember equality
    omega
  · intro index member
    simp only [Finset.mem_filter, Finset.mem_Icc] at member
    refine ⟨(index - split - 1).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      have indexCast := Int.toNat_of_nonneg (show 0 ≤ index - split - 1 by omega)
      omega
    · rw [Int.toNat_of_nonneg (by omega : 0 ≤ index - split - 1)]
      omega
  · intro offset member
    rfl

theorem split_common_interval (terms : ℤ → Space) (lower upper split : ℤ)
    (lowerSplit : lower ≤ split) (splitUpper : split ≤ upper)
    (support : Function.support terms ⊆ Set.Icc lower upper) :
    (∑ᶠ offset : ℕ, terms (split - offset)) +
        (∑ᶠ offset : ℕ, terms (split + 1 + offset)) =
      ∑ index ∈ Finset.Icc lower upper, terms index := by
  rw [descending_common_interval terms lower upper split lowerSplit splitUpper support,
    ascending_common_interval terms lower upper split lowerSplit splitUpper support,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index member
  by_cases below : index ≤ split
  · simp [below, show ¬ split < index by omega]
  · simp [below, show split < index by omega]

end
end D5.S3.VertexAlgebra.BcGhostConformalFiniteComparison
