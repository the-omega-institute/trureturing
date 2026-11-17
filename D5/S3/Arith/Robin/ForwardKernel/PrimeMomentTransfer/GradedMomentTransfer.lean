/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/GradedMomentTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/GradedMomentTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The zero-degree collision terms approximate every finite quadratic moment with a uniform error. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.AllPartitionExpansion
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartitionCoefficientStructure
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CollisionGradingEstimate

/-! The degree decomposition separates partial-pairing main terms from uniformly small errors. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]

private theorem partition_configuration_error_bound {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ))
    (a b C H L : ℝ) (hC : 1 ≤ C) (hHL : L ≤ H) (hL : 1 ≤ L)
    (ha : |a| ≤ C * L) (hb : |b| ≤ C * L)
    (hunit : ℓ 1 = 1) (hcenter : ∀ d, ℓ (Y d) = 0)
    (hD : (Fintype.card ι : ℝ) ≤ C * H) (hf : ∀ i d, |f i d| ≤ 1)
    (hR : DisjointLabelMomentBound ℓ Y f C (Real.sqrt (H * L))) :
    |partitionCoefficient σ S a b * kernelDistinctMoment ℓ Y f σ S -
      (if (∀ B, mult (Quotient.mk σ) B = if B ∈ S then 1 else 2) then
        partitionCoefficient σ S a b * partitionMainResidual ℓ Y f σ S else 0)| ≤
      (2 : ℝ) ^ (k * k) * (C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k *
        (Real.sqrt (L / H) + 1 / H) := by
  classical
  have hH : 0 < H := by linarith
  have hH1 : 1 ≤ H := le_trans hL hHL
  have hL0 : 0 ≤ L := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hM : 0 ≤ (C + 1) * L := mul_nonneg (by linarith) hL0
  by_cases hc : partitionCoefficient σ S a b = 0
  · simp only [hc, zero_mul, ite_self, sub_self, abs_zero]
    positivity
  by_cases hr1 : S.card = 1
  · rw [kernelDistinctMoment_zero_of_retained_card_one ℓ Y f σ S hr1 hcenter,
      partitionMainResidual_zero_of_retained_card_one ℓ Y f σ S hr1 hcenter]
    simp only [mul_zero, ite_self, sub_self, abs_zero]
    positivity
  let m : Quotient σ → ℕ := mult (Quotient.mk σ)
  let q := Sᶜ.card
  let r := S.card
  let δ := (∑ B ∈ S, (m B - 1)) + ∑ B ∈ Sᶜ, (m B - 2)
  have hret : ∀ B ∈ S, 1 ≤ m B := fun B _ => quotient_mult_pos σ B
  have hfree : ∀ B ∉ S, 2 ≤ m B :=
    partitionCoefficient_nonzero_free_mult σ S a b hc
  have hsum : (∑ B, m B) = k := sum_quotient_multiplicities σ
  have hdeg : k = 2 * q + r + δ := by
    have h := collision_degree_decomposition m S hret hfree
    simpa only [hsum] using h
  have hcount : Fintype.card (Quotient σ) = q + r := by
    exact (Finset.card_compl_add_card S).symm
  have htk : Fintype.card (Quotient σ) ≤ k := by omega
  have hcBound : |partitionCoefficient σ S a b| ≤
      ((C + 1) * L) ^ (k - Fintype.card (Quotient σ)) :=
    partition_coefficient_bound σ S a b C L hC hL ha hb
  have hgraded := collision_partition_grading_bound m S hret hfree C H L hC hH hL0
  simp only [hsum] at hgraded
  have hgood : (∀ B, m B = if B ∈ S then 1 else 2) ↔ δ = 0 := by
    rw [hgraded.2]
    constructor
    · intro hg
      exact ⟨fun B hB => by simpa only [if_pos hB] using hg B,
        fun B hB => by simpa only [if_neg hB] using hg B⟩
    · rintro ⟨hr, hf⟩ B
      split_ifs with hB
      · exact hr B hB
      · exact hf B hB
  have hedge : (2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) ≤
      (2 : ℝ) ^ (k * k) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul htk htk)
  have henv (α : ℝ) (hα : 0 ≤ α) :
      (2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
        (C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k * α ≤
      (2 : ℝ) ^ (k * k) * (C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k * α := by
    apply mul_le_mul_of_nonneg_right _ hα
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Real.sqrt_nonneg _) _)
    exact mul_le_mul_of_nonneg_right hedge (pow_nonneg (by linarith) _)
  by_cases hg : ∀ B, m B = if B ∈ S then 1 else 2
  · have hδ : δ = 0 := hgood.mp hg
    have hk : k = 2 * q + r := by omega
    change |partitionCoefficient σ S a b * kernelDistinctMoment ℓ Y f σ S -
      (if (∀ B, m B = if B ∈ S then 1 else 2) then
        partitionCoefficient σ S a b * partitionMainResidual ℓ Y f σ S else 0)| ≤ _
    rw [if_pos hg]
    by_cases hq0 : q = 0
    · rw [kernelDistinctMoment_eq_main_of_compl_card_zero ℓ Y f σ S hq0,
        sub_self, abs_zero]
      positivity
    have hq : 1 ≤ q := by omega
    have hrk : S.card < k := by change r < k; omega
    have hJ := (kernelDistinctMoment_collision_estimates ℓ Y f σ S C H
      (Real.sqrt (H * L)) hC hH1 (Real.sqrt_nonneg _) hunit hcenter hD hf hR hrk).2 hq
    have hscale : ((C + 1) * L) ^ (k - Fintype.card (Quotient σ)) *
        C ^ q * H ^ (q - 1) * (Real.sqrt (H * L)) ^ r ≤
      ((C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k) / H := by
      have h := collision_free_component_bound C H L hC hH hL0 (q - 1) r
      rw [Nat.sub_add_cancel hq, ← hk] at h
      have hexp : k - Fintype.card (Quotient σ) = q := by omega
      simpa only [hexp] using h
    calc
      _ = |partitionCoefficient σ S a b| *
          |kernelDistinctMoment ℓ Y f σ S - partitionMainResidual ℓ Y f σ S| := by
        rw [← mul_sub, abs_mul]
      _ ≤ ((C + 1) * L) ^ (k - Fintype.card (Quotient σ)) *
          ((2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
            C ^ q * H ^ (q - 1) * (Real.sqrt (H * L)) ^ r) := by
        exact mul_le_mul hcBound hJ (abs_nonneg _) (pow_nonneg hM _)
      _ = (2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
          (((C + 1) * L) ^ (k - Fintype.card (Quotient σ)) *
            C ^ q * H ^ (q - 1) * (Real.sqrt (H * L)) ^ r) := by ring
      _ ≤ (2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
          (((C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k) / H) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
          (C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k * (1 / H) := by ring
      _ ≤ (2 : ℝ) ^ (k * k) * (C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k *
          (1 / H) := henv _ (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (Real.sqrt_nonneg (L / H))) (by positivity)
  · have hδ : 1 ≤ δ := by
      have : δ ≠ 0 := fun h => hg (hgood.mpr h)
      omega
    have hrk : S.card < k := by change r < k; omega
    have hJ := (kernelDistinctMoment_collision_estimates ℓ Y f σ S C H
      (Real.sqrt (H * L)) hC hH1 (Real.sqrt_nonneg _) hunit hcenter hD hf hR hrk).1
    have hscale : ((C + 1) * L) ^ (k - Fintype.card (Quotient σ)) *
        C ^ (q + 1) * H ^ q * (Real.sqrt (H * L)) ^ r ≤
      (C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k * Real.sqrt (L / H) := by
      have hexp : k - Fintype.card (Quotient σ) = q + δ := by omega
      rw [hexp, hdeg]
      exact collision_positive_grading_bound C H L hC hHL hL q r δ hδ
    change |partitionCoefficient σ S a b * kernelDistinctMoment ℓ Y f σ S -
      (if (∀ B, m B = if B ∈ S then 1 else 2) then
        partitionCoefficient σ S a b * partitionMainResidual ℓ Y f σ S else 0)| ≤ _
    rw [if_neg hg, sub_zero, abs_mul]
    calc
      _ ≤ ((C + 1) * L) ^ (k - Fintype.card (Quotient σ)) *
          ((2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
            C ^ (q + 1) * H ^ q * (Real.sqrt (H * L)) ^ r) :=
        mul_le_mul hcBound hJ (abs_nonneg _) (pow_nonneg hM _)
      _ = (2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
          (((C + 1) * L) ^ (k - Fintype.card (Quotient σ)) *
            C ^ (q + 1) * H ^ q * (Real.sqrt (H * L)) ^ r) := by ring
      _ ≤ (2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
          ((C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k * Real.sqrt (L / H)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (2 : ℝ) ^ (Fintype.card (Quotient σ) * Fintype.card (Quotient σ)) *
          (C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k * Real.sqrt (L / H) := by ring
      _ ≤ (2 : ℝ) ^ (k * k) * (C + 1) ^ (k + 1) * (Real.sqrt (H * L)) ^ k *
          Real.sqrt (L / H) := henv _ (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (by positivity : 0 ≤ 1 / H)) (by positivity)

/-- At every finite order the zero-degree partition terms approximate the moment,
with a constant depending only on the order and the common hypothesis constant. -/
theorem quadratic_moment_graded_transfer_bound {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (a b C H L : ℝ) (hC : 1 ≤ C) (hHL : L ≤ H) (hL : 1 ≤ L)
    (ha : |a| ≤ C * L) (hb : |b| ≤ C * L)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + b • (1 : A))
    (hunit : ℓ 1 = 1) (hcenter : ∀ d, ℓ (Y d) = 0)
    (hD : (Fintype.card ι : ℝ) ≤ C * H) (hf : ∀ i d, |f i d| ≤ 1)
    (hR : DisjointLabelMomentBound ℓ Y f C (Real.sqrt (H * L))) :
    |quadraticFamilyMoment ℓ Y f -
      (∑ σ ∈ tupleKernelPatterns k (Fin k), ∑ S : Finset (Quotient σ),
        if (∀ B, mult (Quotient.mk σ) B = if B ∈ S then 1 else 2) then
          partitionCoefficient σ S a b * partitionMainResidual ℓ Y f σ S else 0)| ≤
      (k ^ k * 2 ^ k : ℕ) * (2 : ℝ) ^ (k * k) * (C + 1) ^ (k + 1) *
        (Real.sqrt (H * L)) ^ k * (Real.sqrt (L / H) + 1 / H) := by
  classical
  let E := (2 : ℝ) ^ (k * k) * (C + 1) ^ (k + 1) *
    (Real.sqrt (H * L)) ^ k * (Real.sqrt (L / H) + 1 / H)
  have hH : 0 < H := by linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  rw [quadratic_moment_eq_all_partition_expansion ℓ Y a b hquad f]
  change |(∑ σ ∈ tupleKernelPatterns k (Fin k), ∑ S : Finset (Quotient σ),
      partitionCoefficient σ S a b * kernelDistinctMoment ℓ Y f σ S) - _| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ ∈ tupleKernelPatterns k (Fin k),
        |(∑ S : Finset (Quotient σ),
            partitionCoefficient σ S a b * kernelDistinctMoment ℓ Y f σ S) -
          ∑ S : Finset (Quotient σ),
            if (∀ B, mult (Quotient.mk σ) B = if B ∈ S then 1 else 2) then
              partitionCoefficient σ S a b * partitionMainResidual ℓ Y f σ S else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ ∈ tupleKernelPatterns k (Fin k), ∑ _S : Finset (Quotient σ), E := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro S hS
      exact partition_configuration_error_bound ℓ Y f σ S a b C H L hC hHL hL
        ha hb hunit hcenter hD hf hR
    _ = (∑ σ ∈ tupleKernelPatterns k (Fin k),
        (Fintype.card (Finset (Quotient σ)) : ℝ)) * E := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_mul]
    _ ≤ (k ^ k * 2 ^ k : ℕ) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      exact_mod_cast all_partition_configuration_bound k
    _ = _ := by dsimp only [E]; ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
