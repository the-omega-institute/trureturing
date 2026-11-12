/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCoefficientStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonzero quadratic partition coefficients exclude free singleton blocks. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartitionCollisionExpansion

/-! The nonvanishing configurations have positive retained block sizes and free block
sizes at least two. If every block is retained, collision removal has no error. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- The product of the chosen linear and constant quadratic reduction coefficients. -/
def partitionCoefficient {k : ℕ} (σ : Setoid (Fin k)) (S : Finset (Quotient σ))
    (a b : ℝ) : ℝ :=
  (∏ B ∈ S, (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).1) *
    (∏ B ∈ Sᶜ, (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).2)

/-- The term in which only retained blocks are required to have distinct indices. -/
def partitionMainResidual {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]
    {k : ℕ} (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) : ℝ :=
  (∏ B ∈ Sᶜ, ∑ d, collisionComponentWeight σ f B d) *
    distinctIndexMoment ℓ Y (fun i : Fin (Fintype.card S) =>
      collisionComponentWeight σ f ((Fintype.equivFin S).symm i))

/-- An unretained singleton contributes v(1)=0. -/
theorem partitionCoefficient_zero_of_free_singleton {k : ℕ}
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) (a b : ℝ)
    (B : Quotient σ) (hB : B ∉ S) (hm : mult (Quotient.mk σ) B = 1) :
    partitionCoefficient σ S a b = 0 := by
  unfold partitionCoefficient
  have hz : (∏ B ∈ Sᶜ,
      (quadraticPowerCoeffs a b (mult (Quotient.mk σ) B)).2) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_compl.mpr hB)
    rw [hm]
    simp [quadraticPowerCoeffs]
  rw [hz, mul_zero]

/-- Every unretained block of a nonzero configuration has at least two labels. -/
theorem partitionCoefficient_nonzero_free_mult {k : ℕ}
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) (a b : ℝ)
    (hcoeff : partitionCoefficient σ S a b ≠ 0) :
    ∀ B ∉ S, 2 ≤ mult (Quotient.mk σ) B := by
  intro B hB
  have hp := quotient_mult_pos σ B
  by_contra hn
  have hm : mult (Quotient.mk σ) B = 1 := by omega
  exact hcoeff (partitionCoefficient_zero_of_free_singleton σ S a b B hB hm)

/-- With no free blocks, the collision removal is exact and retains the full top-order
moment without requiring any size estimate for it. -/
theorem kernelDistinctMoment_eq_main_of_compl_card_zero
    {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A] {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) (hq : Sᶜ.card = 0) :
    kernelDistinctMoment ℓ Y f σ S = partitionMainResidual ℓ Y f σ S := by
  have hempty : Sᶜ = ∅ := Finset.card_eq_zero.mp hq
  have hSuniv : S = Finset.univ := by
    ext B
    simp only [Finset.mem_univ, iff_true]
    by_contra hB
    have hmem := Finset.mem_compl.mpr hB
    rw [hempty] at hmem
    simp at hmem
  have hedge : collisionEdges S = ∅ := by
    rw [hSuniv]
    ext e
    simp [collisionEdges]
  rw [kernelDistinctMoment_eq_collision_assignment_sum, hedge]
  simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero,
    one_mul]
  exact collisionAssignmentMoment_empty ℓ Y (collisionComponentWeight σ f) S

/-- A single retained block vanishes by centering, before taking any absolute values. -/
theorem kernelDistinctMoment_zero_of_retained_card_one
    {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A] {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) (hS : S.card = 1)
    (hcenter : ∀ d, ℓ (Y d) = 0) : kernelDistinctMoment ℓ Y f σ S = 0 := by
  obtain ⟨B, rfl⟩ := Finset.card_eq_one.mp hS
  unfold kernelDistinctMoment
  apply Finset.sum_eq_zero
  intro d hd
  simp only [Finset.prod_singleton, hcenter, mul_zero]

/-- The main residual with a single retained block vanishes by the same centering. -/
theorem partitionMainResidual_zero_of_retained_card_one
    {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A] {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (σ : Setoid (Fin k)) (S : Finset (Quotient σ)) (hS : S.card = 1)
    (hcenter : ∀ d, ℓ (Y d) = 0) : partitionMainResidual ℓ Y f σ S = 0 := by
  rw [partitionMainResidual, ← collisionAssignmentMoment_empty]
  obtain ⟨B, rfl⟩ := Finset.card_eq_one.mp hS
  unfold collisionAssignmentMoment
  apply Finset.sum_eq_zero
  intro d hd
  simp only [Finset.prod_singleton, hcenter, mul_zero]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
