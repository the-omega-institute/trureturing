/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite quadratic moment propagates its partial-pairing defects with a uniform error. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.GradedMomentTransfer
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingDefectAlgebra
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingPartitionMoments

/-! The finite arbitrary-order pairing-defect transfer theorem. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]

private theorem partitionMainResidual_pairing {k : ℕ} (D : PairingPartitionData k)
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ) :
    partitionMainResidual ℓ Y f D.partition D.retained =
      (∏ E ∈ pairingPartitionPairs D, subsetWeightSum f E) *
        subsetDistinctMoment ℓ Y f (Finset.univ \ pairingSupport (pairingPartitionPairs D)) := by
  have hfree : (∏ B ∈ D.retainedᶜ, ∑ d, collisionComponentWeight D.partition f B d) =
      ∏ E ∈ pairingPartitionPairs D, subsetWeightSum f E := by
    rw [pairingPartitionPairs, Finset.prod_image (partitionLabelBlock_injective D.partition).injOn]
    rfl
  have hret : distinctIndexMoment ℓ Y
      (fun i : Fin (Fintype.card D.retained) =>
        collisionComponentWeight D.partition f ((Fintype.equivFin D.retained).symm i)) =
      subsetDistinctMoment ℓ Y f
        (Finset.univ \ pairingSupport (pairingPartitionPairs D)) := by
    rw [← retained_assignment_reindex ℓ Y D.retained (collisionComponentWeight D.partition f)]
    simpa only [collisionComponentWeight, partitionLabelBlock, subsetDistinctMoment,
      Finset.compl_eq_univ_sdiff] using pairingPartition_retained_moment D ℓ Y f
  rw [partitionMainResidual, hfree, hret]

private theorem zero_degree_sum_eq_partial_pairings {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ) (a b : ℝ) :
    (∑ σ ∈ tupleKernelPatterns k (Fin k), ∑ S : Finset (Quotient σ),
      if (∀ B, mult (Quotient.mk σ) B = if B ∈ S then 1 else 2) then
        partitionCoefficient σ S a b * partitionMainResidual ℓ Y f σ S else 0) =
      ∑ P : Finset (Finset (Fin k)) with IsPartialPairing Finset.univ P,
        b ^ P.card * (∏ E ∈ P, subsetWeightSum f E) *
          subsetDistinctMoment ℓ Y f (Finset.univ \ pairingSupport P) := by
  let G : {P : Finset (Finset (Fin k)) // IsPartialPairing Finset.univ P} → ℝ :=
    fun P => b ^ P.val.card * (∏ E ∈ P.val, subsetWeightSum f E) *
      subsetDistinctMoment ℓ Y f (Finset.univ \ pairingSupport P.val)
  calc
    _ = ∑ σ ∈ tupleKernelPatterns k (Fin k), ∑ S : Finset (Quotient σ),
        if hs : ∀ B, mult (Quotient.mk σ) B = if B ∈ S then 1 else 2 then
          G ⟨pairingPartitionPairs ⟨σ, S, hs⟩,
            pairingPartitionPairs_isPartial ⟨σ, S, hs⟩⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro σ hσ
      apply Finset.sum_congr rfl
      intro S hS
      split_ifs with hs
      · let D : PairingPartitionData k := ⟨σ, S, hs⟩
        change partitionCoefficient D.partition D.retained a b *
          partitionMainResidual ℓ Y f D.partition D.retained = _
        rw [partitionCoefficient, pairingPartition_coefficient D,
          partitionMainResidual_pairing D ℓ Y f]
        dsimp only [G, D]
        ring
      · rfl
    _ = ∑ P, G P := sum_pairing_partition_configurations G
    _ = _ := by
      apply Finset.sum_bij (fun P _ => P.val)
      · intro P hP
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, P.property⟩
      · intro P hP Q hQ h
        exact Subtype.ext h
      · intro P hP
        exact ⟨⟨P, (Finset.mem_filter.mp hP).2⟩, Finset.mem_univ _, rfl⟩
      · intro P hP
        rfl

/-- An explicit constant depending only on the order and the hypothesis constant. -/
def pairingDefectConstant (k : ℕ) (C : ℝ) : ℝ :=
  (k ^ k * 2 ^ k : ℕ) * (2 : ℝ) ^ (k * k) * (C + 1) ^ (k + 1)

/-- The original moment and its covariance pairing defect have the same partial-pairing
remainder, bounded uniformly without any upper bound on the top distinct-index moment. -/
theorem quadratic_pairing_defect_transfer {k : ℕ}
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ)
    (a b C H L : ℝ) (hC : 1 ≤ C) (hHL : L ≤ H) (hL : 1 ≤ L)
    (ha : |a| ≤ C * L) (hb : |b| ≤ C * L)
    (hquad : ∀ d, Y d ^ 2 = a • Y d + b • (1 : A))
    (hunit : ℓ 1 = 1) (hcenter : ∀ d, ℓ (Y d) = 0)
    (hD : (Fintype.card ι : ℝ) ≤ C * H) (hf : ∀ i d, |f i d| ≤ 1)
    (hR : DisjointLabelMomentBound ℓ Y f C (Real.sqrt (H * L))) :
    ∃ E : ℝ,
      quadraticFamilyMoment ℓ Y f =
        (∑ P : Finset (Finset (Fin k)) with IsPartialPairing Finset.univ P,
          b ^ P.card * (∏ e ∈ P, subsetWeightSum f e) *
            subsetDistinctMoment ℓ Y f (Finset.univ \ pairingSupport P)) + E ∧
      quadraticFamilyMoment ℓ Y f -
          finitePairingPolynomial Finset.univ (subsetFamilyMoment ℓ Y f) =
        (∑ P : Finset (Finset (Fin k)) with IsPartialPairing Finset.univ P,
          b ^ P.card * (∏ e ∈ P, subsetWeightSum f e) *
            subsetPairingDefect ℓ Y f (Finset.univ \ pairingSupport P)) + E ∧
      |E| ≤ pairingDefectConstant k C * (Real.sqrt (H * L)) ^ k *
        (Real.sqrt (L / H) + 1 / H) := by
  let main := ∑ P : Finset (Finset (Fin k)) with IsPartialPairing Finset.univ P,
    b ^ P.card * (∏ e ∈ P, subsetWeightSum f e) *
      subsetDistinctMoment ℓ Y f (Finset.univ \ pairingSupport P)
  let E := quadraticFamilyMoment ℓ Y f - main
  refine ⟨E, ?_, ?_, ?_⟩
  · dsimp only [E]
    ring
  · have hcov := subset_pairing_defect_convolution ℓ Y a b hunit hcenter
      (fun d => by simpa only [Algebra.smul_def, mul_one] using hquad d) f Finset.univ
    change main - _ = _ at hcov
    dsimp only [E]
    linarith [hcov]
  · have hbound := quadratic_moment_graded_transfer_bound ℓ Y f a b C H L hC hHL hL
      ha hb hquad hunit hcenter hD hf hR
    rw [zero_degree_sum_eq_partial_pairings ℓ Y f a b] at hbound
    simpa only [E, main, pairingDefectConstant, mul_assoc] using hbound

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
