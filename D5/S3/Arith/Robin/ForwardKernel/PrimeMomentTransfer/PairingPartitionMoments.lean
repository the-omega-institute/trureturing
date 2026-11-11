/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionMoments
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Retained singleton-block moments are the original moments on uncovered labels. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PairingPartitionCorrespondence
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CollisionComponentFactor

/-! The degree-zero retained-block moment is unchanged by its identification with labels. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

private theorem pairingPartition_retained_singleton {k : ℕ} (D : PairingPartitionData k)
    (B : D.retained) : partitionLabelBlock D.partition B.val = {B.val.out} := by
  have hout : B.val.out ∈ partitionLabelBlock D.partition B.val := by
    simp [partitionLabelBlock, Quotient.out_eq]
  have hc : (partitionLabelBlock D.partition B.val).card = 1 := by
    change mult (Quotient.mk D.partition) B.val = 1
    simpa only [if_pos B.property] using D.sizes B.val
  exact Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hout, fun i hi => Finset.card_le_one.mp hc.le i hi B.val.out hout⟩

/-- Each retained singleton block is identified with its unique uncovered position. -/
def pairingPartitionRetainedEquiv {k : ℕ} (D : PairingPartitionData k) :
    D.retained ≃ ↥((pairingSupport (pairingPartitionPairs D))ᶜ) where
  toFun B := ⟨B.val.out, by
    rw [Finset.mem_compl, pairingPartitionPairs_support]
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Quotient.out_eq, not_not]
      using B.property⟩
  invFun i := ⟨Quotient.mk D.partition i.val, by
    simpa only [Finset.mem_compl, pairingPartitionPairs_support,
      Finset.mem_filter, Finset.mem_univ, true_and, not_not] using i.property⟩
  left_inv B := by
    apply Subtype.ext
    exact Quotient.out_eq B.val
  right_inv i := by
    apply Subtype.ext
    have hB : Quotient.mk D.partition i.val ∈ D.retained := by
      simpa only [Finset.mem_compl, pairingPartitionPairs_support,
        Finset.mem_filter, Finset.mem_univ, true_and, not_not] using i.property
    have hi : i.val ∈ partitionLabelBlock D.partition (Quotient.mk D.partition i.val) := by
      simp [partitionLabelBlock]
    rw [pairingPartition_retained_singleton D ⟨_, hB⟩] at hi
    exact (Finset.mem_singleton.mp hi).symm

/-- The signed injective moment of the retained singleton-block weights is exactly
the ordered distinct-index moment of the original weights on uncovered labels. -/
theorem pairingPartition_retained_moment {ι A : Type*} [Fintype ι]
    [CommRing A] [Algebra ℝ A] {k : ℕ} (D : PairingPartitionData k)
    (ℓ : A →ₗ[ℝ] ℝ) (Y : ι → A) (f : Fin k → ι → ℝ) :
    (∑ x : D.retained → ι with Function.Injective x,
      (∏ B : D.retained, ∏ i ∈ partitionLabelBlock D.partition B.val, f i (x B)) *
        ℓ (∏ B : D.retained, Y (x B))) =
      distinctIndexMoment ℓ Y
        (fun j : Fin (Fintype.card ↥((pairingSupport (pairingPartitionPairs D))ᶜ)) =>
          f (((Fintype.equivFin ↥((pairingSupport (pairingPartitionPairs D))ᶜ)).symm j).val)) := by
  let e := (pairingPartitionRetainedEquiv D).trans
    (Fintype.equivFin ↥((pairingSupport (pairingPartitionPairs D))ᶜ))
  have h := assignment_moment_reindex ℓ Y e
    (fun B : D.retained => f ((pairingPartitionRetainedEquiv D) B).val)
  simp only [e, Equiv.symm_trans_apply, Equiv.apply_symm_apply] at h
  simpa only [pairingPartition_retained_singleton D, Finset.prod_singleton,
    pairingPartitionRetainedEquiv, Equiv.coe_fn_mk] using h

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
