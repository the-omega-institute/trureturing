/- GID: D5/S3/ObserverMemory/InverseLimits/FactorImageCardinality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/FactorImageCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor maps preserve finite iterate image cardinality. -/

import Mathlib.Data.Set.Card
import Mathlib.Logic.Function.Iterate

/- Library-search audit trail (2026-08-17):
   * Pinned Mathlib supplies `Function.Semiconj.iterate_right` for transporting
     semiconjugacy through iterates and `Set.ncard_image_le` for the finite image
     cardinality bound; both are applied below.
   * `Set.ncard_le_ncard` is the corresponding subset comparison used in local
     repository proofs, but the image lemma is the precise match here.
   * D5 searches found no declaration combining a surjective semiconjugacy with
     an iterate-image equality and cardinality bound. LeanSearch's public API was
     not used in this pass; the local pinned search and source inspection supplied
     the exact declarations above.
-/

namespace D5.S3.ObserverMemory.InverseLimits.FactorImageCardinality

/-- A surjective semiconjugacy carries every iterate image onto the corresponding
    factor image, so finite image cardinality cannot increase under factoring. -/
theorem factor_iterate_range_image_and_cardinality
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (phi : Y -> Z) (tau : Y -> Y) (sigma : Z -> Z)
    (hphi : Function.Surjective phi)
    (hsemiconj : Function.Semiconj phi tau sigma) (k : Nat) :
    phi '' Set.range (tau^[k]) = Set.range (sigma^[k]) /\
      (Set.range (sigma^[k])).ncard <= (Set.range (tau^[k])).ncard := by
  have hiter : Function.Semiconj phi (tau^[k]) (sigma^[k]) :=
    hsemiconj.iterate_right k
  have himage : phi '' Set.range (tau^[k]) = Set.range (sigma^[k]) := by
    apply Set.Subset.antisymm
    · rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨phi x, (hiter x).symm⟩
    · rintro z ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := hphi x
      exact ⟨(tau^[k]) y, ⟨y, rfl⟩, by simpa [hy] using hiter y⟩
  refine ⟨himage, ?_⟩
  rw [← himage]
  exact Set.ncard_image_le

#print axioms factor_iterate_range_image_and_cardinality

end D5.S3.ObserverMemory.InverseLimits.FactorImageCardinality
