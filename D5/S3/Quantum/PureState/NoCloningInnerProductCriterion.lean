/- GID: D5/S3/Quantum/PureState/NoCloningInnerProductCriterion
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/NoCloningInnerProductCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact unitary cloning forces unit-state overlap to be zero or one. -/

import Mathlib.Analysis.InnerProductSpace.TensorProduct

/- Library-search audit trail (2026-08-27):
   * Pinned Mathlib has no exact no-cloning theorem.
   * Exact hits `LinearIsometryEquiv.inner_map_map` and
     `TensorProduct.inner_tmul` compute the input and output overlaps.
   * Exact hits `eq_zero_or_one_of_sq_eq_self` and
     `inner_eq_one_iff_of_norm_eq_one` convert the overlap identity into the
     public identical-or-orthogonal alternative.
   * Current-tree searches found no theorem with both source clauses. No new
     definition or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.PureState.NoCloningInnerProductCriterion

open scoped InnerProductSpace TensorProduct

/-- If one complex linear isometric equivalence clones each of two normalized
vectors from the same normalized blank, their overlap is idempotent. Hence the
two input states are identical or orthogonal. -/
theorem no_cloning_inner_product_criterion
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    (U : (H ⊗[Complex] H) ≃ₗᵢ[Complex] (H ⊗[Complex] H))
    (psi phi blank : H)
    (psiNormalized : ‖psi‖ = 1) (phiNormalized : ‖phi‖ = 1)
    (blankNormalized : ‖blank‖ = 1)
    (clonesPsi : U (psi ⊗ₜ[Complex] blank) = psi ⊗ₜ[Complex] psi)
    (clonesPhi : U (phi ⊗ₜ[Complex] blank) = phi ⊗ₜ[Complex] phi) :
    inner Complex phi psi = inner Complex phi psi ^ 2 ∧
      (phi = psi ∨ inner Complex phi psi = 0) := by
  have blankOverlap : inner Complex blank blank = 1 :=
    inner_self_eq_one_of_norm_eq_one blankNormalized
  have overlapIdentity : inner Complex phi psi = inner Complex phi psi ^ 2 := by
    calc
      inner Complex phi psi =
          inner Complex phi psi * inner Complex blank blank := by
        rw [blankOverlap, mul_one]
      _ = inner Complex (phi ⊗ₜ[Complex] blank)
          (psi ⊗ₜ[Complex] blank) := by
        rw [TensorProduct.inner_tmul]
      _ = inner Complex (U (phi ⊗ₜ[Complex] blank))
          (U (psi ⊗ₜ[Complex] blank)) := by
        rw [U.inner_map_map]
      _ = inner Complex (phi ⊗ₜ[Complex] phi)
          (psi ⊗ₜ[Complex] psi) := by
        rw [clonesPhi, clonesPsi]
      _ = inner Complex phi psi * inner Complex phi psi := by
        rw [TensorProduct.inner_tmul]
      _ = inner Complex phi psi ^ 2 := by
        rw [pow_two]
  refine ⟨overlapIdentity, ?_⟩
  rcases eq_zero_or_one_of_sq_eq_self overlapIdentity.symm with overlapZero | overlapOne
  · exact Or.inr overlapZero
  · exact Or.inl
      ((inner_eq_one_iff_of_norm_eq_one phiNormalized psiNormalized).mp overlapOne)

#print axioms no_cloning_inner_product_criterion

end D5.S3.Quantum.PureState.NoCloningInnerProductCriterion
