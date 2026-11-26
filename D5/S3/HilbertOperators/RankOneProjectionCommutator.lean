/- GID: D5/S3/HilbertOperators/RankOneProjectionCommutator
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/RankOneProjectionCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A rank-one commutator with an orthogonal projection has an exact operator norm. -/

import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! The operator norm is the product of the norms of the two projected components. -/

namespace D5.S3.HilbertOperators.RankOneProjectionCommutator

open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜] [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The rank-one commutator has the same norm as either of its rank-one cross terms. -/
theorem norm_rankOne_projection_commutator (P : H →L[𝕜] H)
    (hP : P.toLinearMap.IsSymmetricProjection) (v : H) :
    ‖rankOne 𝕜 v v ∘L P - P ∘L rankOne 𝕜 v v‖ = ‖P v‖ * ‖v - P v‖ := by
  let C := rankOne 𝕜 v v ∘L P - P ∘L rankOne 𝕜 v v
  change ‖C‖ = _
  have hfix (x : H) : P (P x) = P x :=
    congrArg (fun T : H →ₗ[𝕜] H => T x) hP.isIdempotentElem
  have horth (x y : H) : ⟪P x, y - P y⟫_𝕜 = 0 := by
    rw [hP.isSymmetric.apply_clm, map_sub, hfix, sub_self, inner_zero_right]
  have horth' (x y : H) : ⟪x - P x, P y⟫_𝕜 = 0 := inner_eq_zero_symm.mp (horth y x)
  have hC (x : H) : C x = ⟪P v, x⟫_𝕜 • (v - P v) - ⟪v - P v, x⟫_𝕜 • P v := by
    simp only [C, sub_apply, comp_apply, rankOne_apply, map_smul, ← hP.isSymmetric.apply_clm v x,
      smul_sub, inner_sub_left, sub_smul, sub_sub_sub_cancel_right]
  apply le_antisymm
  · apply opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro x
    have hsplit : P x + (x - P x) = x := add_sub_cancel ..
    have hleft : ⟪P v, x⟫_𝕜 = ⟪P v, P x⟫_𝕜 := by
      rw [← hP.isSymmetric.apply_clm, hfix]
    have hright : ⟪v - P v, x⟫_𝕜 = ⟪v - P v, x - P x⟫_𝕜 := by
      rw [inner_sub_right, horth', sub_zero]
    have hpyth : ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 := by
      simpa only [pow_two, hsplit] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (horth x x)).symm
    rw [hC, hleft, hright, sub_eq_add_neg]
    have hcross :
        ⟪⟪P v, P x⟫_𝕜 • (v - P v), -(⟪v - P v, x - P x⟫_𝕜 • P v)⟫_𝕜 = 0 := by
      rw [inner_neg_right, inner_smul_left, inner_smul_right, horth', mul_zero, mul_zero,
        neg_zero]
    apply le_of_sq_le_sq _ (by positivity)
    calc
      _ = (‖⟪P v, P x⟫_𝕜‖ * ‖v - P v‖) ^ 2 +
          (‖⟪v - P v, x - P x⟫_𝕜‖ * ‖P v‖) ^ 2 := by
        simpa only [pow_two, norm_neg, norm_smul] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hcross
      _ ≤ (‖P v‖ * ‖P x‖ * ‖v - P v‖) ^ 2 +
          (‖v - P v‖ * ‖x - P x‖ * ‖P v‖) ^ 2 := by
        gcongr
        · exact norm_inner_le_norm _ _
        · exact norm_inner_le_norm _ _
      _ = (‖P v‖ * ‖v - P v‖ * ‖x‖) ^ 2 := by
        calc
          _ = (‖P v‖ * ‖v - P v‖) ^ 2 * (‖P x‖ ^ 2 + ‖x - P x‖ ^ 2) := by ring
          _ = _ := by rw [hpyth]; ring
  · by_cases hz : ‖P v‖ = 0
    · rw [hz, zero_mul]
      exact norm_nonneg _
    have htest : ‖C (P v)‖ = ‖P v‖ * ‖v - P v‖ * ‖P v‖ := by
      rw [hC, horth', zero_smul, sub_zero, norm_smul, inner_self_eq_norm_sq_to_K,
        norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      ring
    apply le_of_mul_le_mul_right _ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))
    rw [← htest]
    exact le_opNorm C (P v)

end D5.S3.HilbertOperators.RankOneProjectionCommutator
