/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPositivity4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondPositivity4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ambient positivity from regulated boundary limits and frequency reflection. -/

import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondWeakBoundary4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondMultipliers4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Positivity of the massive covariance and its frequency-reflected counterpart. -/

noncomputable section

open Filter ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder Topology

namespace NullConeGravity

/-- The weak limit of nonnegative shell squares gives positivity on the ambient space. -/
theorem nullB_nonneg {M : ℝ} (hM : 0 < M) : 0 ≤ nullA + nullT M hM := by
  apply nonneg_iff_isPositive.mpr
  refine isPositive_def'.mpr ⟨(nonneg_iff_isPositive.mp nullA_nonneg).isSelfAdjoint.add
    (nullT_selfAdjoint M hM), ?_⟩
  intro f
  change 0 ≤ RCLike.re ⟪(nullA + nullT M hM) f, f⟫_ℂ
  rw [inner_re_symm (𝕜 := ℂ)]
  change 0 ≤ (⟪f, (nullA + nullT M hM) f⟫_ℂ).re
  refine profileEmbed_dense.induction_on f (isClosed_le continuous_const (by fun_prop)) ?_
  intro F
  exact ge_of_tendsto' (massive_boundary_limit hM F) (fun ε => regulatedShellQuad_nonneg M ε F)

private theorem conjugate_re_inner (f g : H4D) :
    (⟪nullConj f, nullConj g⟫_ℂ).re = (⟪f, g⟫_ℂ).re := by
  change RCLike.re ⟪nullConj f, nullConj g⟫_ℂ = RCLike.re ⟪f, g⟫_ℂ
  simp only [re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
    ← map_add, ← map_sub, LinearIsometryEquiv.norm_map]

/-- Conjugating the ambient covariance reverses the sign of the skew multiplier. -/
theorem nullN_sub_J_nonneg {M : ℝ} (hM : 0 < M) :
    0 ≤ (1 : H4D →L[ℂ] H4D) + nullT M hM - nullJ := by
  have hJ := (nonneg_iff_isPositive.mp nullA_nonneg).isSelfAdjoint.sub (IsSelfAdjoint.one _)
  apply nonneg_iff_isPositive.mpr
  refine isPositive_def'.mpr ⟨((IsSelfAdjoint.one _).add (nullT_selfAdjoint M hM)).sub hJ, ?_⟩
  intro f
  have h := (nonneg_iff_isPositive.mp (nullB_nonneg hM)).re_inner_nonneg_left (nullConj f)
  have he : nullA + nullT M hM = 1 + nullT M hM + nullJ := by
    unfold nullJ
    abel
  rw [he] at h
  have hconj : nullConj ((1 + nullT M hM - nullJ) f) =
      (1 + nullT M hM + nullJ) (nullConj f) := by
    simp only [sub_apply, add_apply, one_apply_eq_self, map_sub, map_add, nullConj_comm_T, nullConj_anti_J,
      sub_neg_eq_add]
  change 0 ≤ (⟪(1 + nullT M hM - nullJ) f, f⟫_ℂ).re
  rw [← conjugate_re_inner, hconj]
  exact h

end NullConeGravity
