/- GID: D5/S3/Geometry/AffineBallRigidity
   generality: G
   mirror-B: D5/B/S3/Geometry/AffineBallRigidity
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Extreme]
   utility: none
   digest: An extreme affine sphere prevents a same-dimensional enclosing ball from being larger. -/

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-! Rigidity of affine balls with an extreme entire sphere. -/

noncomputable section
open Set Metric

namespace D5.S3.Geometry.AffineBallRigidity

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compact affine ball has a unique center, even when its linear part
has a kernel. The centers are points of the ambient affine carrier. -/
theorem center_eq_of_ball_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c d : V) (A : E →L[ℝ] V) (B : F →L[ℝ] V)
    (heq : (fun x => c + A x) '' closedBall 0 1 =
      (fun x => d + B x) '' closedBall 0 1) : c = d := by
  let S := (fun x => c + A x) '' closedBall 0 1
  have hS : IsCompact S := (isCompact_closedBall (0 : E) 1).image (by fun_prop)
  have hne : S.Nonempty := ⟨c, 0, by simp, by simp⟩
  have hrc (y : V) (hy : y ∈ S) : (2 : ℝ) • c - y ∈ S := by
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨-x, by simpa using hx, ?_⟩
    simp only [map_neg]
    module
  have hrd (y : V) (hy : y ∈ S) : (2 : ℝ) • d - y ∈ S := by
    change y ∈ (fun x => c + A x) '' closedBall 0 1 at hy
    change (2 : ℝ) • d - y ∈ (fun x => c + A x) '' closedBall 0 1
    rw [heq] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨-x, by simpa using hx, ?_⟩
    simp only [map_neg]
    module
  obtain ⟨l, hl, hln⟩ := exists_dual_vector'' ℝ (c - d)
  change l (c - d) = ‖c - d‖ at hln
  obtain ⟨m, hm, hmax⟩ := hS.exists_isMaxOn hne l.continuous.continuousOn
  have hh := hmax (hrc _ (hrd _ hm))
  change l ((2 : ℝ) • c - ((2 : ℝ) • d - m)) ≤ l m at hh
  simp only [map_sub, map_smul, smul_eq_mul] at hh hln
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (c-d)]))

omit [FiniteDimensional ℝ E] in
/-- Inclusion of affine unit balls entails inclusion of their linear directions. -/
private theorem range_le_of_ball_subset (c d : V) (A B : E →L[ℝ] V)
    (hsub : (fun x => c + A x) '' closedBall 0 1 ⊆
      (fun x => d + B x) '' closedBall 0 1) :
    A.toLinearMap.range ≤ B.toLinearMap.range := by
  have hc : c ∈ (fun x => d + B x) '' closedBall 0 1 :=
    hsub ⟨0, by simp, by simp⟩
  obtain ⟨z, hz, hzc⟩ := hc
  change d + B z = c at hzc
  have hunit (x : E) (hx : ‖x‖ ≤ 1) : A x ∈ B.toLinearMap.range := by
    obtain ⟨y, hy, hyx⟩ := hsub ⟨x, by simpa using hx, rfl⟩
    change d + B y = c + A x at hyx
    refine ⟨y - z, ?_⟩
    change B (y - z) = A x
    rw [map_sub]
    have : (d + B y) - (d + B z) = (c + A x) - c := by rw [hyx, hzc]
    simpa only [add_sub_add_left_eq_sub, add_sub_cancel_left] using this
  rintro _ ⟨x, rfl⟩
  by_cases hx : x = 0
  · simp [hx]
  have hu : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
    simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hh := B.toLinearMap.range.smul_mem ‖x‖ (hunit _ hu)
  simpa [map_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx)] using hh

/-- A full-dimensional affine ball whose entire sphere is extreme cannot be
properly contained in another injective affine ball of the same dimension. -/
theorem eq_of_subset_of_extreme_sphere (K : Set V) (c d : V)
    (A B : E →L[ℝ] V) (hA : Function.Injective A) (hB : Function.Injective B)
    (hsub : (fun x => c + A x) '' closedBall 0 1 ⊆
      (fun x => d + B x) '' closedBall 0 1)
    (hK : (fun x => d + B x) '' closedBall 0 1 ⊆ K)
    (hsphere : ∀ x : E, ‖x‖ = 1 → c + A x ∈ K.extremePoints ℝ) :
    (fun x => c + A x) '' closedBall 0 1 =
      (fun x => d + B x) '' closedBall 0 1 := by
  have hrange : A.toLinearMap.range = B.toLinearMap.range :=
    Submodule.eq_of_le_of_finrank_eq (range_le_of_ball_subset c d A B hsub)
      (by rw [LinearMap.finrank_range_of_inj hA, LinearMap.finrank_range_of_inj hB])
  have hc : c ∈ (fun x => d + B x) '' closedBall 0 1 :=
    hsub ⟨0, by simp, by simp⟩
  obtain ⟨z, hz, hzc⟩ := hc
  change d + B z = c at hzc
  apply Subset.antisymm hsub
  rintro y hy
  obtain ⟨w, hw, hwy⟩ := hy
  change d + B w = y at hwy
  have hyr : y - c ∈ A.toLinearMap.range := by
    rw [hrange]
    refine ⟨w - z, ?_⟩
    change B (w - z) = y - c
    rw [map_sub]
    rw [← hwy, ← hzc]
    abel_nf
  obtain ⟨v, hv⟩ := hyr
  have heq : c + A v = y := by
    change A v = y - c at hv
    rw [hv]
    abel
  have hn : ‖v‖ ≤ 1 := by
    by_contra h
    have hvn : 1 < ‖v‖ := lt_of_not_ge h
    have hp : 0 < ‖v‖ := lt_trans zero_lt_one hvn
    have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
      simp [norm_smul, hp.ne']
    have he := hsphere (‖v‖⁻¹ • v) hu
    have hseg : c + A (‖v‖⁻¹ • v) ∈ openSegment ℝ c y := by
      refine ⟨1 - ‖v‖⁻¹, ‖v‖⁻¹, ?_, inv_pos.mpr hp, by ring, ?_⟩
      · exact sub_pos.mpr ((inv_lt_one₀ hp).mpr hvn)
      · rw [← heq, map_smul, smul_add, sub_smul, one_smul]
        module
    have hzero : A (‖v‖⁻¹ • v) = 0 := by
      have hh := he.2 (hK ⟨z, hz, hzc⟩) (hK ⟨w, hw, hwy⟩) hseg
      exact add_left_cancel (hh.symm.trans (add_zero c).symm)
    have hvzero := hA (show A (‖v‖⁻¹ • v) = A 0 by simpa using hzero)
    have : ‖‖v‖⁻¹ • v‖ = 0 := by rw [hvzero, norm_zero]
    linarith
  exact ⟨v, by simpa using hn, heq⟩

#print axioms eq_of_subset_of_extreme_sphere
#print axioms center_eq_of_ball_eq

end D5.S3.Geometry.AffineBallRigidity
