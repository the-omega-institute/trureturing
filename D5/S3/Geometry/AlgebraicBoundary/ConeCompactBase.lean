/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeCompactBase
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeCompactBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed salient finite real cones admit actual strictly positive compact-base functionals. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A positive normalization is constructed from the original cone by separation. -/

noncomputable section

open Set

namespace D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exists_positive_functional (C : ProperCone ℝ E)
    (hs : (C : ConvexCone ℝ E).Salient) :
    ∃ u : E →L[ℝ] ℝ, ∀ x ∈ C, x ≠ 0 → 0 < u x := by
  classical
  let S : Set E := {x | x ∈ C ∧ ‖x‖ = 1}
  have hS : IsCompact S := by
    convert (isCompact_sphere (0 : E) 1).inter_left C.isClosed using 1
    ext x
    simp [S]
  have hsep : ∀ x : S, ∃ f : E →L[ℝ] ℝ,
      (∀ y ∈ C, 0 ≤ f y) ∧ 0 < f x := by
    intro x
    have hx0 : (x : E) ≠ 0 := by
      intro h
      have hh := x.property.2
      simpa [h] using hh
    have hnot : -(x : E) ∉ C := hs _ x.property.1 hx0
    obtain ⟨f, hf, hfx⟩ := C.hyperplane_separation_point hnot
    refine ⟨f, hf, ?_⟩
    simpa only [map_neg, neg_lt_zero] using hfx
  choose F hF hFx using hsep
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun i : S => {y | 0 < F i y})
    (fun i => isOpen_lt continuous_const (F i).continuous) (by
      intro y hy
      simp only [mem_iUnion, mem_setOf_eq]
      exact ⟨⟨y, hy⟩, hFx ⟨y, hy⟩⟩)
  let u : E →L[ℝ] ℝ := ∑ i ∈ t, F i
  have hu : ∀ y, u y = ∑ i ∈ t, F i y := by
    intro y
    simp [u]
  refine ⟨u, ?_⟩
  intro y hy hy0
  let z : E := ‖y‖⁻¹ • y
  have hz : z ∈ S := by
    refine ⟨C.smul_mem hy (inv_nonneg.mpr (norm_nonneg y)), ?_⟩
    simp [z, norm_smul, norm_ne_zero_iff.mpr hy0]
  obtain ⟨i, hi, hiz⟩ : ∃ i ∈ t, 0 < F i z := by
    simpa only [mem_iUnion, mem_setOf_eq] using ht hz
  have hupos : 0 < u z := by
    rw [hu]
    exact Finset.sum_pos' (fun j hj => hF j z hz.1) ⟨i, hi, hiz⟩
  have hh : 0 < ‖y‖⁻¹ * u y := by simpa [z, map_smul] using hupos
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr (norm_pos_iff.mpr hy0))).mp hh

private theorem exists_positive_compact_base (C : ProperCone ℝ E)
    (hs : (C : ConvexCone ℝ E).Salient) :
    ∃ u : E →L[ℝ] ℝ, (∀ x ∈ C, x ≠ 0 → 0 < u x) ∧
      IsCompact {x : E | x ∈ C ∧ u x = 1} ∧
      Convex ℝ {x : E | x ∈ C ∧ u x = 1} := by
  obtain ⟨u, hu⟩ := exists_positive_functional C hs
  refine ⟨u, hu, ?_, ?_⟩
  · exact D5.S3.Quantum.Foundation.CircuitBalancedConfirmation.base_compact C.isClosed hu
  · exact D5.S3.Quantum.Foundation.CircuitBalancedConfirmation.base_convex
      C.toPointedCone u.toLinearMap

end D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase
