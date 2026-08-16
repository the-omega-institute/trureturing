/- GID: D5/S3/Quantum/Algebra/FiniteLayerProjectionEscape
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/FiniteLayerProjectionEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonzero orthogonal residual contains a unit vector at distance one. -/

import D5.S3.Quantum.Algebra.OrthogonalProjectionComplement
import Mathlib.Topology.MetricSpace.HausdorffDistance

/- Library-search audit trail (2026-08-16):
   * Repository search found the complementary-projection identity in
     `OrthogonalProjectionComplement`; it is imported and applied below.
   * Pinned-Mathlib search found `Submodule.starProjection_minimal`,
     `Submodule.norm_starProjection`, and `Submodule.exists_mem_ne_zero_of_ne_bot`.
   * Natural-language name searches found no exact theorem bundling the unit escape vector,
     its distance from the subspace, and the norm of the complementary projection. -/

noncomputable section

open scoped InnerProductSpace
open D5.S3.Quantum.Algebra.OrthogonalProjectionComplement

namespace D5.S3.Quantum.Algebra.FiniteLayerProjectionEscape

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- If a closed Hilbert subspace has a nonzero orthogonal residual, that residual contains a
unit vector annihilated by the subspace projection and lying at distance one from the subspace;
equivalently, the complementary projection has operator norm one. -/
theorem finite_layer_projection_escape
    (S : Submodule 𝕜 V) [IsClosed (S : Set V)] (hResidual : Sᗮ ≠ ⊥) :
    ∃ e : V, e ∈ Sᗮ ∧ ‖e‖ = 1 ∧ S.starProjection e = 0 ∧
      Metric.infDist e (S : Set V) = 1 ∧
      ‖ContinuousLinearMap.id 𝕜 V - S.starProjection‖ = 1 := by
  obtain ⟨x, hxResidual, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hResidual
  let e : V := (‖x‖ : 𝕜)⁻¹ • x
  have heResidual : e ∈ Sᗮ := Sᗮ.smul_mem _ hxResidual
  have hx_norm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx_ne
  have he_norm : ‖e‖ = 1 := by
    simp [e, norm_smul, hx_norm_ne]
  have he_projection : S.starProjection e = 0 := by
    rw [Submodule.starProjection_apply,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal heResidual]
    rfl
  refine ⟨e, heResidual, he_norm, he_projection, ?_, ?_⟩
  · calc
      Metric.infDist e (S : Set V) = ⨅ y : S, dist e y := Metric.infDist_eq_iInf
      _ = ⨅ y : S, ‖e - y‖ := by simp only [dist_eq_norm]
      _ = ‖e - S.starProjection e‖ := (S.starProjection_minimal e).symm
      _ = 1 := by rw [he_projection, sub_zero, he_norm]
  · rw [← (orthogonal_complement_projection_identities S).1]
    exact Sᗮ.norm_starProjection hResidual

#print axioms finite_layer_projection_escape

end D5.S3.Quantum.Algebra.FiniteLayerProjectionEscape
