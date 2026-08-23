/- GID: D5/S3/Quantum/Fibers/QuotientResidualTransport
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/QuotientResidualTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Isometric quotient transport preserves canonical residual norms and costs. -/

import D5.S3.Quantum.Algebra.QuotientOrthogonalComplement
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/- Library-search audit trail (2026-08-23):
   * Repository searches found no theorem combining quotient-class transport, canonical
     orthogonal residuals, cost invariance, and the common-zero-set countermodel.
   * The exact family theorem `quotient_orthogonal_complement_isometry` identifies each quotient
     class isometrically with `x - M.starProjection x`; it is imported and applied below.
   * Pinned Mathlib contains the exact quotient constructors `Submodule.mkQL` and
     `Submodule.liftQL`, with `Submodule.liftQL_apply` as the computation rule. They construct the
     induced transition below. No exact theorem for the combined source statement was found. -/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Quantum.Fibers.QuotientResidualTransport

open D5.S3.Quantum.Algebra.QuotientOrthogonalComplement

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {𝕜 Eₖ Eⱼ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup Eₖ] [InnerProductSpace 𝕜 Eₖ]
  [NormedAddCommGroup Eⱼ] [InnerProductSpace 𝕜 Eⱼ]

/-- The quotient transition constructed from a continuous linear chart transition that preserves
the invisible source and target subspaces. -/
def inducedQuotientTransition
    (Mₖ : Submodule 𝕜 Eₖ) [IsClosed (Mₖ : Set Eₖ)]
    (Mⱼ : Submodule 𝕜 Eⱼ) [IsClosed (Mⱼ : Set Eⱼ)]
    (T : Eₖ →L[𝕜] Eⱼ) (h_preserves : ∀ y ∈ Mₖ, T y ∈ Mⱼ) :
    (Eₖ ⧸ Mₖ) →L[𝕜] (Eⱼ ⧸ Mⱼ) :=
  Mₖ.liftQL (Mⱼ.mkQL.comp T) (by
    intro y hy
    change Mⱼ.mkQ (T y) = 0
    exact (Submodule.Quotient.mk_eq_zero (p := Mⱼ)).mpr (h_preserves y hy))

@[simp]
theorem inducedQuotientTransition_mkQ
    (Mₖ : Submodule 𝕜 Eₖ) [IsClosed (Mₖ : Set Eₖ)]
    (Mⱼ : Submodule 𝕜 Eⱼ) [IsClosed (Mⱼ : Set Eⱼ)]
    (T : Eₖ →L[𝕜] Eⱼ) (h_preserves : ∀ y ∈ Mₖ, T y ∈ Mⱼ) (x : Eₖ) :
    inducedQuotientTransition Mₖ Mⱼ T h_preserves (Mₖ.mkQ x) = Mⱼ.mkQ (T x) := by
  rfl

/-- A compatible chart transition carries the source quotient class to the target class. If its
induced quotient map is isometric, the canonical orthogonal residual norms and their half-squared
costs agree. An explicit pair of scalar residual maps shows that a common zero set alone does not
force the cost equality. -/
theorem quotient_residual_transport_and_zero_set_countermodel
    (Mₖ : Submodule 𝕜 Eₖ) [Mₖ.HasOrthogonalProjection] [IsClosed (Mₖ : Set Eₖ)]
    (Mⱼ : Submodule 𝕜 Eⱼ) [Mⱼ.HasOrthogonalProjection] [IsClosed (Mⱼ : Set Eⱼ)]
    (T : Eₖ →L[𝕜] Eⱼ) (h_preserves : ∀ y ∈ Mₖ, T y ∈ Mⱼ)
    (xₖ : Eₖ) (xⱼ : Eⱼ) (h_compatible : T xₖ - xⱼ ∈ Mⱼ) :
    inducedQuotientTransition Mₖ Mⱼ T h_preserves (Mₖ.mkQ xₖ) = Mⱼ.mkQ xⱼ ∧
      (Isometry (inducedQuotientTransition Mₖ Mⱼ T h_preserves) →
        ‖xₖ - Mₖ.starProjection xₖ‖ = ‖xⱼ - Mⱼ.starProjection xⱼ‖ ∧
        (1 / 2 : ℝ) * ‖xₖ - Mₖ.starProjection xₖ‖ ^ 2 =
          (1 / 2 : ℝ) * ‖xⱼ - Mⱼ.starProjection xⱼ‖ ^ 2) ∧
      ∃ (first second : ℝ →L[ℝ] ℝ) (point : ℝ),
        (∀ x, first x = 0 ↔ second x = 0) ∧
          (1 / 2 : ℝ) * ‖first point‖ ^ 2 ≠ (1 / 2 : ℝ) * ‖second point‖ ^ 2 := by
  have h_class : Mⱼ.mkQ (T xₖ) = Mⱼ.mkQ xⱼ := by
    rw [← sub_eq_zero, ← map_sub]
    exact (Submodule.Quotient.mk_eq_zero (p := Mⱼ)).mpr h_compatible
  have h_transport :
      inducedQuotientTransition Mₖ Mⱼ T h_preserves (Mₖ.mkQ xₖ) = Mⱼ.mkQ xⱼ := by
    rw [inducedQuotientTransition_mkQ, h_class]
  refine ⟨h_transport, ?_, ?_⟩
  · intro h_isometry
    have h_source_representation :=
      (quotient_orthogonal_complement_isometry Mₖ).2.2 xₖ
    have h_target_representation :=
      (quotient_orthogonal_complement_isometry Mⱼ).2.2 xⱼ
    have h_source_norm :
        ‖Mₖ.mkQ xₖ‖ = ‖xₖ - Mₖ.starProjection xₖ‖ := by
      calc
        ‖Mₖ.mkQ xₖ‖ = ‖Mₖ.quotientEquivOrthogonal (Mₖ.mkQ xₖ)‖ :=
          (Mₖ.quotientEquivOrthogonal.norm_map _).symm
        _ = ‖(Mₖ.quotientEquivOrthogonal (Mₖ.mkQ xₖ) : Eₖ)‖ := rfl
        _ = ‖xₖ - Mₖ.starProjection xₖ‖ := congrArg norm h_source_representation
    have h_target_norm :
        ‖Mⱼ.mkQ xⱼ‖ = ‖xⱼ - Mⱼ.starProjection xⱼ‖ := by
      calc
        ‖Mⱼ.mkQ xⱼ‖ = ‖Mⱼ.quotientEquivOrthogonal (Mⱼ.mkQ xⱼ)‖ :=
          (Mⱼ.quotientEquivOrthogonal.norm_map _).symm
        _ = ‖(Mⱼ.quotientEquivOrthogonal (Mⱼ.mkQ xⱼ) : Eⱼ)‖ := rfl
        _ = ‖xⱼ - Mⱼ.starProjection xⱼ‖ := congrArg norm h_target_representation
    have h_residual_norm :
        ‖xₖ - Mₖ.starProjection xₖ‖ = ‖xⱼ - Mⱼ.starProjection xⱼ‖ := by
      rw [← h_source_norm, ← h_target_norm, ← h_transport]
      exact (h_isometry.norm_map_of_map_zero
        (map_zero (inducedQuotientTransition Mₖ Mⱼ T h_preserves)) (Mₖ.mkQ xₖ)).symm
    exact ⟨h_residual_norm, congrArg (fun value : ℝ => (1 / 2) * value ^ 2)
      h_residual_norm⟩
  · refine ⟨ContinuousLinearMap.id ℝ ℝ, (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ, 1, ?_, ?_⟩
    · intro x
      simp
    · norm_num

example : ℝ := 0

example : (⊥ : Submodule ℝ ℝ).HasOrthogonalProjection := inferInstance

#print axioms quotient_residual_transport_and_zero_set_countermodel

end D5.S3.Quantum.Fibers.QuotientResidualTransport
