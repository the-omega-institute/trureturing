/- GID: D5/S3/Observer/MetricGeometryLaws/TailResidualCrossLayerBound
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/TailResidualCrossLayerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A Lipschitz update separates a coarse defect into a fine tail and cross-layer defect. -/

import D5.S3.Observer.MetricGeometry.DefectDecomposition
import D5.S3.Quantum.Algebra.OrthogonalProjectionComplement

/- Library-search audit trail (2026-08-25):
   * Current-tree searches found the adjacent abstract diagram theorem
     `DefectDecomposition.defect_decomposition`, but it does not expose the source Hilbert
     carrier or its canonical nested orthogonal projections, so it is not an exact statement hit.
   * The canonical source projections are Mathlib's `Submodule.starProjection`; no new family
     primitive is declared here.
   * Pinned Mathlib exact supporting hits `dist_triangle`,
     `Submodule.norm_starProjection_apply_le`, `LipschitzWith.dist_le_mul`, and
     `Submodule.starProjection_comp_starProjection_of_le` are applied directly below. -/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Observer.MetricGeometryLaws.TailResidualCrossLayerBound

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V]

/-- For nested visible subspaces, the coarse naturality defect of a Lipschitz update is bounded
by the unresolved fine-layer tail plus the defect internal to the fine layer. Both defects and
the tail are stated directly from the update and the canonical orthogonal projections. -/
theorem tail_residual_cross_layer_defect_bound
    (Vm Vn : Submodule 𝕜 V)
    [Vm.HasOrthogonalProjection] [Vn.HasOrthogonalProjection]
    (hmn : Vm ≤ Vn) (F : V -> V) (L : NNReal)
    (hF : LipschitzWith L F) (X : V) :
    ‖Vm.starProjection (F X) -
        Vm.starProjection (F (Vm.starProjection X))‖ ≤
      L * ‖(ContinuousLinearMap.id 𝕜 V - Vn.starProjection) X‖ +
        ‖Vm.starProjection (F (Vn.starProjection X)) -
          Vm.starProjection
            (F (Vm.starProjection (Vn.starProjection X)))‖ := by
  have hcoarseFine :
      Vm.starProjection (Vn.starProjection X) = Vm.starProjection X := by
    have hcomp := Submodule.starProjection_comp_starProjection_of_le hmn
    exact congrArg (fun projection : V →L[𝕜] V => projection X) hcomp
  have htail :
      ‖Vm.starProjection (F X) -
          Vm.starProjection (F (Vn.starProjection X))‖ ≤
        L * ‖(ContinuousLinearMap.id 𝕜 V - Vn.starProjection) X‖ := by
    calc
      ‖Vm.starProjection (F X) -
          Vm.starProjection (F (Vn.starProjection X))‖ =
          ‖Vm.starProjection (F X - F (Vn.starProjection X))‖ := by
            rw [map_sub]
      _ ≤ ‖F X - F (Vn.starProjection X)‖ :=
        Vm.norm_starProjection_apply_le _
      _ = dist (F X) (F (Vn.starProjection X)) := by
        rw [dist_eq_norm]
      _ ≤ L * dist X (Vn.starProjection X) := hF.dist_le_mul _ _
      _ = L * ‖X - Vn.starProjection X‖ := by rw [dist_eq_norm]
      _ = L * ‖(ContinuousLinearMap.id 𝕜 V - Vn.starProjection) X‖ := by
        simp
  calc
    ‖Vm.starProjection (F X) -
        Vm.starProjection (F (Vm.starProjection X))‖ =
        dist (Vm.starProjection (F X))
          (Vm.starProjection (F (Vm.starProjection X))) := by
            rw [dist_eq_norm]
    _ ≤ dist (Vm.starProjection (F X))
          (Vm.starProjection (F (Vn.starProjection X))) +
        dist (Vm.starProjection (F (Vn.starProjection X)))
          (Vm.starProjection (F (Vm.starProjection X))) := dist_triangle _ _ _
    _ = ‖Vm.starProjection (F X) -
          Vm.starProjection (F (Vn.starProjection X))‖ +
        ‖Vm.starProjection (F (Vn.starProjection X)) -
          Vm.starProjection (F (Vm.starProjection X))‖ := by
            simp only [dist_eq_norm]
    _ ≤ L * ‖(ContinuousLinearMap.id 𝕜 V - Vn.starProjection) X‖ +
        ‖Vm.starProjection (F (Vn.starProjection X)) -
          Vm.starProjection (F (Vm.starProjection X))‖ :=
      add_le_add htail le_rfl
    _ = L * ‖(ContinuousLinearMap.id 𝕜 V - Vn.starProjection) X‖ +
        ‖Vm.starProjection (F (Vn.starProjection X)) -
          Vm.starProjection
            (F (Vm.starProjection (Vn.starProjection X)))‖ := by
      rw [hcoarseFine]

#print axioms tail_residual_cross_layer_defect_bound

end D5.S3.Observer.MetricGeometryLaws.TailResidualCrossLayerBound
