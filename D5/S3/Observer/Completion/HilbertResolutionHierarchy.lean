/- GID: D5/S3/Observer/Completion/HilbertResolutionHierarchy
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/HilbertResolutionHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three Hilbert resolution modes and the proper-stage obstruction. -/

import D5.S3.Observer.Completion.ResidualProgressMeasure
import D5.S3.Quantum.Completion.UniformCompletionObstruction

/- Library-search audit trail (2026-08-28):
   * Exact repository hit `ResidualProgressMeasure.testResidualSize` is the canonical extended
     supremum of residual projection norms over an arbitrary test family and is reused below.
   * Exact repository hit `UniformCompletionObstruction.uniform_completion_obstruction` proves
     the proper-stage norm-one and nonconvergence clause and is applied directly.
   * Related repository hits `DenseTowerStrongCompletion.dense_tower_strong_completion` and
     `IncreasingProjectionStrongLimit.increasing_projection_strong_limit` prove strong target
     convergence under density, but do not package either implication in the source hierarchy.
   * Pinned Mathlib provides `Submodule.starProjection_orthogonal`,
     `Submodule.norm_starProjection`, `Submodule.orthogonal_eq_bot_iff`, and the indexed-supremum
     order lemmas used below; no exact theorem packages all three source clauses. -/

noncomputable section

namespace D5.S3.Observer.Completion.HilbertResolutionHierarchy

open Filter Topology
open D5.S3.Observer.Completion.ResidualProgressMeasure
open D5.S3.Quantum.Completion.UniformCompletionObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Uniform operator-norm resolution forces residual resolution for every state family. Family
resolution in turn forces resolution of each member target. If all visible stages are proper,
the identity-minus-projection norm is always one and uniform resolution fails. -/
theorem hilbert_resolution_hierarchy
    {K H : Type*} [RCLike K] [NormedAddCommGroup H] [InnerProductSpace K H]
    (V : Nat -> Submodule K H) [forall n, (V n).HasOrthogonalProjection]
    (T : Set H) (x : H) :
    (Tendsto
        (fun n => ‖ContinuousLinearMap.id K H - (V n).starProjection‖)
        atTop (nhds 0) ->
      Tendsto (fun n => testResidualSize ((V n)ᗮ) T) atTop (nhds 0)) /\
    (x ∈ T ->
      Tendsto (fun n => testResidualSize ((V n)ᗮ) T) atTop (nhds 0) ->
      Tendsto (fun n => ENNReal.ofReal ‖((V n)ᗮ).starProjection x‖)
        atTop (nhds 0)) /\
    ((forall n, V n ≠ ⊤) ->
      (forall n, ‖ContinuousLinearMap.id K H - (V n).starProjection‖ = 1) /\
      (¬ Tendsto
        (fun n => ‖ContinuousLinearMap.id K H - (V n).starProjection‖)
        atTop (nhds 0))) := by
  constructor
  · intro hUniform
    have hSmall : ∀ᶠ n in atTop,
        ‖ContinuousLinearMap.id K H - (V n).starProjection‖ < 1 :=
      (tendsto_order.1 hUniform).2 1 zero_lt_one
    apply tendsto_congr' _ |>.2 tendsto_const_nhds
    filter_upwards [hSmall] with n hn
    have hTop : V n = ⊤ := by
      by_contra hProper
      have hOrthogonal : (V n)ᗮ ≠ ⊥ := by
        intro hbot
        exact hProper ((Submodule.orthogonal_eq_bot_iff).mp hbot)
      have hNorm :
          ‖ContinuousLinearMap.id K H - (V n).starProjection‖ = 1 := by
        calc
          ‖ContinuousLinearMap.id K H - (V n).starProjection‖ =
              ‖((V n)ᗮ).starProjection‖ := by
                rw [Submodule.starProjection_orthogonal]
          _ = 1 := (V n)ᗮ.norm_starProjection hOrthogonal
      rw [hNorm] at hn
      exact (lt_irrefl 1) hn
    simp [testResidualSize, hTop]
  constructor
  · intro hx hFamily
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hFamily ?_ ?_
    · exact Eventually.of_forall fun _ => bot_le
    · exact Eventually.of_forall fun n =>
        le_iSup (fun y : T => ENNReal.ofReal ‖((V n)ᗮ).starProjection (y : H)‖) ⟨x, hx⟩
  · intro hProper
    exact uniform_completion_obstruction V atTop hProper

#print axioms hilbert_resolution_hierarchy

end D5.S3.Observer.Completion.HilbertResolutionHierarchy
