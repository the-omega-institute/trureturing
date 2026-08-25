/- GID: D5/S3/Quantum/Completion/UniformCompletionObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/UniformCompletionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proper orthogonal-projection stages stay one operator-norm unit from identity. -/

/- Library-search audit trail (2026-08-25):
   * The completion family's frozen theorem
     `InfiniteDimensionalProjectionSeparation.infinite_dimensional_projection_separation`
     proves the same norm obstruction for a narrower natural-numbered, finite-dimensional,
     dense increasing tower. It is imported as the source section's repository anchor, but its
     extra hypotheses prevent it from covering the general stagewise statement here.
   * Pinned-Mathlib searches found the exact declarations
     `Submodule.starProjection_orthogonal`, `Submodule.norm_starProjection`, and
     `Submodule.orthogonal_eq_bot_iff`; all are applied directly below.
   * Repository searches across Observer, ConceptDynamics, Entropy, and Quantum completion
     found no public theorem for arbitrary proper projection stages and a nontrivial index
     filter. No new family primitive is introduced. -/

import D5.S3.Quantum.Completion.InfiniteDimensionalProjectionSeparation

noncomputable section

namespace D5.S3.Quantum.Completion.UniformCompletionObstruction

open Filter
open Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {K H I : Type*} [RCLike K] [NormedAddCommGroup H]
  [InnerProductSpace K H]

/-- Every proper closed-subspace stage has identity-minus-projection operator norm one. Along
any nontrivial stage filter, those norm distances therefore cannot converge to zero. -/
theorem uniform_completion_obstruction
    (S : I -> Submodule K H)
    [forall i, (S i).HasOrthogonalProjection]
    (stageFilter : Filter I) [NeBot stageFilter]
    (hProper : forall i, S i ≠ ⊤) :
    (forall i,
      ‖ContinuousLinearMap.id K H - (S i).starProjection‖ = 1) /\
      (¬ Tendsto
        (fun i => ‖ContinuousLinearMap.id K H - (S i).starProjection‖)
        stageFilter (nhds 0)) := by
  have hNorm :
      forall i, ‖ContinuousLinearMap.id K H - (S i).starProjection‖ = 1 := by
    intro i
    have hOrthogonal : (S i)ᗮ ≠ ⊥ := by
      intro hbot
      exact hProper i ((Submodule.orthogonal_eq_bot_iff).mp hbot)
    calc
      ‖ContinuousLinearMap.id K H - (S i).starProjection‖ =
          ‖(S i)ᗮ.starProjection‖ := by
            rw [Submodule.starProjection_orthogonal]
      _ = 1 := (S i)ᗮ.norm_starProjection hOrthogonal
  refine ⟨hNorm, ?_⟩
  intro hUniform
  have hOne : Tendsto (fun _i : I => (1 : Real)) stageFilter (nhds 0) := by
    simpa only [hNorm] using hUniform
  exact zero_ne_one (tendsto_nhds_unique hOne tendsto_const_nhds)

#print axioms uniform_completion_obstruction

end D5.S3.Quantum.Completion.UniformCompletionObstruction
