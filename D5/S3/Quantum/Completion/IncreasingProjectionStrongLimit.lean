/- GID: D5/S3/Quantum/Completion/IncreasingProjectionStrongLimit
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/IncreasingProjectionStrongLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Increasing orthogonal projections converge strongly to the cumulative projection. -/

/- Library-search audit trail (2026-08-22):
   * The completion family's exact repository definitions `cumulativeSpace` and `residualSpace`
     construct the source's terminal known and residual subspaces and are imported below.
   * Loogle query `"starProjection_tendsto_closure_iSup"` returned the exact Mathlib theorem
     `Submodule.starProjection_tendsto_closure_iSup`. LeanSearch query `orthogonal projections onto
     an increasing sequence of closed subspaces converge strongly to projection onto closure of
     union` ranked the same declaration first. It is directly applied for the first clause.
   * Exact Mathlib hits `Submodule.starProjection_tendsto_self` and
     `PointwiseConvergenceCLM.tendsto_iff_forall_tendsto` are directly applied to obtain the
     identity limit in the pointwise-convergence topology on continuous linear maps, which
     Mathlib documents as the strong operator topology.
   * Repository search found one private use of the first hit inside the imported completion
     module, but no public declaration packaging both source clauses and no receipt for this atom.
-/

import D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

namespace D5.S3.Quantum.Completion.IncreasingProjectionStrongLimit

open Filter
open Topology
open D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Projections onto an increasing sequence of subspaces converge vectorwise to the projection
onto their closed cumulative span. If the canonical terminal residual vanishes, the projection
operators converge to the identity in the pointwise-convergence (strong operator) topology. -/
theorem increasing_projection_strong_limit
    (S : ℕ -> Submodule 𝕜 H)
    [forall n, (S n).HasOrthogonalProjection]
    [(cumulativeSpace S).HasOrthogonalProjection]
    (hS : Monotone S) :
    (forall x,
      Tendsto (fun n => (S n).starProjection x) atTop
        (𝓝 ((cumulativeSpace S).starProjection x))) /\
      (residualSpace S = ⊥ ->
        Tendsto
          (fun n => ContinuousLinearMap.toPointwiseConvergenceCLM
            𝕜 (RingHom.id 𝕜) H H (S n).starProjection) atTop
          (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM
            𝕜 (RingHom.id 𝕜) H H (ContinuousLinearMap.id 𝕜 H)))) := by
  constructor
  · intro x
    simpa only [cumulativeSpace] using
      (Submodule.starProjection_tendsto_closure_iSup S hS x)
  · intro hresidual
    have hcumulative : cumulativeSpace S = ⊤ := by
      apply (Submodule.orthogonal_eq_bot_iff).mp
      simpa only [residualSpace] using hresidual
    refine (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto
      (σ := RingHom.id 𝕜) (E := H) (F := H) (p := atTop)
      (a := fun n => ContinuousLinearMap.toPointwiseConvergenceCLM
        𝕜 (RingHom.id 𝕜) H H (S n).starProjection)
      (a₀ := ContinuousLinearMap.toPointwiseConvergenceCLM
        𝕜 (RingHom.id 𝕜) H H (ContinuousLinearMap.id 𝕜 H))).2 ?_
    intro x
    have htop : ⊤ ≤ (⨆ n, S n).topologicalClosure := by
      change ⊤ ≤ cumulativeSpace S
      rw [hcumulative]
    change Tendsto (fun n => (S n).starProjection x) atTop (𝓝 x)
    exact Submodule.starProjection_tendsto_self S hS x htop

/-- The constant full-space tower witnesses monotonicity and terminal-residual vanishing. -/
example :
    Monotone (fun _n : ℕ => (⊤ : Submodule ℝ ℝ)) /\
      residualSpace (fun _n : ℕ => (⊤ : Submodule ℝ ℝ)) = ⊥ := by
  constructor
  · exact monotone_const
  · simp [residualSpace, cumulativeSpace]

#print axioms increasing_projection_strong_limit

end D5.S3.Quantum.Completion.IncreasingProjectionStrongLimit
