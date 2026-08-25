/- GID: D5/S3/Quantum/Completion/DenseTowerStrongCompletion
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/DenseTowerStrongCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A dense increasing Hilbert-subspace tower converges strongly to identity. -/

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/- Library-search audit trail (2026-08-25):
   * Exact pinned-Mathlib hit `Submodule.starProjection_tendsto_self`
     proves vectorwise convergence for an arbitrary preorder-indexed monotone
     family with dense closed supremum and is applied directly below.
   * Exact support hit `Filter.Tendsto.norm` turns convergence of each
     identity-minus-projection residual vector into convergence of its norm.
   * The repository theorem `increasing_projection_strong_limit` directly
     applies the first hit for natural-numbered towers, but is narrower than
     the source's arbitrary tower index.
   * Searches across Observer, ConceptDynamics, Entropy, and Quantum completion
     found no receipt for this atom. This module introduces no family primitive. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Completion.DenseTowerStrongCompletion

open Filter
open Topology

/-- Orthogonal projections onto a nonempty directed increasing tower with dense
closed supremum converge on every vector to that vector. Equivalently, each
identity-minus-projection residual converges to zero in norm. -/
theorem dense_tower_strong_completion
    {K H I : Type*} [RCLike K] [NormedAddCommGroup H]
    [InnerProductSpace K H] [SemilatticeSup I] [Nonempty I]
    (S : I -> Submodule K H) [forall i, (S i).HasOrthogonalProjection]
    (hS : Monotone S) (hDense : (⨆ i, S i).topologicalClosure = ⊤) :
    (forall x,
      Tendsto (fun i => (S i).starProjection x) atTop (nhds x)) /\
    (forall x,
      Tendsto
        (fun i => ‖(ContinuousLinearMap.id K H - (S i).starProjection) x‖)
        atTop (nhds 0)) := by
  have hTop : ⊤ ≤ (⨆ i, S i).topologicalClosure := by rw [hDense]
  constructor
  · intro x
    exact Submodule.starProjection_tendsto_self S hS x hTop
  · intro x
    have hProjection := Submodule.starProjection_tendsto_self S hS x hTop
    have hResidual :
        Tendsto (fun i => x - (S i).starProjection x) atTop (nhds (x - x)) :=
      tendsto_const_nhds.sub hProjection
    simpa using hResidual.norm

#print axioms dense_tower_strong_completion

end D5.S3.Quantum.Completion.DenseTowerStrongCompletion
