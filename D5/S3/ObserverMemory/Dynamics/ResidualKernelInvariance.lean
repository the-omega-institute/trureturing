/- GID: D5/S3/ObserverMemory/Dynamics/ResidualKernelInvariance
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/ResidualKernelInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adjoint invariance makes the orthogonal residual kernel invariant. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint

/- Library-search audit trail (2026-08-16):
   * Repository searches found no equal or stronger D5 declaration about an adjoint-invariant
     observer subspace making its orthogonal residual invariant under the original evolution.
   * Pinned Mathlib contains the exact general result
     `ContinuousLinearMap.orthogonal_mem_invtSubmodule`, imported and applied below.
   * Loogle's exact-name query returned that declaration as its single hit. The local
     `smart_search.sh` phrase query returned no name hit (exit 1). -/

open Module

namespace D5.S3.ObserverMemory.Dynamics.ResidualKernelInvariance

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- If the adjoint evolution preserves the observable subspace, the original evolution
preserves its orthogonal residual kernel. -/
theorem residual_kernel_invariant
    (evolution : E →L[𝕜] E) (observable : Submodule 𝕜 E)
    (h_observable : Set.MapsTo evolution.adjoint observable observable) :
    Set.MapsTo evolution observableᗮ observableᗮ := by
  apply (Module.End.mem_invtSubmodule_iff_mapsTo evolution.toLinearMap).mp
  apply ContinuousLinearMap.orthogonal_mem_invtSubmodule
  exact
    (Module.End.mem_invtSubmodule_iff_mapsTo evolution.adjoint.toLinearMap).mpr h_observable

#print axioms residual_kernel_invariant

end D5.S3.ObserverMemory.Dynamics.ResidualKernelInvariance
