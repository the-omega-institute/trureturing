/- GID: D5/S3/Quantum/Completion/LimitStageResidualIntersection
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/LimitStageResidualIntersection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A limit-stage residual is the intersection of all predecessor residuals. -/

import Mathlib.Analysis.InnerProductSpace.Orthogonal

/- Library-search audit trail (2026-09-03):
   * Repository searches found only a specialized well-ordered basis tower and a
     natural-numbered cumulative-space decomposition, not this arbitrary indexed statement.
   * Pinned Mathlib provides the exact identity `ClosedSubmodule.iInf_orthogonal`, which is
     applied directly below.
   * The ordered search stopped at the exact pinned-Mathlib hit, before third-party libraries.
   * This module introduces no new family primitive or auxiliary definition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace D5.S3.Quantum.Completion.LimitStageResidualIntersection

/-- If the closed subspace at a stage is the closed supremum of all predecessor subspaces,
then its orthogonal residual is the intersection of the predecessor residuals. -/
theorem limit_stage_residual_intersection
    {K H I : Type*} [RCLike K] [NormedAddCommGroup H]
    [InnerProductSpace K H] [CompleteSpace H] [Preorder I]
    (V : I -> ClosedSubmodule K H) (limit : I)
    (hlimit : V limit = ⨆ alpha : Set.Iio limit, V alpha.1) :
    (V limit)ᗮ = ⨅ alpha : Set.Iio limit, (V alpha.1)ᗮ := by
  rw [hlimit]
  exact (ClosedSubmodule.iInf_orthogonal
    (fun alpha : Set.Iio limit => V alpha.1)).symm

#print axioms limit_stage_residual_intersection

end D5.S3.Quantum.Completion.LimitStageResidualIntersection
