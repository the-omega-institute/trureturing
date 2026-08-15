/- GID: D5/S3/Quantum/Algebra/OrthogonalDeMorgan
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/OrthogonalDeMorgan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Orthogonal complements exchange joins and meets of closed subspaces. -/

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/- Library-search audit trail (2026-08-16):
   * Repository search found no D5 declaration of the two orthogonal De Morgan identities.
   * Pinned-Mathlib search found the exact declarations `ClosedSubmodule.inf_orthogonal`
     and `ClosedSubmodule.sup_orthogonal`; both are imported and applied below.
   * The ordered search stopped at the exact pinned-Mathlib hit, before third-party libraries. -/

open scoped InnerProductSpace

namespace D5.S3.Quantum.Algebra.OrthogonalDeMorgan

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Orthogonal complementation exchanges joins and meets of closed subspaces. The join in
`ClosedSubmodule` is the closed linear span, so the second identity is the closure-of-sum form. -/
theorem orthogonal_de_morgan (M N : ClosedSubmodule 𝕜 E) :
    (M ⊔ N)ᗮ = Mᗮ ⊓ Nᗮ ∧
      (M ⊓ N)ᗮ = Mᗮ ⊔ Nᗮ := by
  exact ⟨(ClosedSubmodule.inf_orthogonal M N).symm,
    (ClosedSubmodule.sup_orthogonal M N).symm⟩

example : ℝ := 0

example : CompleteSpace ℝ := inferInstance

#print axioms orthogonal_de_morgan

end D5.S3.Quantum.Algebra.OrthogonalDeMorgan
