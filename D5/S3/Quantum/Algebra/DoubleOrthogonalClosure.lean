/- GID: D5/S3/Quantum/Algebra/DoubleOrthogonalClosure
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/DoubleOrthogonalClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Double orthogonal complementation equals topological closure in a Hilbert space. -/

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/- Library-search audit trail (2026-08-16):
   * Repository search found no D5 declaration of double orthogonal complementation as closure.
   * Loogle found the exact pinned-Mathlib declaration
     `Submodule.orthogonal_orthogonal_eq_closure` in the imported module.
   * The local smart-search name query did not find the declaration; direct pinned-source search
     did.
   * The ordered search stopped at the exact pinned-Mathlib hit, before third-party libraries. -/

open scoped InnerProductSpace

namespace D5.S3.Quantum.Algebra.DoubleOrthogonalClosure

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- In a Hilbert space, taking the orthogonal complement twice closes an arbitrary subspace. -/
theorem double_orthogonal_complement_eq_closure (M : Submodule 𝕜 E) :
    Mᗮᗮ = M.topologicalClosure :=
  Submodule.orthogonal_orthogonal_eq_closure M

example : (⊥ : Submodule ℝ ℝ)ᗮᗮ = (⊥ : Submodule ℝ ℝ).topologicalClosure :=
  double_orthogonal_complement_eq_closure _

#print axioms double_orthogonal_complement_eq_closure

end D5.S3.Quantum.Algebra.DoubleOrthogonalClosure
