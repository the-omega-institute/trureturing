/- GID: D5/S3/Quantum/Completion/LimitResidualDecomposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/LimitResidualDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The intersection of stage residuals is the cumulative orthogonal complement. -/

import D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction

/- Library-search audit trail (2026-08-22):
   * The completion family's frozen `cumulativeSpace` constructs the source's closed cumulative
     visible space and is imported rather than redeclared.
   * Repository searches found no existing definition of the intersection of all stage
     orthogonal residuals and no theorem packaging the two limiting decomposition clauses.
   * Pinned Mathlib provides the exact results `Submodule.iInf_orthogonal`,
     `Submodule.orthogonal_closure`, and `Submodule.isCompl_orthogonal`; all three are applied
     directly below. -/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Quantum.Completion.LimitResidualDecomposition

open D5.S3.Quantum.Completion.BoundedInverseLimitReconstruction

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The vectors lying in the orthogonal residual of every visible stage. -/
def limitingResidual (S : ℕ -> Submodule 𝕜 H) : Submodule 𝕜 H :=
  ⨅ n, (S n)ᗮ

/-- The limiting residual is exactly the orthogonal complement of the closed cumulative
visible space, and the two canonical subspaces form an internal direct sum of the ambient
Hilbert space. -/
theorem limit_residual_orthogonal_decomposition (S : ℕ -> Submodule 𝕜 H) :
    limitingResidual S = (cumulativeSpace S)ᗮ ∧
      IsCompl (cumulativeSpace S) (limitingResidual S) := by
  have hResidual : limitingResidual S = (cumulativeSpace S)ᗮ := by
    rw [limitingResidual, cumulativeSpace, Submodule.orthogonal_closure]
    exact Submodule.iInf_orthogonal S
  refine ⟨hResidual, ?_⟩
  rw [hResidual]
  letI : (cumulativeSpace S).HasOrthogonalProjection := by
    rw [cumulativeSpace]
    infer_instance
  exact (cumulativeSpace S).isCompl_orthogonal

/- A constant zero stage family witnesses that the public carrier and indexed-family scope are
inhabited. -/
example :
    limitingResidual (fun _n : ℕ => (⊥ : Submodule ℝ ℝ)) =
        (cumulativeSpace (fun _n : ℕ => (⊥ : Submodule ℝ ℝ)))ᗮ ∧
      IsCompl
        (cumulativeSpace (fun _n : ℕ => (⊥ : Submodule ℝ ℝ)))
        (limitingResidual (fun _n : ℕ => (⊥ : Submodule ℝ ℝ))) :=
  limit_residual_orthogonal_decomposition _

#print axioms limit_residual_orthogonal_decomposition

end D5.S3.Quantum.Completion.LimitResidualDecomposition
