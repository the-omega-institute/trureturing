/- GID: D5/S3/Observer/HiddenFlow/ProjectionDoesNotImplyClosure
   generality: G
   mirror-B: D5/B/S3/Observer/HiddenFlow/ProjectionDoesNotImplyClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A nonzero proper idempotent Hermitian coordinate projection can have a range that is not invariant under a concrete linear dynamics. -/

import D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'perfect_projection_does_not_imply_dynamical_closure'
     D5 Golden/Frozen/accepted` returned no hit.
   * All ten modules in `D5/S3/Observer/HiddenFlow/` were checked by digest. The nearest
     public result is `visible_descent_does_not_prevent_hidden_leakage`, which proves an
     asymmetric cross-block witness but neither projection perfection nor non-invariance of
     `IsInvariant` on the projection range. No private declaration covers the claim.
   * Repository-wide searches for projection closure and invariant ranges found no other
     theorem combining an idempotent self-adjoint projection with a closure counterexample.
   * Pinned Mathlib searches found `Matrix.IsHermitian`, `IsIdempotentElem`, and
     `LinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff`, but no packaged separation
     witness. The proof uses the first two notions and concrete finite-coordinate calculation,
     while reusing the repository's public `IsInvariant` definition for dynamical closure.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.HiddenFlow.ProjectionDoesNotImplyClosure

open D5.S3.Observer.HiddenFlow.VisibleHiddenProjectionCriteria

/-- A projection is perfect here when it is both idempotent and Hermitian. -/
def IsPerfectProjection {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℚ) : Prop :=
  IsIdempotentElem D ∧ D.IsHermitian

/-- The nonzero proper projection onto the first coordinate of `ℚ²`. -/
def firstCoordinateProjection : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 0; 0, 0]

/-- The dynamics sending the first coordinate into the second coordinate. -/
def firstToSecondDynamics : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 0; 1, 0]

/-- The first standard basis vector, which lies in the projection range. -/
def firstBasisVector : Fin 2 → ℚ :=
  ![1, 0]

/-- The concrete first-coordinate projection is idempotent and Hermitian. -/
theorem firstCoordinateProjection_isPerfect :
    IsPerfectProjection firstCoordinateProjection := by
  change firstCoordinateProjection * firstCoordinateProjection = firstCoordinateProjection ∧
    Matrix.conjTranspose firstCoordinateProjection = firstCoordinateProjection
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [firstCoordinateProjection, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [firstCoordinateProjection, Matrix.conjTranspose]

/-- A perfect projection does not by itself force its range to be dynamically invariant. -/
theorem perfect_projection_does_not_imply_dynamical_closure :
    ∃ D F : Matrix (Fin 2) (Fin 2) ℚ,
      IsPerfectProjection D ∧
        ¬ IsInvariant (Matrix.toLin' F) (LinearMap.range (Matrix.toLin' D)) := by
  refine ⟨firstCoordinateProjection, firstToSecondDynamics,
    firstCoordinateProjection_isPerfect, ?_⟩
  intro hClosure
  have hFirstBasisInRange :
      firstBasisVector ∈ LinearMap.range (Matrix.toLin' firstCoordinateProjection) := by
    refine ⟨firstBasisVector, ?_⟩
    ext i
    fin_cases i <;>
      norm_num [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        firstCoordinateProjection, firstBasisVector]
  rcases hClosure _ hFirstBasisInRange with ⟨y, hy⟩
  have hSecondCoordinate := congrFun hy 1
  norm_num [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    firstCoordinateProjection, firstToSecondDynamics, firstBasisVector] at hSecondCoordinate

example : IsPerfectProjection firstCoordinateProjection := by
  exact firstCoordinateProjection_isPerfect

#print axioms perfect_projection_does_not_imply_dynamical_closure

end D5.S3.Observer.HiddenFlow.ProjectionDoesNotImplyClosure
