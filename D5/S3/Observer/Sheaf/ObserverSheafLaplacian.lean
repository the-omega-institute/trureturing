/- GID: D5/S3/Observer/Sheaf/ObserverSheafLaplacian
   generality: G
   mirror-B: D5/B/S3/Observer/Sheaf/ObserverSheafLaplacian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite observer coboundary yields a positive Hermitian Laplacian and zero Dirichlet energy exactly characterizes compatibility. -/

import D5.S3.Observer.Sheaf.FiniteObserverSheaf
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Finite observer sheaf Laplacian

Once finite vertex and edge stalk coordinates have been chosen, the observer
coboundary is represented by a matrix `D`.  Its degree-zero sheaf Laplacian is

`L = Dᴴ D`.

The local compatibility condition is `D s = 0`.  The associated Dirichlet
energy is the sum of squared norms of all edge defects.  It is nonnegative and
vanishes exactly on compatible local observer families.  Every compatible
family is therefore harmonic for the Laplacian.

This module is a finite coordinate realization.  It does not identify the
matrix complex with derived sheaf cohomology, prove a Hodge decomposition, or
study asymptotic diffusion and oversmoothing.
-/

/- Library-search audit trail (2026-09-01):
   * `FiniteObserverSheaf` owns the abstract zero-to-one observer coboundary and
     compatible-section kernel.
   * `SheafPairwiseEqualizer` owns categorical unique gluing.
   * Repository search found no matrix sheaf Laplacian or finite observer
     Dirichlet zero-energy characterization.
   * Pinned Mathlib supplies conjugate transpose, matrix-vector products,
     Hermitian Gram matrices, finite sums, and norm positivity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Sheaf.ObserverSheafLaplacian

noncomputable section

universe u v

variable {Vertex : Type u} {Edge : Type v}
variable [Fintype Vertex] [DecidableEq Vertex]
variable [Fintype Edge] [DecidableEq Edge]

/-- Matrix compatibility of a finite local observer family. -/
def MatrixCompatible
    (coboundary : Matrix Edge Vertex ℂ)
    (section : Vertex → ℂ) : Prop :=
  coboundary.mulVec section = 0

/-- Degree-zero finite observer sheaf Laplacian. -/
def observerSheafLaplacian
    (coboundary : Matrix Edge Vertex ℂ) : Matrix Vertex Vertex ℂ :=
  coboundaryᴴ * coboundary

/-- Sum of squared edge-defect norms. -/
def observerDirichletEnergy
    (coboundary : Matrix Edge Vertex ℂ)
    (section : Vertex → ℂ) : ℝ :=
  ∑ edge, ‖coboundary.mulVec section edge‖ ^ 2

/-- Harmonicity for the degree-zero observer sheaf Laplacian. -/
def IsObserverHarmonic
    (coboundary : Matrix Edge Vertex ℂ)
    (section : Vertex → ℂ) : Prop :=
  (observerSheafLaplacian coboundary).mulVec section = 0

/-- The finite observer sheaf Laplacian is Hermitian. -/
theorem observerSheafLaplacian_isHermitian
    (coboundary : Matrix Edge Vertex ℂ) :
    (observerSheafLaplacian coboundary).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_self coboundary

/-- The observer Dirichlet energy is nonnegative. -/
theorem observerDirichletEnergy_nonneg
    (coboundary : Matrix Edge Vertex ℂ)
    (section : Vertex → ℂ) :
    0 ≤ observerDirichletEnergy coboundary section := by
  unfold observerDirichletEnergy
  exact Finset.sum_nonneg fun edge _ => sq_nonneg _

/-- Zero Dirichlet energy is exactly matrix compatibility. -/
theorem observerDirichletEnergy_eq_zero_iff
    (coboundary : Matrix Edge Vertex ℂ)
    (section : Vertex → ℂ) :
    observerDirichletEnergy coboundary section = 0 ↔
      MatrixCompatible coboundary section := by
  constructor
  · intro hEnergy
    unfold MatrixCompatible
    funext edge
    have hTermLe :
        ‖coboundary.mulVec section edge‖ ^ 2 ≤
          observerDirichletEnergy coboundary section := by
      unfold observerDirichletEnergy
      exact Finset.single_le_sum
        (fun other _ => sq_nonneg
          ‖coboundary.mulVec section other‖)
        (Finset.mem_univ edge)
    rw [hEnergy] at hTermLe
    have hTermZero : ‖coboundary.mulVec section edge‖ ^ 2 = 0 :=
      le_antisymm hTermLe (sq_nonneg _)
    have hNormZero : ‖coboundary.mulVec section edge‖ = 0 := by
      nlinarith [norm_nonneg (coboundary.mulVec section edge)]
    exact norm_eq_zero.mp hNormZero
  · intro hCompatible
    unfold MatrixCompatible at hCompatible
    unfold observerDirichletEnergy
    apply Finset.sum_eq_zero
    intro edge _
    rw [show coboundary.mulVec section edge = 0 by
      exact congrFun hCompatible edge]
    norm_num

/-- The Laplacian matrix-vector action factors through the coboundary and its
conjugate transpose. -/
theorem observerSheafLaplacian_mulVec
    (coboundary : Matrix Edge Vertex ℂ)
    (section : Vertex → ℂ) :
    (observerSheafLaplacian coboundary).mulVec section =
      coboundaryᴴ.mulVec (coboundary.mulVec section) := by
  exact Matrix.mulVec_mulVec coboundaryᴴ coboundary section

/-- Every compatible observer family is harmonic. -/
theorem matrixCompatible_implies_harmonic
    (coboundary : Matrix Edge Vertex ℂ)
    (section : Vertex → ℂ)
    (hCompatible : MatrixCompatible coboundary section) :
    IsObserverHarmonic coboundary section := by
  unfold IsObserverHarmonic MatrixCompatible at hCompatible ⊢
  rw [observerSheafLaplacian_mulVec, hCompatible]
  simp

/-- Under injectivity of the adjoint coboundary, harmonicity also forces
compatibility. -/
theorem harmonic_implies_matrixCompatible_of_adjoint_injective
    (coboundary : Matrix Edge Vertex ℂ)
    (section : Vertex → ℂ)
    (hInjective : Function.Injective coboundaryᴴ.mulVec)
    (hHarmonic : IsObserverHarmonic coboundary section) :
    MatrixCompatible coboundary section := by
  unfold IsObserverHarmonic MatrixCompatible at hHarmonic ⊢
  rw [observerSheafLaplacian_mulVec] at hHarmonic
  apply hInjective
  simpa using hHarmonic

example :
    observerDirichletEnergy
      (0 : Matrix (Fin 1) (Fin 1) ℂ) (fun _ => 1) = 0 := by
  simp [observerDirichletEnergy, Matrix.mulVec]

#print axioms observerSheafLaplacian_isHermitian
#print axioms observerDirichletEnergy_nonneg
#print axioms observerDirichletEnergy_eq_zero_iff
#print axioms observerSheafLaplacian_mulVec
#print axioms matrixCompatible_implies_harmonic
#print axioms harmonic_implies_matrixCompatible_of_adjoint_injective

end

end D5.S3.Observer.Sheaf.ObserverSheafLaplacian
