/- GID: D5/S3/Quantum/Tomography/ResidualControlsNaturality
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ResidualControlsNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Orthogonal residual norms control visible compression defects. -/

import D5.S0.Diagonal.Naturality.NaturalityDefectComposition
import D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
import D5.S3.Quantum.Tomography.ComplementaryContextProbabilityPythagoras

/- Library-search audit trail (2026-08-22):
   * Pinned Mathlib exact hits `Submodule.lipschitzWith_starProjection`,
     `LipschitzWith.dist_le_mul`, `Submodule.starProjection_orthogonal_val`, and
     `Real.sqrt_sq` are applied directly below.
   * Repository exact hits supply the canonical real trace-zero Hermitian carrier,
     centered density coordinate, residual mass, and pointwise naturality defect.
   * `loogle` and `leansearch` executables are absent from PATH. Repository and
     pinned-Mathlib searches found no theorem packaging both source inequalities. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix NNReal

namespace D5.S3.Quantum.Tomography.ResidualControlsNaturality

open D5.S0.Diagonal.Naturality.NaturalityDefectComposition
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open D5.S3.Quantum.Tomography.ComplementaryContextProbabilityPythagoras

variable {d : Type*} [Fintype d] [Nonempty d] [DecidableEq d]

local instance matrixNormedAddCommGroup : NormedAddCommGroup (Matrix d d ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace : InnerProductSpace ℂ (Matrix d d ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace : InnerProductSpace ℝ (Matrix d d ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix d d ℂ)

local instance hermitianTraceZeroTopologicalSpace :
    TopologicalSpace (HermitianTraceZero (d := d)) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

private lemma centered_state_mem (rho : Matrix d d ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1) :
    centeredState rho ∈ HermitianTraceZero (d := d) := by
  refine ⟨hrho.1.isHermitian.sub ?_, ?_⟩
  · exact Matrix.IsHermitian.smul (by simp) (by rw [isSelfAdjoint_iff]; simp)
  · simp only [centeredState, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_one, hrho.2]
    simp only [smul_eq_mul]
    field_simp [show (Fintype.card d : ℂ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero]
    simp

/-- The source's centered density coordinate, constructed on the real trace-zero
Hermitian carrier from positivity and trace normalization. -/
def densityCoordinate (rho : Matrix d d ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1) :
    HermitianTraceZero (d := d) :=
  ⟨centeredState rho, centered_state_mem rho hrho⟩

/-- The source's visible dynamics: apply the ambient dynamics and then project
orthogonally back to the visible subspace. -/
def visibleDynamics
    (visible : Submodule ℝ (HermitianTraceZero (d := d)))
    [IsClosed (visible : Set (HermitianTraceZero (d := d)))]
    (dynamics : HermitianTraceZero (d := d) → HermitianTraceZero (d := d)) :
    HermitianTraceZero (d := d) → HermitianTraceZero (d := d) :=
  fun x => visible.starProjection (dynamics x)

/-- A Lipschitz ambient dynamics has visible-compression defect bounded by the
orthogonal residual norm. At a density coordinate, the same bound is the square
root of the residual mass. -/
theorem residual_controls_naturality
    (rho : Matrix d d ℂ) (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (visible : Submodule ℝ (HermitianTraceZero (d := d)))
    [IsClosed (visible : Set (HermitianTraceZero (d := d)))]
    (dynamics : HermitianTraceZero (d := d) → HermitianTraceZero (d := d))
    (L : NNReal) (hLipschitz : LipschitzWith L dynamics)
    (X : HermitianTraceZero (d := d)) :
    naturalityDefect visible.starProjection visible.starProjection
        dynamics (visibleDynamics visible dynamics) X ≤
          L * ‖visibleᗮ.starProjection X‖ ∧
      naturalityDefect visible.starProjection visible.starProjection
        dynamics (visibleDynamics visible dynamics) (densityCoordinate rho hrho) ≤
          L * Real.sqrt (residualMass visible (densityCoordinate rho hrho)) := by
  have defect_le_residual (Y : HermitianTraceZero (d := d)) :
      naturalityDefect visible.starProjection visible.starProjection
          dynamics (visibleDynamics visible dynamics) Y ≤
        L * ‖visibleᗮ.starProjection Y‖ := by
    unfold naturalityDefect visibleDynamics
    calc
      dist (visible.starProjection (dynamics Y))
          (visible.starProjection (dynamics (visible.starProjection Y))) ≤
          dist (dynamics Y) (dynamics (visible.starProjection Y)) := by
        simpa using visible.lipschitzWith_starProjection.dist_le_mul
          (dynamics Y) (dynamics (visible.starProjection Y))
      _ ≤ L * dist Y (visible.starProjection Y) :=
        hLipschitz.dist_le_mul Y (visible.starProjection Y)
      _ = L * ‖visibleᗮ.starProjection Y‖ := by
        rw [dist_eq_norm, Submodule.starProjection_orthogonal_val]
  refine ⟨defect_le_residual X, ?_⟩
  simpa [residualMass, Real.sqrt_sq (norm_nonneg _)] using
    defect_le_residual (densityCoordinate rho hrho)

example : Nonempty (HermitianTraceZero (d := Fin 1)) := ⟨0⟩

example : LipschitzWith 0
    (fun _ : HermitianTraceZero (d := Fin 1) =>
      (0 : HermitianTraceZero (d := Fin 1))) := by
  exact LipschitzWith.const (0 : HermitianTraceZero (d := Fin 1))

example : ∃ rho : Matrix (Fin 1) (Fin 1) ℂ,
    rho.PosSemidef ∧ Matrix.trace rho = 1 :=
  ⟨1, Matrix.PosSemidef.one, by simp⟩

#print axioms densityCoordinate
#print axioms visibleDynamics
#print axioms residual_controls_naturality

end D5.S3.Quantum.Tomography.ResidualControlsNaturality
