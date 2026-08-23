/- GID: D5/S3/Quantum/Tomography/FutureProbabilityResidualCorrelation
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/FutureProbabilityResidualCorrelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Future probability error is exactly the correlation of two orthogonal residuals. -/

import D5.S3.Quantum.Fibers.CenteredEffectTowerStability
import D5.S3.Quantum.Tomography.ResidualControlsNaturality

/- Library-search audit trail (2026-08-23):
   * Exact repository hits `HermitianTraceZero`, `densityCoordinate`,
     `towerSpace`, `residualSpace`, and `residualMass` supply the source's
     carrier, centered state, visible tower, residual tower, and residual mass.
   * Repository searches found no linear prediction representative or theorem
     packaging the exact residual correlation together with its norm bound.
   * Pinned Mathlib exact hits `Submodule.starProjection_orthogonal_val`,
     `Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left`,
     `abs_real_inner_le_norm`, and `Real.sqrt_sq` are applied below.
   * Exact atom-id search outside the digestion ledger and source documentation missed;
     `loogle` and `leansearch` executables are absent from PATH. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix
open ClosedSubmodule

namespace D5.S3.Quantum.Tomography.FutureProbabilityResidualCorrelation

open D5.S3.Quantum.Fibers.CenteredEffectTowerStability
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open D5.S3.Quantum.Tomography.ComplementaryContextProbabilityPythagoras
open D5.S3.Quantum.Tomography.ResidualControlsNaturality

variable {d : Type*} [Fintype d] [Nonempty d] [DecidableEq d]

local instance matrixNormedAddCommGroup : NormedAddCommGroup (Matrix d d ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace : InnerProductSpace ℂ (Matrix d d ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance hermitianTraceZeroTopologicalSpace :
    TopologicalSpace (HermitianTraceZero (d := d)) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance hermitianTraceZeroSubmoduleIsClosed
    (visible : Submodule ℝ (HermitianTraceZero (d := d))) :
    IsClosed (visible : Set (HermitianTraceZero (d := d))) :=
  visible.closed_of_finiteDimensional

/-- The source's linear prediction representative: retain the visible centered
coordinate and restore the trace-one scalar part. It is not asserted positive. -/
def linearPredictionRepresentative
    (visible : Submodule ℝ (HermitianTraceZero (d := d)))
    [IsClosed (visible : Set (HermitianTraceZero (d := d)))]
    (state : HermitianTraceZero (d := d)) : Matrix d d ℂ :=
  (visible.starProjection state).1 +
    (Fintype.card d : ℂ)⁻¹ • (1 : Matrix d d ℂ)

private theorem matrix_inner_eq_trace_conjTranspose_mul
    (A B : Matrix d d ℂ) :
    inner ℂ A B = Matrix.trace (Aᴴ * B) := by
  change Matrix.trace (B * 1 * Aᴴ) = Matrix.trace (Aᴴ * B)
  rw [mul_one, Matrix.trace_mul_comm]

private theorem real_inner_eq_trace_mul
    (A B : HermitianTraceZero (d := d)) :
    inner ℝ A B = (Matrix.trace (A.1 * B.1)).re := by
  change (inner ℂ A.1 B.1).re = _
  rw [matrix_inner_eq_trace_conjTranspose_mul, A.2.1.eq]

private theorem state_sub_representative
    (rho : Matrix d d ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (visible : Submodule ℝ (HermitianTraceZero (d := d)))
    [IsClosed (visible : Set (HermitianTraceZero (d := d)))] :
    rho - linearPredictionRepresentative visible (densityCoordinate rho hrho) =
      (visibleᗮ.starProjection (densityCoordinate rho hrho)).1 := by
  rw [Submodule.starProjection_orthogonal_val]
  change rho - ((visible.starProjection (densityCoordinate rho hrho)).1 +
      (Fintype.card d : ℂ)⁻¹ • (1 : Matrix d d ℂ)) =
    centeredState rho - (visible.starProjection (densityCoordinate rho hrho)).1
  unfold centeredState
  abel

private theorem residual_inner_projection
    (residual : Submodule ℝ (HermitianTraceZero (d := d)))
    (state future : HermitianTraceZero (d := d)) :
    inner ℝ (residual.starProjection state) future =
      inner ℝ (residual.starProjection state) (residual.starProjection future) := by
  calc
    inner ℝ (residual.starProjection state) future =
        inner ℝ state (residual.starProjection future) :=
      residual.inner_starProjection_left_eq_right state future
    _ = inner ℝ (residual.starProjection state)
        (residual.starProjection future) := by
      have hfixed : residual.starProjection (residual.starProjection future) =
          residual.starProjection future :=
        residual.starProjection_eq_self_iff.mpr
          (residual.starProjection_apply_mem future)
      simpa only [hfixed] using
        (residual.inner_starProjection_left_eq_right state
          (residual.starProjection future)).symm

private def threeLevelDensity : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun i => if i = 0 then 1 else 0

private theorem threeLevelDensity_valid :
    threeLevelDensity.PosSemidef ∧ Matrix.trace threeLevelDensity = 1 := by
  constructor
  · rw [threeLevelDensity, Matrix.posSemidef_diagonal_iff]
    intro i
    split <;> simp_all
  · simp [threeLevelDensity, Matrix.trace, Fin.sum_univ_succ]

private def threeLevelDirection : HermitianTraceZero (d := Fin 3) :=
  ⟨Matrix.diagonal fun i => if i = 0 then 1 else if i = 2 then -1 else 0, by
    constructor
    · rw [Matrix.isHermitian_diagonal_iff]
      intro i
      by_cases h0 : i = 0
      · simp [h0]
      · by_cases h2 : i = 2
        · subst i
          norm_num [h0, isSelfAdjoint_iff, RCLike.star_def]
        · simp [h0, h2]
    · simp [Matrix.trace, Fin.sum_univ_succ]⟩

private def threeLevelVisible :
    Submodule ℝ (HermitianTraceZero (d := Fin 3)) :=
  ℝ ∙ threeLevelDirection

private theorem threeLevel_projection :
    threeLevelVisible.starProjection
        (densityCoordinate threeLevelDensity threeLevelDensity_valid) =
      (2 : ℝ)⁻¹ • threeLevelDirection := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [threeLevelVisible, Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_eq_trace_mul]
    norm_num [densityCoordinate, centeredState, threeLevelDensity,
      threeLevelDirection, Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply,
      Fin.sum_univ_succ, show (1 : Fin 3) ≠ 2 by decide]

private theorem threeLevel_representative_not_positive :
    ¬ (linearPredictionRepresentative threeLevelVisible
      (densityCoordinate threeLevelDensity threeLevelDensity_valid)).PosSemidef := by
  intro hpositive
  have hcoordinate := hpositive.2 (Finsupp.single (2 : Fin 3) 1)
  rw [linearPredictionRepresentative, threeLevel_projection] at hcoordinate
  norm_num [threeLevelDirection, Matrix.mul_apply, Fin.sum_univ_succ] at hcoordinate
  rw [if_neg (show (2 : Fin 3) ≠ 0 by decide)] at hcoordinate
  norm_num at hcoordinate
  exact (show ¬ ((1 : ℂ) / 6 ≤ 0) by
    rw [Complex.not_le_zero_iff]
    left
    norm_num) hcoordinate

/-- For every centered future effect obtained by iterating the Heisenberg map,
the linear prediction error is exactly the Hilbert--Schmidt correlation of the
state and effect residuals and obeys the corresponding Cauchy--Schwarz bound.
The final conjunct gives an explicit valid density whose linear representative
after projection onto a trace-zero diagonal line is not positive. -/
theorem future_probability_residual_correlation
    {r : Nat} (rho : Matrix d d ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (heisenberg : HermitianTraceZero (d := d) →ₗ[ℝ]
      HermitianTraceZero (d := d))
    (effects : Fin (r + 1) → HermitianTraceZero (d := d))
    (m k : Nat) (a : Fin (r + 1)) :
    let visible := towerSpace heisenberg effects m
    let residual := residualSpace heisenberg effects m
    let state := densityCoordinate rho hrho
    let future := (heisenberg^[k]) (effects a)
    let representative := linearPredictionRepresentative visible state
    let error := (Matrix.trace ((rho - representative) * future.1)).re
    (error = inner ℝ (residual.starProjection state)
        (residual.starProjection future)) ∧
      |error| ≤ Real.sqrt (residualMass visible state) *
        ‖residual.starProjection future‖ ∧
      ¬ (linearPredictionRepresentative threeLevelVisible
        (densityCoordinate threeLevelDensity threeLevelDensity_valid)).PosSemidef := by
  dsimp only
  let visible := towerSpace heisenberg effects m
  let residual := residualSpace heisenberg effects m
  let state := densityCoordinate rho hrho
  let future := (heisenberg^[k]) (effects a)
  let representative := linearPredictionRepresentative visible state
  let error := (Matrix.trace ((rho - representative) * future.1)).re
  have herror : error = inner ℝ (residual.starProjection state)
      (residual.starProjection future) := by
    have hdifference := state_sub_representative rho hrho visible
    have htrace : error = inner ℝ (residual.starProjection state) future := by
      simp only [error, representative]
      rw [hdifference]
      exact (real_inner_eq_trace_mul (residual.starProjection state) future).symm
    exact htrace.trans (residual_inner_projection residual state future)
  refine ⟨herror, ?_, threeLevel_representative_not_positive⟩
  calc
    |error| = |inner ℝ (residual.starProjection state)
        (residual.starProjection future)| := congrArg abs herror
    _ ≤ ‖residual.starProjection state‖ * ‖residual.starProjection future‖ :=
      abs_real_inner_le_norm _ _
    _ = Real.sqrt (residualMass visible state) *
        ‖residual.starProjection future‖ := by
      simp only [residual, residualSpace, residualMass, visible,
        Real.sqrt_sq (norm_nonneg _)]

#print axioms linearPredictionRepresentative
#print axioms future_probability_residual_correlation

end D5.S3.Quantum.Tomography.FutureProbabilityResidualCorrelation
