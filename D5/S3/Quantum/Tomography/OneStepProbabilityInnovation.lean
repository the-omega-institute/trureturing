/- GID: D5/S3/Quantum/Tomography/OneStepProbabilityInnovation
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/OneStepProbabilityInnovation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One complementary context removes exactly its centered probability energy. -/

import D5.S3.Observer.Tomography.InnovationEnergyRecurrence
import D5.S3.Quantum.Tomography.RankOneContextCommutator
import D5.S3.Quantum.Tomography.ResidualControlsNaturality

/- Library-search audit trail (2026-08-23):
   * Exact repository hit `InnovationEnergyRecurrence.innovation_energy_recurrence`
     supplies the one-step residual-energy identity and is applied directly.
   * Exact family hits `HermitianTraceZero`, `densityCoordinate`, `RankOneContext`,
     `centeredEffect`, and `residualMass` supply the source carrier and constructions.
   * Pinned Mathlib exact hit `Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection`
     supplies the residual-space direct sum and is applied directly.
   * Repository and pinned-Mathlib searches found no theorem packaging the centered
     probability drop with both public direct-sum clauses. -/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.OneStepProbabilityInnovation

open D5.S3.Observer.Tomography.InnovationEnergyRecurrence
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open D5.S3.Quantum.Tomography.ComplementaryContextProbabilityPythagoras
open D5.S3.Quantum.Tomography.RankOneContextCommutator
open D5.S3.Quantum.Tomography.ResidualControlsNaturality

variable {d : Nat} [NeZero d]

local instance matrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

local instance hermitianTraceZeroTopologicalSpace :
    TopologicalSpace (HermitianTraceZero (d := Fin d)) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

private lemma centered_projector_mem
    (context : RankOneContext d) (j : Fin d) :
    centeredEffect (context.projector j) ∈ HermitianTraceZero (d := Fin d) := by
  have hProjector := context.rankOne j
  have hHermitian : (context.projector j).IsHermitian := hProjector.1
  refine ⟨hHermitian.sub ?_, ?_⟩
  · exact Matrix.IsHermitian.smul (by simp)
      (by rw [isSelfAdjoint_iff, hProjector.2.2.1]; simp)
  · simp only [centeredEffect, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_one, hProjector.2.2.1]
    field_simp [show (Fintype.card (Fin d) : ℂ) ≠ 0 by
      exact_mod_cast Fintype.card_ne_zero]
    simp

/-- The centered projector coordinate of a complete rank-one context, on the
canonical real trace-zero Hermitian carrier. -/
def centeredProjector (context : RankOneContext d) (j : Fin d) :
    HermitianTraceZero (d := Fin d) :=
  ⟨centeredEffect (context.projector j), centered_projector_mem context j⟩

/-- The source's traceless diagonal plane, constructed as the real span of a
complete rank-one context's centered projectors. -/
def centeredContextPlane (context : RankOneContext d) :
    Submodule ℝ (HermitianTraceZero (d := Fin d)) :=
  Submodule.span ℝ (Set.range (centeredProjector context))

/-- The Born probability of one outcome of the added context. -/
def contextProbability (rho : Matrix (Fin d) (Fin d) ℂ)
    (context : RankOneContext d) (j : Fin d) : ℝ :=
  (Matrix.trace (rho * context.projector j)).re

/-- Adding one complementary rank-one context removes exactly its centered
probability energy from the residual mass. The old residual is the orthogonal
sum of the added context plane and the new residual. -/
theorem one_step_probability_innovation
    (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (context : RankOneContext d)
    (visible nextVisible : Submodule ℝ (HermitianTraceZero (d := Fin d)))
    [IsClosed (visible : Set (HermitianTraceZero (d := Fin d)))]
    [IsClosed (nextVisible : Set (HermitianTraceZero (d := Fin d)))]
    (hNested : visible ≤ nextVisible)
    (hNewContext :
      innovationSubspace visible nextVisible = centeredContextPlane context)
    (hProbabilityCoordinates :
      ‖(centeredContextPlane context).starProjection
          (densityCoordinate rho hrho)‖ ^ 2 =
        ∑ j, (contextProbability rho context j - (d : ℝ)⁻¹) ^ 2) :
    residualMass visible (densityCoordinate rho hrho) -
          residualMass nextVisible (densityCoordinate rho hrho) =
        ∑ j, (contextProbability rho context j - (d : ℝ)⁻¹) ^ 2 ∧
      visibleᗮ = centeredContextPlane context ⊔ nextVisibleᗮ ∧
      centeredContextPlane context ⟂ nextVisibleᗮ := by
  let X := densityCoordinate rho hrho
  have hRecurrence := innovation_energy_recurrence visible nextVisible X hNested
  have hDrop :
      residualMass visible X - residualMass nextVisible X =
        ∑ j, (contextProbability rho context j - (d : ℝ)⁻¹) ^ 2 := by
    have hRecurrence' :
        residualMass visible X = residualMass nextVisible X +
          ‖(innovationSubspace visible nextVisible).starProjection X‖ ^ 2 := by
      simpa only [residualMass, residualEnergy] using hRecurrence
    rw [hNewContext, hProbabilityCoordinates] at hRecurrence'
    linarith
  have hResidualSplit :
      visibleᗮ = innovationSubspace visible nextVisible ⊔ nextVisibleᗮ := by
    have hSplit := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
      (Submodule.orthogonal_le hNested)
    simpa only [innovationSubspace, Submodule.orthogonal_orthogonal,
      inf_comm, sup_comm] using hSplit.symm
  have hOrthogonal :
      innovationSubspace visible nextVisible ⟂ nextVisibleᗮ := by
    apply (Submodule.isOrtho_orthogonal_right nextVisible).mono_left
    exact inf_le_right
  rw [hNewContext] at hResidualSplit hOrthogonal
  exact ⟨hDrop, hResidualSplit, hOrthogonal⟩

#print axioms centeredProjector
#print axioms centeredContextPlane
#print axioms contextProbability
#print axioms one_step_probability_innovation

end D5.S3.Quantum.Tomography.OneStepProbabilityInnovation
