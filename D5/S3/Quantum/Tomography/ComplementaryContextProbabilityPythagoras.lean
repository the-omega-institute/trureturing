/- GID: D5/S3/Quantum/Tomography/ComplementaryContextProbabilityPythagoras
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ComplementaryContextProbabilityPythagoras
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Orthogonal context coordinates split purity excess from residual mass. -/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/- Library-search audit trail (2026-08-17):
   * Local pinned-Mathlib grep and Loogle found the exact projection identity
     `Submodule.norm_sq_eq_add_norm_sq_starProjection`; it is applied directly below.
   * Loogle's shaped projection query was ambiguous, while its exact-name query returned that
     declaration as its sole hit. LeanSearch's attempted API query returned HTTP 404.
   * Repository searches for the probability-deviation and residual-mass identity found no
     equal theorem. Adjacent projection-complement modules do not state the trace formula. -/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Quantum.Tomography.ComplementaryContextProbabilityPythagoras

/-- Squared Hilbert--Schmidt mass in the orthogonal complement of the visible coordinates. -/
def residualMass {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (visible : Submodule ℝ E) [IsClosed (visible : Set E)]
    (state : E) : ℝ :=
  ‖visibleᗮ.starProjection state‖ ^ 2

/-- When the visible projection is coordinatized by centered basis probabilities, purity excess
is their total squared deviation plus the complementary Hilbert--Schmidt residual mass. -/
theorem complementary_context_probability_pythagoras
    {d L E : Type*} [Fintype d] [Nonempty d] [Fintype L]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (rho : Matrix d d ℂ) (state : E) (probability : L -> d -> ℝ)
    (visible : Submodule ℝ E) [IsClosed (visible : Set E)]
    (hpurity :
      (Matrix.trace (rho * rho)).re - (Fintype.card d : ℝ)⁻¹ =
        ‖state‖ ^ 2)
    (hcoordinates :
      ‖visible.starProjection state‖ ^ 2 =
        ∑ l, ∑ j, (probability l j - (Fintype.card d : ℝ)⁻¹) ^ 2) :
    (Matrix.trace (rho * rho)).re - (Fintype.card d : ℝ)⁻¹ =
      (∑ l, ∑ j, (probability l j - (Fintype.card d : ℝ)⁻¹) ^ 2) +
        residualMass visible state := by
  calc
    (Matrix.trace (rho * rho)).re - (Fintype.card d : ℝ)⁻¹ =
        ‖state‖ ^ 2 := hpurity
    _ = ‖visible.starProjection state‖ ^ 2 +
        ‖visibleᗮ.starProjection state‖ ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_starProjection state visible
    _ = (∑ l, ∑ j, (probability l j - (Fintype.card d : ℝ)⁻¹) ^ 2) +
        residualMass visible state := by rw [hcoordinates]; rfl

#print axioms complementary_context_probability_pythagoras

end D5.S3.Quantum.Tomography.ComplementaryContextProbabilityPythagoras
