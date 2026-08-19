/- GID: D5/S3/Quantum/Dynamics/PredictionClosureDynamicalRepair
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PredictionClosureDynamicalRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The least invariant observer closure induces dynamics on the visible quotient. -/

import D5.S3.Quantum.Dynamics.ObserverOrbitClosure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Quotient.Basic

/- Library-search audit trail (2026-08-18):
   * Repository search exactly found `observer_closure_is_least_invariant`,
     which constructs the power-orbit closure and proves its invariance and
     minimality. It is imported and directly applied below.
   * Pinned-Mathlib search exactly found
     `Module.End.mem_invtSubmodule_adjoint_iff`, which transfers invariance to
     the adjoint-invariant orthogonal residual; it is directly applied below.
   * Pinned-Mathlib search also exactly found `Submodule.mapQ` and
     `Submodule.mapQ_mkQ`, which construct the descended quotient evolution
     and prove its canonical projection equation. No theorem packages these
     results with final invisibility congruence and closure minimality. -/

noncomputable section

namespace D5.S3.Quantum.Dynamics.PredictionClosureDynamicalRepair

open D5.S3.Quantum.Dynamics.ObserverOrbitClosure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Differences invisible to every observable in the forward orbit closure. -/
def predictionResidual (observableEvolution : Module.End ℝ V)
    (visible : Submodule ℝ V) : Submodule ℝ V :=
  (observerClosure observableEvolution visible)ᗮ

/-- Two state vectors are finally indistinguishable when their difference is
orthogonal to every observable generated from the current visible space. -/
def FinallyInvisible (observableEvolution : Module.End ℝ V)
    (visible : Submodule ℝ V) (first second : V) : Prop :=
  first - second ∈ predictionResidual observableEvolution visible

private theorem prediction_residual_invariant [FiniteDimensional ℝ V]
    (observableEvolution : Module.End ℝ V) (visible : Submodule ℝ V) :
    predictionResidual observableEvolution visible ∈
      Module.End.invtSubmodule observableEvolution.adjoint := by
  rw [Module.End.mem_invtSubmodule_adjoint_iff]
  simpa [predictionResidual] using
    (observer_closure_is_least_invariant observableEvolution visible).2.2.2.1

private theorem final_invisibility_preserved [FiniteDimensional ℝ V]
    (observableEvolution : Module.End ℝ V) (visible : Submodule ℝ V)
    {first second : V}
    (hInvisible : FinallyInvisible observableEvolution visible first second) :
    FinallyInvisible observableEvolution visible
      (observableEvolution.adjoint first)
      (observableEvolution.adjoint second) := by
  have hMapped := prediction_residual_invariant observableEvolution visible hInvisible
  change observableEvolution.adjoint (first - second) ∈
    predictionResidual observableEvolution visible at hMapped
  change observableEvolution.adjoint first - observableEvolution.adjoint second ∈
    predictionResidual observableEvolution visible
  simpa only [LinearMap.map_sub] using hMapped

/-- State evolution induced on the quotient by final observational
indistinguishability. -/
def quotientEvolution [FiniteDimensional ℝ V]
    (observableEvolution : Module.End ℝ V) (visible : Submodule ℝ V) :
    (V ⧸ predictionResidual observableEvolution visible) →ₗ[ℝ]
      (V ⧸ predictionResidual observableEvolution visible) :=
  (predictionResidual observableEvolution visible).mapQ
    (predictionResidual observableEvolution visible)
    observableEvolution.adjoint
    (prediction_residual_invariant observableEvolution visible)

/-- Closing the current visible coordinates under observable evolution is the
least coordinate extension that makes final invisibility a state-evolution
congruence and therefore supports canonical quotient dynamics. -/
theorem prediction_closure_minimal_dynamical_repair
    [FiniteDimensional ℝ V]
    (observableEvolution : Module.End ℝ V) (visible : Submodule ℝ V) :
    visible ≤ observerClosure observableEvolution visible ∧
    observerClosure observableEvolution visible ∈
      observableEvolution.invtSubmodule ∧
    predictionResidual observableEvolution visible ∈
      Module.End.invtSubmodule observableEvolution.adjoint ∧
    (∀ first second,
      FinallyInvisible observableEvolution visible first second →
        FinallyInvisible observableEvolution visible
          (observableEvolution.adjoint first)
          (observableEvolution.adjoint second)) ∧
    (quotientEvolution observableEvolution visible).comp
        (predictionResidual observableEvolution visible).mkQ =
      (predictionResidual observableEvolution visible).mkQ.comp
        observableEvolution.adjoint ∧
    (∀ extension : Submodule ℝ V,
      visible ≤ extension → extension ∈ observableEvolution.invtSubmodule →
        observerClosure observableEvolution visible ≤ extension) := by
  have closureLaws :=
    observer_closure_is_least_invariant observableEvolution visible
  refine ⟨closureLaws.1, closureLaws.2.2.2.1,
    prediction_residual_invariant observableEvolution visible, ?_, ?_,
    closureLaws.2.2.2.2⟩
  · intro first second hInvisible
    exact final_invisibility_preserved observableEvolution visible hInvisible
  · simpa [quotientEvolution] using
      (Submodule.mapQ_mkQ
        (predictionResidual observableEvolution visible)
        (predictionResidual observableEvolution visible)
        observableEvolution.adjoint)

#print axioms prediction_closure_minimal_dynamical_repair

end D5.S3.Quantum.Dynamics.PredictionClosureDynamicalRepair
