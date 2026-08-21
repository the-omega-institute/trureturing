/- GID: D5/S3/ObserverMemory/PredictionFactors/MinimalNaturality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/MinimalNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Diagonal naturality forces the unique surjective predictive-completion factor. -/

import D5.S3.ObserverMemory.PredictionFactors.DeterministicCompletionMinimality

universe uA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionFactors.MinimalNaturality

open D5.S3.ObserverMemory.Refinement.PredictionCompletion
open D5.S3.ObserverMemory.PredictionFactors.DeterministicCompletionMinimality

/- Source-semantics primitives for evaluation tables and their pushed-forward values. -/
def diagonalEvaluation {A Y : Type*} (tau : Y -> Y) (table : A -> A -> Y) : A -> Y :=
  fun a => tau (table a a)

def pushedTable {A Y W : Type*} (r : Y -> W) (table : A -> A -> Y) : A -> A -> W :=
  fun a b => r (table a b)

def pushedVector {A Y W : Type*} (r : Y -> W) (vector : A -> Y) : A -> W :=
  fun a => r (vector a)

theorem minimal_naturality_factor
    {Y O W : Type*} [Finite Y] [Finite W] [Nonempty Y]
    (tau : Y -> Y) (q : Y -> O)
    (r : Y -> W) (o : W -> O) (sigma : W -> W)
    (r_surjective : Function.Surjective r)
    (readout_preserved : q = o ∘ r)
    (naturality : ∀ {A : Type uA} [Nonempty A] (table : A -> A -> Y),
      pushedVector r (diagonalEvaluation tau table) =
        diagonalEvaluation sigma (pushedTable r table)) :
    (r ∘ tau = sigma ∘ r) ∧
      ∃! h : W -> CompletedState tau q,
        Function.Surjective h ∧
          completionProjection tau q = h ∘ r := by
  have step_factors : r ∘ tau = sigma ∘ r := by
    funext y
    let singleton : ULift.{uA} Unit := ULift.up ()
    let table : ULift.{uA} Unit -> ULift.{uA} Unit -> Y := fun _ _ => y
    have htable := naturality (A := ULift.{uA} Unit) table
    have hpoint := congrFun htable singleton
    change r (tau y) = sigma (r y) at hpoint
    exact hpoint
  rcases minimal_deterministic_completion tau q r sigma o r_surjective
      step_factors readout_preserved with
    ⟨⟨factor, factor_property, _⟩, _⟩
  refine ⟨step_factors, factor, ⟨factor_property.1, factor_property.2.1⟩, ?_⟩
  intro candidate candidate_property
  funext w
  rcases r_surjective w with ⟨y, rfl⟩
  calc
    candidate (r y) = completionProjection tau q y :=
      (congrFun candidate_property.2 y).symm
    _ = factor (r y) := congrFun factor_property.2.1 y

#print axioms minimal_naturality_factor

end D5.S3.ObserverMemory.PredictionFactors.MinimalNaturality
