/- GID: D5/S3/ObserverMemory/PredictionFactors/DeterministicCompletionMinimality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/DeterministicCompletionMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite deterministic realizations factor uniquely onto the completed state. -/

import D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality
import D5.S3.ObserverMemory.Refinement.PredictionCompletion
import Mathlib.SetTheory.Cardinal.NatCard

/- Library-search audit trail (2026-08-21):
   * Repository search found the canonical `CompletedState`, `completionProjection`,
     `completionUpdate`, and `completionReadout` declarations; they are imported rather than
     redeclared.
   * Exact repository hit `prediction_completion_universality` constructs the full-itinerary
     factorization used to prove independence from representatives; it is applied directly.
   * Exact pinned-Mathlib hits `Function.surjInv`, `Function.rightInverse_surjInv`, and
     `Nat.card_le_card_of_surjective` are applied directly below.
   * Repository and pinned-Mathlib searches found no equal or stronger theorem carrying the
     unique surjective factor, all three commuting equations, and the cardinal bound together.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

namespace D5.S3.ObserverMemory.PredictionFactors.DeterministicCompletionMinimality

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality
open D5.S3.ObserverMemory.Refinement.PredictionCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every finite deterministic implementation of the source update and readout admits a unique
surjective factor onto the canonical completed-state carrier. The factor commutes with the source
projection, update, and readout, and its surjectivity gives the finite cardinal lower bound. -/
theorem minimal_deterministic_completion
    {Y O W : Type*} [Finite Y] [Finite W]
    (update : Y -> Y) (readout : Y -> O)
    (implementation : Y -> W) (implementationUpdate : W -> W)
    (implementationReadout : W -> O)
    (implementation_surjective : Function.Surjective implementation)
    (step_factors : implementation ∘ update = implementationUpdate ∘ implementation)
    (readout_factors : readout = implementationReadout ∘ implementation) :
    (∃! factor : W -> CompletedState update readout,
      Function.Surjective factor ∧
        completionProjection update readout = factor ∘ implementation ∧
        factor ∘ implementationUpdate = completionUpdate update readout ∘ factor ∧
        completionReadout update readout ∘ factor = implementationReadout) ∧
      Nat.card (CompletedState update readout) <= Nat.card W := by
  rcases prediction_completion_universality update readout implementation
      implementationUpdate implementationReadout step_factors readout_factors with
    ⟨implementationItinerary, itinerary_factors⟩
  let representative : W -> Y := Function.surjInv implementation_surjective
  have representative_spec : Function.RightInverse representative implementation :=
    Function.rightInverse_surjInv implementation_surjective
  let factor : W -> CompletedState update readout :=
    fun state => completionProjection update readout (representative state)
  have projection_factors :
      completionProjection update readout = factor ∘ implementation := by
    funext state
    apply Quotient.sound'
    change completeItinerary update readout state =
      completeItinerary update readout (representative (implementation state))
    calc
      completeItinerary update readout state =
          implementationItinerary (implementation state) :=
        congrFun itinerary_factors state
      _ = implementationItinerary
          (implementation (representative (implementation state))) :=
        congrArg implementationItinerary
          (representative_spec (implementation state)).symm
      _ = completeItinerary update readout
          (representative (implementation state)) :=
        (congrFun itinerary_factors
          (representative (implementation state))).symm
  have factor_surjective : Function.Surjective factor := by
    intro completed
    refine Quotient.inductionOn' completed (fun state => ?_)
    exact ⟨implementation state, (congrFun projection_factors state).symm⟩
  have factor_update :
      factor ∘ implementationUpdate = completionUpdate update readout ∘ factor := by
    funext state
    rcases implementation_surjective state with ⟨source, rfl⟩
    calc
      factor (implementationUpdate (implementation source)) =
          factor (implementation (update source)) :=
        congrArg factor (congrFun step_factors source).symm
      _ = completionProjection update readout (update source) :=
        (congrFun projection_factors (update source)).symm
      _ = completionUpdate update readout
          (completionProjection update readout source) := rfl
      _ = completionUpdate update readout (factor (implementation source)) :=
        congrArg (completionUpdate update readout)
          (congrFun projection_factors source)
  have factor_readout :
      completionReadout update readout ∘ factor = implementationReadout := by
    funext state
    rcases implementation_surjective state with ⟨source, rfl⟩
    calc
      completionReadout update readout (factor (implementation source)) =
          completionReadout update readout
            (completionProjection update readout source) :=
        congrArg (completionReadout update readout)
          (congrFun projection_factors source).symm
      _ = readout source := rfl
      _ = implementationReadout (implementation source) :=
        congrFun readout_factors source
  refine ⟨?_, Nat.card_le_card_of_surjective factor factor_surjective⟩
  refine ⟨factor, ⟨factor_surjective, projection_factors, factor_update,
    factor_readout⟩, ?_⟩
  intro candidate candidate_property
  funext state
  rcases implementation_surjective state with ⟨source, rfl⟩
  calc
    candidate (implementation source) =
        completionProjection update readout source :=
      (congrFun candidate_property.2.1 source).symm
    _ = factor (implementation source) := congrFun projection_factors source

/-- The hypotheses and full conclusion are jointly inhabited by the one-state system. -/
example :
    (∃! factor : Unit -> CompletedState (id : Unit -> Unit) id,
      Function.Surjective factor ∧
        completionProjection id id = factor ∘ id ∧
        factor ∘ id = completionUpdate id id ∘ factor ∧
        completionReadout id id ∘ factor = id) ∧
      Nat.card (CompletedState (id : Unit -> Unit) id) <= Nat.card Unit := by
  exact minimal_deterministic_completion id id id id id
    Function.surjective_id rfl rfl

/-- The source state domain used by the witness is inhabited. -/
example : Unit := ()

#print axioms minimal_deterministic_completion

end D5.S3.ObserverMemory.PredictionFactors.DeterministicCompletionMinimality
