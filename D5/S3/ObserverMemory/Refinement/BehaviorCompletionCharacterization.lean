/- GID: D5/S3/ObserverMemory/Refinement/BehaviorCompletionCharacterization
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/BehaviorCompletionCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Universal stable completion is uniquely equivalent to canonical completion. -/

import D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality
import D5.S3.ObserverMemory.Refinement.PredictionCompletion

/- Library-search audit trail (2026-08-25):
   * Repository search found the canonical `completeItinerary`, `CompletedState`,
     `completionProjection`, `completionUpdate`, and `completionReadout` declarations;
     they are imported rather than redeclared.
   * Exact family hit `prediction_completion_universality` supplies the comparison
     from any stable readout realization to the canonical completion and is applied below.
   * The close family hit `minimal_deterministic_completion` assumes finite carriers and
     concludes a one-way factor plus a cardinal bound, so it is not an exact general hit.
   * Pinned Mathlib search found `Function.surjInv`,
     `Function.rightInverse_surjInv`, and `Quotient.mk_surjective`; all are applied below.
   * Repository and pinned-Mathlib searches found no theorem exposing all three public
     completion clauses and the unique commuting equivalence at this generality. -/

namespace D5.S3.ObserverMemory.Refinement.BehaviorCompletionCharacterization

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.PredictionFactors.PredictionCompletionUniversality
open D5.S3.ObserverMemory.Refinement.PredictionCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- Any effective readout interface that is stable under the source update,
preserves the original readout, and factors through every effective stable
refinement is uniquely equivalent to the canonical behavior completion. -/
theorem behavior_completion_characterization
    {Y O W : Type u}
    (update : Y -> Y) (readout : Y -> O)
    (candidate : Y -> W) (candidateUpdate : W -> W)
    (candidateReadout : W -> O)
    (candidate_surjective : Function.Surjective candidate)
    (candidate_stable : candidate ∘ update = candidateUpdate ∘ candidate)
    (preserves_readout : readout = candidateReadout ∘ candidate)
    (universal_factorization :
      forall (V : Type u) (stable : Y -> V) (stableUpdate : V -> V)
        (stableReadout : V -> O),
        Function.Surjective stable ->
        stable ∘ update = stableUpdate ∘ stable ->
        readout = stableReadout ∘ stable ->
        ∃! factor : V -> W, candidate = factor ∘ stable) :
    ∃! equivalence : W ≃ CompletedState update readout,
      completionProjection update readout = equivalence ∘ candidate := by
  rcases prediction_completion_universality update readout candidate
      candidateUpdate candidateReadout candidate_stable preserves_readout with
    ⟨candidateItinerary, itinerary_factors⟩
  let representative : W -> Y := Function.surjInv candidate_surjective
  have representative_spec : Function.RightInverse representative candidate :=
    Function.rightInverse_surjInv candidate_surjective
  let toCompletion : W -> CompletedState update readout :=
    fun state => completionProjection update readout (representative state)
  have projection_factors :
      completionProjection update readout = toCompletion ∘ candidate := by
    funext state
    apply Quotient.sound'
    change completeItinerary update readout state =
      completeItinerary update readout (representative (candidate state))
    calc
      completeItinerary update readout state =
          candidateItinerary (candidate state) :=
        congrFun itinerary_factors state
      _ = candidateItinerary (candidate (representative (candidate state))) :=
        congrArg candidateItinerary (representative_spec (candidate state)).symm
      _ = completeItinerary update readout
          (representative (candidate state)) :=
        (congrFun itinerary_factors (representative (candidate state))).symm
  have completion_stable :
      completionProjection update readout ∘ update =
        completionUpdate update readout ∘ completionProjection update readout := by
    rfl
  have completion_preserves_readout :
      readout = completionReadout update readout ∘
        completionProjection update readout := by
    rfl
  rcases universal_factorization (CompletedState update readout)
      (completionProjection update readout) (completionUpdate update readout)
      (completionReadout update readout) Quotient.mk_surjective
      completion_stable completion_preserves_readout with
    ⟨fromCompletion, candidate_factors, _⟩
  have left_inverse : Function.LeftInverse fromCompletion toCompletion := by
    intro state
    rcases candidate_surjective state with ⟨source, rfl⟩
    calc
      fromCompletion (toCompletion (candidate source)) =
          fromCompletion (completionProjection update readout source) :=
        congrArg fromCompletion (congrFun projection_factors source).symm
      _ = candidate source := (congrFun candidate_factors source).symm
  have right_inverse : Function.RightInverse fromCompletion toCompletion := by
    intro completed
    rcases Quotient.mk_surjective completed with ⟨source, rfl⟩
    calc
      toCompletion (fromCompletion (completionProjection update readout source)) =
          toCompletion (candidate source) :=
        congrArg toCompletion (congrFun candidate_factors source).symm
      _ = completionProjection update readout source :=
        (congrFun projection_factors source).symm
  let equivalence : W ≃ CompletedState update readout :=
    ⟨toCompletion, fromCompletion, left_inverse, right_inverse⟩
  refine ⟨equivalence, projection_factors, ?_⟩
  intro other other_factors
  ext state
  rcases candidate_surjective state with ⟨source, rfl⟩
  calc
    other (candidate source) = completionProjection update readout source :=
      (congrFun other_factors source).symm
    _ = equivalence (candidate source) := congrFun projection_factors source

#print axioms behavior_completion_characterization

end D5.S3.ObserverMemory.Refinement.BehaviorCompletionCharacterization
