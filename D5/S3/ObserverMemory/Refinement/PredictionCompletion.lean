/- GID: D5/S3/ObserverMemory/Refinement/PredictionCompletion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/PredictionCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observation refinement induces a unique surjective map of predictive completions. -/

import D5.S0.Rewriting.Quotients.RelativeIdentityRefinement
import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

namespace D5.S3.ObserverMemory.Refinement.PredictionCompletion

open D5.S0.Rewriting.Quotients.RelativeIdentityRefinement
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- The complete-future relation is the kernel of `completeItinerary`. The exact
   repository theorem `relative_identity_refinement` supplies the quotient map
   and its uniqueness; the remaining equations follow on representatives. -/

/-- States modulo equality of every future readout. -/
abbrev CompletedState {Y O : Type*} (update : Y -> Y) (readout : Y -> O) :=
  Quotient (Setoid.ker (completeItinerary update readout))

/-- The canonical projection to predictive completion. -/
def completionProjection {Y O : Type*} (update : Y -> Y) (readout : Y -> O) :
    Y -> CompletedState update readout :=
  Quotient.mk _

/-- The state update induced on predictive completion. -/
def completionUpdate {Y O : Type*} (update : Y -> Y) (readout : Y -> O) :
    CompletedState update readout -> CompletedState update readout :=
  Quotient.map update (by
    intro y y' heq
    funext n
    simpa [completeItinerary, Function.iterate_succ_apply] using
      congrFun heq (n + 1))

/-- The current readout induced on predictive completion. -/
def completionReadout {Y O : Type*} (update : Y -> Y) (readout : Y -> O) :
    CompletedState update readout -> O :=
  Quotient.lift readout (by
    intro y y' heq
    simpa [completeItinerary] using congrFun heq 0)

private theorem completionUpdate_projection {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (y : Y) :
    completionUpdate update readout (completionProjection update readout y) =
      completionProjection update readout (update y) := rfl

/-- If a readout factors through a finer readout, its complete-future relation
is coarser. The induced map of predictive completions is uniquely determined,
surjective, and intertwines the projections, updates, and readouts. -/
theorem observation_refinement_completion
    {Y O P : Type*} (update : Y -> Y) (fine : Y -> O) (coarse : Y -> P)
    (forget : O -> P) (hfactor : coarse = forget ∘ fine) :
    (Setoid.ker (completeItinerary update fine) ≤
        Setoid.ker (completeItinerary update coarse)) ∧
      ∃! descend : CompletedState update fine -> CompletedState update coarse,
        Function.Surjective descend ∧
          completionProjection update coarse =
            descend ∘ completionProjection update fine ∧
          descend ∘ completionUpdate update fine =
            completionUpdate update coarse ∘ descend ∧
          completionReadout update coarse ∘ descend =
            forget ∘ completionReadout update fine := by
  have hitinerary :
      completeItinerary update coarse =
        (fun itinerary : Nat -> O => fun n => forget (itinerary n)) ∘
          completeItinerary update fine := by
    funext y n
    simp [completeItinerary, hfactor]
  have hrefinement :=
    relative_identity_refinement
      (completeItinerary update fine) (completeItinerary update coarse)
      (fun itinerary : Nat -> O => fun n => forget (itinerary n)) hitinerary
  rcases hrefinement with ⟨hle, descend, hdescend, hunique⟩
  refine ⟨hle, descend, ?_, ?_⟩
  · refine ⟨hdescend.1, ?_, ?_, ?_⟩
    · funext y
      exact (hdescend.2 y).symm
    · funext state
      refine Quotient.inductionOn' state (fun y => ?_)
      calc
        descend (completionUpdate update fine (completionProjection update fine y)) =
            descend (completionProjection update fine (update y)) :=
          congrArg descend (completionUpdate_projection update fine y)
        _ = completionProjection update coarse (update y) := hdescend.2 (update y)
        _ = completionUpdate update coarse (completionProjection update coarse y) :=
          (completionUpdate_projection update coarse y).symm
        _ = completionUpdate update coarse
            (descend (completionProjection update fine y)) :=
          congrArg (completionUpdate update coarse) (hdescend.2 y).symm
    · funext state
      refine Quotient.inductionOn' state (fun y => ?_)
      change completionReadout update coarse
          (descend (completionProjection update fine y)) =
        forget (completionReadout update fine (completionProjection update fine y))
      change completionReadout update coarse
          (descend (Quotient.mk'' y)) =
        forget (completionReadout update fine (Quotient.mk'' y))
      rw [hdescend.2 y]
      change coarse y = forget (fine y)
      rw [hfactor]
      rfl
  · intro candidate hcandidate
    apply hunique candidate
    refine ⟨hcandidate.1, ?_⟩
    intro y
    exact (congrFun hcandidate.2.1 y).symm

#print axioms observation_refinement_completion

end D5.S3.ObserverMemory.Refinement.PredictionCompletion
