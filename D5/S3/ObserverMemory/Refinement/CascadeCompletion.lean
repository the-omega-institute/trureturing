/- GID: D5/S3/ObserverMemory/Refinement/CascadeCompletion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/CascadeCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Completing a fine readout and then a coarse one equals direct coarse completion. -/

import D5.S3.ObserverMemory.Refinement.PredictionCompletion
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-18):
   * The repository exact hit `observation_refinement_completion` supplies the
     canonical surjective map from the fine completion to the coarse one; it
     is applied below.
   * Pinned Mathlib and Loogle returned the exact third-isomorphism hit
     `Setoid.quotientQuotientEquivQuotient`; it is applied directly below.
   * Supporting exact hits `Quotient.map_surjective`, `Quotient.eq`, and
     `Quotient.congrRight` respectively establish surjectivity, compare
     representative relations, and transport the quotient relation.
   * LeanSearch's query endpoint returned HTTP 404. Repository search found no
     theorem covering the second-stage future relation and quotient
     identification together. -/

namespace D5.S3.ObserverMemory.Refinement.CascadeCompletion

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Refinement.PredictionCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The coarse readout induced on the fine predictive completion. -/
def coarseReadoutOnFineCompletion {Y O P : Type*}
    (update : Y -> Y) (fine : Y -> O) (forget : O -> P) :
    CompletedState update fine -> P :=
  forget ∘ completionReadout update fine

/-- Infinite-future equality after first completing the fine readout. -/
def secondStageRelation {Y O P : Type*}
    (update : Y -> Y) (fine : Y -> O) (forget : O -> P) :
    Setoid (CompletedState update fine) :=
  Setoid.ker
    (completeItinerary (completionUpdate update fine)
      (coarseReadoutOnFineCompletion update fine forget))

/-- The canonical map from the fine completion to the coarse completion. -/
def completionFactor {Y O P : Type*}
    (update : Y -> Y) (fine : Y -> O) (coarse : Y -> P)
    (forget : O -> P) (hfactor : coarse = forget ∘ fine) :
    CompletedState update fine -> CompletedState update coarse :=
  Quot.mapRight
    (observation_refinement_completion update fine coarse forget hfactor).1

private theorem completion_update_iterate_projection {Y O : Type*}
    (update : Y -> Y) (fine : Y -> O) (n : Nat) (y : Y) :
    ((completionUpdate update fine)^[n])
        (completionProjection update fine y) =
      completionProjection update fine ((update^[n]) y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        ((completionUpdate update fine)^[n])
            (completionProjection update fine (update y)) =
          completionProjection update fine ((update^[n]) (update y))
      exact ih (update y)

/-- The second-stage relation on projected states is the original coarse
infinite-future relation. -/
theorem second_stage_relation_projection {Y O P : Type*}
    (update : Y -> Y) (fine : Y -> O) (coarse : Y -> P)
    (forget : O -> P) (hfactor : coarse = forget ∘ fine) (y y' : Y) :
    secondStageRelation update fine forget
        (completionProjection update fine y)
        (completionProjection update fine y') ↔
      Setoid.ker (completeItinerary update coarse) y y' := by
  have hitinerary (state : Y) :
      completeItinerary (completionUpdate update fine)
          (coarseReadoutOnFineCompletion update fine forget)
          (completionProjection update fine state) =
        completeItinerary update coarse state := by
    funext n
    change
      forget (completionReadout update fine
        (((completionUpdate update fine)^[n])
          (completionProjection update fine state))) =
        coarse ((update^[n]) state)
    rw [completion_update_iterate_projection]
    change forget (fine ((update^[n]) state)) = coarse ((update^[n]) state)
    rw [hfactor]
    rfl
  change
    completeItinerary (completionUpdate update fine)
        (coarseReadoutOnFineCompletion update fine forget)
        (completionProjection update fine y) =
      completeItinerary (completionUpdate update fine)
        (coarseReadoutOnFineCompletion update fine forget)
        (completionProjection update fine y') ↔
      completeItinerary update coarse y = completeItinerary update coarse y'
  rw [hitinerary y, hitinerary y']

@[simp] theorem completion_factor_projection {Y O P : Type*}
    (update : Y -> Y) (fine : Y -> O) (coarse : Y -> P)
    (forget : O -> P) (hfactor : coarse = forget ∘ fine) (y : Y) :
    completionFactor update fine coarse forget hfactor
        (completionProjection update fine y) =
      completionProjection update coarse y := rfl

private theorem completion_factor_surjective {Y O P : Type*}
    (update : Y -> Y) (fine : Y -> O) (coarse : Y -> P)
    (forget : O -> P) (hfactor : coarse = forget ∘ fine) :
    Function.Surjective
      (completionFactor update fine coarse forget hfactor) := by
  exact Quotient.map_surjective
    (observation_refinement_completion update fine coarse forget hfactor).1
    Function.surjective_id

private theorem second_stage_relation_eq_factor_kernel {Y O P : Type*}
    (update : Y -> Y) (fine : Y -> O) (coarse : Y -> P)
    (forget : O -> P) (hfactor : coarse = forget ∘ fine) :
    secondStageRelation update fine forget =
      Setoid.ker (completionFactor update fine coarse forget hfactor) := by
  apply Setoid.ext
  intro first second
  refine Quotient.inductionOn₂' first second fun y y' => ?_
  change
    secondStageRelation update fine forget
        (completionProjection update fine y)
        (completionProjection update fine y') ↔
      completionFactor update fine coarse forget hfactor
          (completionProjection update fine y) =
        completionFactor update fine coarse forget hfactor
          (completionProjection update fine y')
  rw [second_stage_relation_projection update fine coarse forget hfactor y y']
  change
    Setoid.ker (completeItinerary update coarse) y y' ↔
      completionProjection update coarse y =
        completionProjection update coarse y'
  exact Quotient.eq.symm

/-- Quotienting the fine completion by its coarse future relation is
canonically equivalent to direct coarse completion. -/
def cascadeCompletionEquiv {Y O P : Type*}
    (update : Y -> Y) (fine : Y -> O) (coarse : Y -> P)
    (forget : O -> P) (hfactor : coarse = forget ∘ fine) :
    Quotient (secondStageRelation update fine forget) ≃
      CompletedState update coarse := by
  let hle :=
    (observation_refinement_completion update fine coarse forget hfactor).1
  let changeRelation :
      Quotient (secondStageRelation update fine forget) ≃
        Quotient (Setoid.ker (Quot.mapRight hle)) :=
    Quotient.congrRight fun first second => by
      rw [second_stage_relation_eq_factor_kernel update fine coarse forget hfactor]
      rfl
  exact changeRelation.trans
    (Setoid.quotientQuotientEquivQuotient
      (Setoid.ker (completeItinerary update fine))
      (Setoid.ker (completeItinerary update coarse)) hle)

private theorem cascade_completion_equiv_projection {Y O P : Type*}
    (update : Y -> Y) (fine : Y -> O) (coarse : Y -> P)
    (forget : O -> P) (hfactor : coarse = forget ∘ fine)
    (state : CompletedState update fine) :
    cascadeCompletionEquiv update fine coarse forget hfactor
        (Quotient.mk'' state) =
      completionFactor update fine coarse forget hfactor state := by
  refine Quotient.inductionOn' state fun y => ?_
  rfl

/-- Fine completion followed by completion of the induced coarse readout is
the direct coarse completion, and the second projection is the canonical
fine-to-coarse factor map. -/
theorem cascade_completion {Y O P : Type*}
    (update : Y -> Y) (fine : Y -> O) (coarse : Y -> P)
    (forget : O -> P) (hfactor : coarse = forget ∘ fine) :
    (∀ y y',
      secondStageRelation update fine forget
          (completionProjection update fine y)
          (completionProjection update fine y') ↔
        Setoid.ker (completeItinerary update coarse) y y') ∧
      Function.Surjective
        (completionFactor update fine coarse forget hfactor) ∧
      secondStageRelation update fine forget =
        Setoid.ker (completionFactor update fine coarse forget hfactor) ∧
      ∃ equivalence :
          Quotient (secondStageRelation update fine forget) ≃
            CompletedState update coarse,
        (∀ state,
          equivalence (Quotient.mk'' state) =
            completionFactor update fine coarse forget hfactor state) ∧
        ∀ y,
          equivalence
              (Quotient.mk'' (completionProjection update fine y)) =
            completionProjection update coarse y := by
  refine ⟨second_stage_relation_projection update fine coarse forget hfactor,
    completion_factor_surjective update fine coarse forget hfactor,
    second_stage_relation_eq_factor_kernel update fine coarse forget hfactor,
    cascadeCompletionEquiv update fine coarse forget hfactor, ?_, ?_⟩
  · exact cascade_completion_equiv_projection
      update fine coarse forget hfactor
  · intro y
    rw [cascade_completion_equiv_projection]
    exact completion_factor_projection update fine coarse forget hfactor y

#print axioms cascade_completion

end D5.S3.ObserverMemory.Refinement.CascadeCompletion
