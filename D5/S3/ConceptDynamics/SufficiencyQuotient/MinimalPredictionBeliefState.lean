/- GID: D5/S3/ConceptDynamics/SufficiencyQuotient/MinimalPredictionBeliefState
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SufficiencyQuotient/MinimalPredictionBeliefState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every sufficient history summary uniquely covers the predictive belief quotient. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.ObserverMemory.PredictionFactors.CausalStateFactorization
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-25):
   * Exact repository primitive `jointReadout` is the canonical dependent product
     of all action-indexed future-observation readouts; it is imported rather than
     redeclared as another profile function.
   * The closest family theorem `causal_state_factorization` uniquely factors a
     sufficient interface onto the realized future-law image. It is applied below,
     then the exact Mathlib equivalence `Setoid.quotientKerEquivRange` exposes the
     source's canonical kernel quotient rather than replacing it by an image type.
   * `GlobalProfileQuotientUniversality` is adjacent but requires nonempty histories,
     extends factors to unrealized summary values, and does not publicly quantify all
     empirical objectives based on the observation profile, so it is not an exact hit.
   * Repository and pinned-Mathlib searches found no theorem packaging the canonical
     quotient, objective invariance, unique realized-summary factor, and its
     surjectivity with no nonemptiness restriction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.SufficiencyQuotient.MinimalPredictionBeliefState

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ObserverMemory.PredictionFactors.CausalStateFactorization

universe u v w z

/-- If every action-indexed future-observation possibility is predicted from a
history summary, equal summary values determine the same predictive-belief class
and every empirical objective of that profile. The canonical kernel quotient is
the unique surjective image of the realized summary state. -/
theorem minimal_prediction_belief_state
    {History : Type u} {Query : Type v} {Summary : Type w}
    {Observation : Query -> Type z}
    (possibleObservation : (query : Query) -> History -> Observation query)
    (summary : History -> Summary)
    (predictor : Summary -> ((query : Query) -> Observation query))
    (sufficient : jointReadout possibleObservation = predictor ∘ summary) :
    (∀ history history', summary history = summary history' ->
      Quotient.mk (Setoid.ker (jointReadout possibleObservation)) history =
          Quotient.mk (Setoid.ker (jointReadout possibleObservation)) history' ∧
        ∀ {Objective : Type*}
          (empiricalObjective : ((query : Query) -> Observation query) -> Objective),
          empiricalObjective (jointReadout possibleObservation history) =
            empiricalObjective (jointReadout possibleObservation history')) ∧
      ∃! factor : Set.range summary ->
          Quotient (Setoid.ker (jointReadout possibleObservation)),
        (fun history =>
          Quotient.mk (Setoid.ker (jointReadout possibleObservation)) history) =
            factor ∘ Set.rangeFactorization summary ∧
          Function.Surjective factor := by
  let profile := jointReadout possibleObservation
  have imageResult := causal_state_factorization summary profile predictor sufficient
  rcases imageResult with
    ⟨⟨imageFactor, ⟨imageFactorization, _factorMatches⟩, _imageUnique⟩,
      _separates⟩
  have sameProfile : ∀ history history', summary history = summary history' ->
      profile history = profile history' := by
    intro history history' sameSummary
    change jointReadout possibleObservation history =
      jointReadout possibleObservation history'
    rw [sufficient]
    exact congrArg predictor sameSummary
  constructor
  · intro history history' sameSummary
    have profileEqual := sameProfile history history' sameSummary
    constructor
    · exact Quotient.sound profileEqual
    · intro Objective empiricalObjective
      exact congrArg empiricalObjective profileEqual
  · let quotientEquiv : Quotient (Setoid.ker profile) ≃ Set.range profile :=
      Setoid.quotientKerEquivRange profile
    let factor : Set.range summary -> Quotient (Setoid.ker profile) :=
      quotientEquiv.symm ∘ imageFactor
    have factorization :
        (fun history => Quotient.mk (Setoid.ker profile) history) =
          factor ∘ Set.rangeFactorization summary := by
      funext history
      apply quotientEquiv.injective
      change Set.rangeFactorization profile history =
        quotientEquiv (factor (Set.rangeFactorization summary history))
      rw [show quotientEquiv (factor (Set.rangeFactorization summary history)) =
          imageFactor (Set.rangeFactorization summary history) by
        exact quotientEquiv.apply_symm_apply _]
      exact congrFun imageFactorization history
    have factorSurjective : Function.Surjective factor := by
      intro belief
      induction belief using Quotient.inductionOn with
      | _ history =>
          refine ⟨Set.rangeFactorization summary history, ?_⟩
          exact (congrFun factorization history).symm
    refine ⟨factor, ⟨factorization, factorSurjective⟩, ?_⟩
    intro candidate candidateProperty
    apply Set.rangeFactorization_surjective.injective_comp_right
    exact candidateProperty.1.symm.trans factorization

#print axioms minimal_prediction_belief_state

end D5.S3.ConceptDynamics.SufficiencyQuotient.MinimalPredictionBeliefState
