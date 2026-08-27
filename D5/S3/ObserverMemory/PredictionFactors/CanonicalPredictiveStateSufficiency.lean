/- GID: D5/S3/ObserverMemory/PredictionFactors/CanonicalPredictiveStateSufficiency
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/CanonicalPredictiveStateSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical future-law state makes past and future conditionally independent. -/

import D5.S3.Entropy.Submodularity.MarkovDataProcessing
import Mathlib.Probability.ProbabilityMassFunction.Basic

/- Library-search audit trail (2026-08-28):
   * Exact family hits `CausalStateFactorization.causal_state_factorization` and
     `ConditionalProbabilityProfileMinimality.conditional_probability_profile_is_minimal`
     establish `Set.rangeFactorization futureLaw` as the canonical predictive-state map.
   * Exact supporting hit `MarkovDataProcessing.markov_of_channel` proves the finite Markov
     cross-product identity for a channel-generated law and is applied directly below.
   * `PredictionClosureCriterion.prediction_closure_iff_markov` characterizes the corresponding
     conditional factorization but does not construct the canonical predictive state.
   * Pinned Mathlib supplies `PMF`, `PMF.tsum_coe`, and `ENNReal.toReal_sum`; no complete theorem
     constructs the predictive state and proves its sufficiency on this finite carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionFactors.CanonicalPredictiveStateSufficiency

open D5.S3.Entropy.Submodularity.MarkovDataProcessing
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.Submodularity.StrongSubadditivity

open scoped Classical in
/-- Mapping each past to its complete conditional future law produces the canonical predictive
state. In the joint law induced by the prior and future channel, the complete past and future
satisfy the finite conditional-independence cross-product identity given that state. -/
theorem canonical_predictive_state_is_sufficient
    {Past Future : Type*} [Fintype Past] [Fintype Future]
    (prior : PMF Past) (futureLaw : Past -> PMF Future) :
    let stateOf : Past -> Set.range futureLaw :=
      Set.rangeFactorization futureLaw
    let jointLaw : Past × (Set.range futureLaw × Future) -> Real := fun q =>
      if stateOf q.1 = q.2.1 then
        (prior q.1).toReal * (futureLaw q.1 q.2.2).toReal
      else 0
    forall past state future,
      jointLaw (past, (state, future)) *
          marginal (yFirstLaw jointLaw) state =
        xyProjection jointLaw (past, state) *
          xzProjection (yFirstLaw jointLaw) (state, future) := by
  classical
  dsimp only
  let stateOf : Past -> Set.range futureLaw :=
    Set.rangeFactorization futureLaw
  let pastStateLaw : Past × Set.range futureLaw -> Real := fun q =>
    if stateOf q.1 = q.2 then (prior q.1).toReal else 0
  let stateKernel : Set.range futureLaw -> Future -> Real := fun state future =>
    (state.1 future).toReal
  have stateKernelSum : forall state, ∑ future, stateKernel state future = 1 := by
    intro state
    have pmfSum : (∑ future : Future, state.1 future) = 1 := by
      simpa using state.1.tsum_coe
    calc
      (∑ future : Future, stateKernel state future) =
          (∑ future : Future, state.1 future).toReal := by
        simp only [stateKernel]
        symm
        exact ENNReal.toReal_sum (fun future _ => PMF.apply_ne_top state.1 future)
      _ = 1 := by rw [pmfSum]; simp
  have markov := markov_of_channel pastStateLaw stateKernel stateKernelSum
  have jointLawFormula :
      (fun q : Past × (Set.range futureLaw × Future) =>
        if stateOf q.1 = q.2.1 then
          (prior q.1).toReal * (futureLaw q.1 q.2.2).toReal
        else 0) =
        (fun q : Past × (Set.range futureLaw × Future) =>
          pastStateLaw (q.1, q.2.1) * stateKernel q.2.1 q.2.2) := by
    funext q
    by_cases sameState : stateOf q.1 = q.2.1
    · have sameLaw : futureLaw q.1 = q.2.1.1 :=
        congrArg Subtype.val sameState
      simp [pastStateLaw, stateKernel, sameState, sameLaw]
    · simp [pastStateLaw, stateKernel, sameState]
  rw [← jointLawFormula] at markov
  exact markov

/- A deterministic Boolean future channel witnesses all public binders. -/
example :
    let stateOf : Bool -> Set.range (fun past : Bool => PMF.pure past) :=
      Set.rangeFactorization (fun past : Bool => PMF.pure past)
    let jointLaw :
        Bool × (Set.range (fun past : Bool => PMF.pure past) × Bool) -> Real := fun q =>
      if stateOf q.1 = q.2.1 then
        ((PMF.pure false) q.1).toReal * ((PMF.pure q.1) q.2.2).toReal
      else 0
    forall past state future,
      jointLaw (past, (state, future)) *
          marginal (yFirstLaw jointLaw) state =
        xyProjection jointLaw (past, state) *
          xzProjection (yFirstLaw jointLaw) (state, future) := by
  exact canonical_predictive_state_is_sufficient
    (PMF.pure false) (fun past : Bool => PMF.pure past)

example : Bool := false

#print axioms canonical_predictive_state_is_sufficient

end D5.S3.ObserverMemory.PredictionFactors.CanonicalPredictiveStateSufficiency
