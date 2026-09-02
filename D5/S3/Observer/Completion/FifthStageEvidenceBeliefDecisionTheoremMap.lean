/- GID: D5/S3/Observer/Completion/FifthStageEvidenceBeliefDecisionTheoremMap
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/FifthStageEvidenceBeliefDecisionTheoremMap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed fifth-stage evidence, belief, risk, optimality, and adaptive cost map. -/

import D5.S3.ConceptDynamics.ExperimentDesign.ThreeStateAdaptiveEarlyStopping
import D5.S3.Estimation.DataProcessing.AdaptivePosteriorPolicySufficiency
import D5.S3.Estimation.DecisionRisk.PosteriorStoppingMapErrorBound
import D5.S3.Observer.DynamicProgramming.StationaryPolicyOptimality
import D5.S3.Observer.MeasureSeparation.EpsilonStoppingPairEvidenceCompletion

/- Library-search audit trail (2026-09-02):
   * Keyword, spelling-variant, theorem-shape, formalization-receipt, digest,
     generalized-owner, and every in-flight `origin/lane/math/*` search found
     no theorem packaging the fifth-stage evidence/belief/decision map.
   * Exact repository owners are applied directly: `open_loop_finite_state_completion`,
     `posterior_adaptive_policy_universal_sufficiency`,
     `posterior_stopping_map_error_bound`,
     `discounted_bellman_contraction_and_unique_fixed_point`,
     `bellman_greedy_stationary_policy_is_optimal`, and
     `three_state_adaptive_early_stopping_strict_advantage`.
   * Their pinned-Mathlib backbone includes `exists_subordinate_pairwise_disjoint`,
     `PMF.tsum_coe`, `ENNReal.tsum_le_tsum`, finite `Finset` extrema, and
     `ContractingWith.fixedPoint_unique`; no exact Mathlib synthesis theorem exists.
   * The source's "common fixed point" is not asserted literally. The available
     evidence theorem is open-loop and assumes an explicit Kakutani bridge, the
     Bellman theorem is for a finite ordinary MDP, and the adaptive cost theorem
     is a separate three-state construction. The last conjunct imports the
     counterexample showing that the abstract evidence bridge cannot be dropped. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Completion.FifthStageEvidenceBeliefDecisionTheoremMap

open D5.S3.ConceptDynamics.ExperimentDesign.ThreeStateAdaptiveEarlyStopping
open D5.S3.Estimation.DataProcessing.AdaptivePosteriorPolicySufficiency
open D5.S3.Estimation.DecisionRisk.PosteriorStoppingMapErrorBound
open D5.S3.Observer.DynamicProgramming.DiscountedBellmanContraction
open D5.S3.Observer.DynamicProgramming.StationaryPolicyOptimality
open D5.S3.Observer.MeasureSeparation.EpsilonStoppingPairEvidenceCompletion
open MeasureTheory
open scoped BigOperators BoundedContinuousFunction ENNReal

/-- The rigorously typed fifth-stage completion map. Divergent open-loop pair
evidence gives singular transcript laws and a zero-error classifier only under
the named evidence dichotomy. Equal current posteriors determine every finite
belief-adaptive future law and continuation value. Stopping in a posterior
threshold region controls MAP error. A finite discounted MDP has a contractive
Bellman operator with a unique fixed value, and a globally greedy stationary
policy realizes it. Finally, an explicit adaptive decision tree preserves exact
identification while strictly reducing expected observation cost.

This is a conjunction of compatible typed interfaces, not a claim that the
repository already contains one closed-loop Kakutani/posterior/MDP theorem. -/
theorem fifth_stage_evidence_belief_decision_theorem_map
    {EvidenceState Experiment Output Transcript : Type*} [Finite EvidenceState]
    [MeasurableSpace Output] [MeasurableSpace Transcript]
    (affinity : MeasureAffinity Output)
    (evidenceKernel : Experiment -> EvidenceState -> Measure Output)
    (experiment : Nat -> Experiment)
    (transcriptLaw : EvidenceState -> Measure Transcript)
    (localEquivalent : OpenLoopLocallyEquivalent evidenceKernel experiment)
    (evidenceDiverges : forall x y, x ≠ y ->
      openLoopPairEvidence affinity evidenceKernel experiment x y = ⊤)
    (evidenceDichotomy :
      OpenLoopEvidenceDichotomy affinity evidenceKernel experiment transcriptLaw)
    {Theta History AdaptiveExperiment Observation FutureAction : Type*}
    [Fintype Theta]
    (joint : Theta -> History -> NNReal)
    (extend : History -> AdaptiveExperiment -> Observation -> History)
    (adaptiveKernel : AdaptiveExperiment -> Theta -> PMF Observation)
    (bayesConditioned : forall history adaptiveExperiment observation,
      D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency.posterior joint
          (extend history adaptiveExperiment observation) =
        D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency.posteriorUpdate
          (fun theta output =>
            (adaptiveKernel adaptiveExperiment theta output).toNNReal)
          (D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency.posterior
            joint history)
          observation)
    {history history' : History}
    (equalPosterior :
      D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency.posterior
          joint history =
        D5.S3.Estimation.DecisionRisk.PosteriorUniversalSufficiency.posterior
          joint history')
    (futurePolicy : Nat -> (Theta -> NNReal) -> AdaptiveExperiment)
    (futureLoss : Theta -> FutureAction -> ENNReal) (horizon : Nat)
    {StoppedState StoppedHistory : Type*} [Finite StoppedState]
    [DecidableEq StoppedState]
    (stoppedHistoryLaw : PMF StoppedHistory)
    (posteriorAtStop : StoppedHistory -> PMF StoppedState)
    (estimate : StoppedHistory -> StoppedState) (stoppingEpsilon : ENNReal)
    (mapOutput : forall stoppedHistory state,
      posteriorAtStop stoppedHistory state <=
        posteriorAtStop stoppedHistory (estimate stoppedHistory))
    (stopped : forall stoppedHistory, exists mapState,
      (forall state,
        posteriorAtStop stoppedHistory state <=
          posteriorAtStop stoppedHistory mapState) /\
        1 - posteriorAtStop stoppedHistory mapState <= stoppingEpsilon)
    {ControlState ControlAction : Type*}
    [Fintype ControlState] [Nonempty ControlState]
    [TopologicalSpace ControlState] [DiscreteTopology ControlState]
    [Fintype ControlAction] [Nonempty ControlAction]
    (reward loss : ControlState -> ControlAction -> Real)
    (transition : ControlState -> ControlAction -> ControlState -> Real)
    (gamma : NNReal) (gammaPositive : 0 < gamma) (gammaBelowOne : gamma < 1)
    (stochastic : IsStochasticTransition transition)
    (stationaryPolicy : StationaryPolicy ControlState ControlAction)
    (optimalValue policyValue : ControlState →ᵇ Real)
    (optimalFixed : Function.IsFixedPt
      (discountedLossBellmanOperator loss transition gamma) optimalValue)
    (policyFixed : Function.IsFixedPt
      (stationaryPolicyBellmanOperator loss transition gamma stationaryPolicy)
      policyValue)
    (greedy : IsBellmanGreedy loss transition gamma stationaryPolicy optimalValue)
    (activeEpsilon : Real) (activeEpsilonPositive : 0 < activeEpsilon)
    (activeEpsilonUpper : activeEpsilon < 1 / 2) :
    ((Pairwise fun x y => transcriptLaw x ⟂ₘ transcriptLaw y) /\
        HasCommonZeroErrorClassifier transcriptLaw) /\
      (adaptiveFutureOutputLaw joint extend adaptiveKernel futurePolicy horizon history =
          adaptiveFutureOutputLaw joint extend adaptiveKernel futurePolicy horizon history' /\
        adaptiveContinuationValue joint extend adaptiveKernel futurePolicy futureLoss
            horizon history =
          adaptiveContinuationValue joint extend adaptiveKernel futurePolicy futureLoss
            horizon history') /\
      ((∑' stoppedHistory, stoppedHistoryLaw stoppedHistory *
        ∑' state,
          if estimate stoppedHistory = state then 0
          else posteriorAtStop stoppedHistory state) <= stoppingEpsilon) /\
      ((forall value other : ControlState →ᵇ Real,
          norm (discountedBellmanOperator reward transition gamma value -
              discountedBellmanOperator reward transition gamma other) <=
            (gamma : Real) * norm (value - other)) /\
        ∃! value : ControlState →ᵇ Real,
          Function.IsFixedPt
            (discountedBellmanOperator reward transition gamma) value) /\
      IsOptimalStationaryPolicy stationaryPolicy policyValue optimalValue /\
      (let State := Option Bool
       let priorMass : State -> Real := fun state =>
         match state with
         | none => 1 - 2 * activeEpsilon
         | some _ => activeEpsilon
       let firstReadout : State -> Bool := Option.isNone
       let secondReadout : State -> Bool := fun state =>
         match state with
         | some true => true
         | _ => false
       let staticTranscript : State -> List Bool := fun state =>
         [firstReadout state, secondReadout state]
       let adaptiveTranscript : State -> List Bool := fun state =>
         if firstReadout state then [true] else [false, secondReadout state]
       ((forall state : State, 0 <= priorMass state) /\
           ∑ state : State, priorMass state = 1) /\
         Function.Injective staticTranscript /\
         Function.Injective adaptiveTranscript /\
         ((forall state : State, (adaptiveTranscript state).length <= 2) /\
           exists state : State, (adaptiveTranscript state).length = 2) /\
         (∑ state : State,
           priorMass state * (staticTranscript state).length = 2) /\
         (∑ state : State,
           priorMass state * (adaptiveTranscript state).length =
             1 + 2 * activeEpsilon) /\
         (∑ state : State,
           priorMass state * (adaptiveTranscript state).length) <
           ∑ state : State,
             priorMass state * (staticTranscript state).length) /\
      (∃ (badAffinity : MeasureAffinity Unit)
          (badKernel : Unit -> Bool -> Measure Unit)
          (badExperiment : Nat -> Unit)
          (badTranscriptLaw : Bool -> Measure Unit),
        OpenLoopLocallyEquivalent badKernel badExperiment /\
          (forall x y, x ≠ y ->
            openLoopPairEvidence badAffinity badKernel badExperiment x y = ⊤) /\
          ¬Pairwise fun x y =>
            badTranscriptLaw x ⟂ₘ badTranscriptLaw y) := by
  have evidenceCompletion :=
    open_loop_finite_state_completion affinity evidenceKernel experiment transcriptLaw
      localEquivalent evidenceDiverges evidenceDichotomy
  have beliefCompletion :=
    posterior_adaptive_policy_universal_sufficiency joint extend adaptiveKernel
      bayesConditioned equalPosterior futurePolicy FutureAction futureLoss horizon
  have stoppingCompletion :=
    posterior_stopping_map_error_bound stoppedHistoryLaw posteriorAtStop estimate
      stoppingEpsilon mapOutput stopped
  have bellmanCompletion :=
    discounted_bellman_contraction_and_unique_fixed_point reward transition gamma
      gammaPositive gammaBelowOne stochastic.1 stochastic.2
  have policyCompletion :=
    bellman_greedy_stationary_policy_is_optimal loss transition gamma gammaBelowOne
      stochastic stationaryPolicy optimalValue policyValue optimalFixed policyFixed greedy
  have activeCompletion :=
    three_state_adaptive_early_stopping_strict_advantage activeEpsilon
      activeEpsilonPositive activeEpsilonUpper
  exact ⟨evidenceCompletion, beliefCompletion, stoppingCompletion,
    bellmanCompletion, policyCompletion, activeCompletion,
    evidence_dichotomy_is_necessary⟩

#print axioms fifth_stage_evidence_belief_decision_theorem_map

end D5.S3.Observer.Completion.FifthStageEvidenceBeliefDecisionTheoremMap
