/- GID: D5/S0/History/Consensus/InlineConsensusProtocolFixtures
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusProtocolFixtures
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quantified router transitions consume the observation that selected their exit. -/
import D5.S0.History.Consensus.InlineConsensusExecution

namespace D5.S0.History.Consensus.InlineConsensusProtocolFixtures

open InlineConsensusOptimality

structure DesignRouterReady (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState)
    (situation : DesignSituation) : Prop where
  dispatchShape : model.dispatchShape config.dispatchPlan
  wellFormed : StateWellFormed state
  budgetAuthorized : PassBudgetAuthorized config
  live : state.phase = .live
  isolated : state.isolation = .available
  atMeta : state.stage = .metaJudge
  recorded : state.designSituation = some situation
  withinBudget : state.passesUsed < config.sharedPassBudget

structure ReviewRouterReady (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState)
    (results : ReviewResults) : Prop where
  dispatchShape : model.dispatchShape config.dispatchPlan
  wellFormed : StateWellFormed state
  budgetAuthorized : PassBudgetAuthorized config
  live : state.phase = .live
  isolated : state.isolation = .available
  atReview : state.stage = .reviewTripletWorkers
  authorized : results.DispatchAuthorized model config state
  attemptsFresh : Disjoint (results.attemptKeys state) state.attemptedFlights

structure TerminationRouterReady (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState)
    (observation : TerminationObservation) : Prop where
  dispatchShape : model.dispatchShape config.dispatchPlan
  wellFormed : StateWellFormed state
  budgetAuthorized : PassBudgetAuthorized config
  live : state.phase = .live
  isolated : state.isolation = .available
  atEnd : state.stage = .fixOrDone
  reviewDone : state.reviewExit = some .done
  reviewCurrent : state.reviewEpoch = some state.artifactEpoch
  noPermit : state.terminationExit ≠ some .permitClaim
  authorized : observation.DispatchAuthorized model config state
  attemptsFresh : Disjoint (observation.attemptKeys state) state.attemptedFlights
  withinBudget : state.passesUsed < config.sharedPassBudget

def RouterTransitionsExhaustive (model : InlineConsensusModel) : Prop :=
  (forall config state situation, DesignRouterReady model config state situation ->
    Nonempty (DesignRouteTransition model config state situation)) /\
  (forall config state results, ReviewRouterReady model config state results ->
    Nonempty (ReviewRouteTransition model config state results)) /\
  (forall config state observation, TerminationRouterReady model config state observation ->
    Nonempty (TerminationRouteTransition model config state observation))

theorem router_transitions_are_exhaustive :
    RouterTransitionsExhaustive inlineConsensusModel := by
  refine ⟨?_, ?_, ?_⟩
  · intro config state situation ready
    cases situation with
    | unanimousActionable =>
        let condition : AdvanceCondition inlineConsensusModel config state :=
          .metaJudge ready.atMeta .unanimousActionable ready.recorded rfl
        let action : ProtocolAction inlineConsensusModel config state
            (.advance state.stage .implementationWorker condition.attemptKeys)
            (condition.nextState .implementationWorker) :=
          .advance state .implementationWorker ready.budgetAuthorized ready.live ready.isolated
            condition (by simp [AdvanceCondition.attemptKeys])
            (by change Stage.Successor state.stage .implementationWorker
                simp [ready.atMeta, Stage.Successor, Stage.next])
        exact ⟨{
          recorded := ready.recorded
          final := recordEvent state (condition.nextState .implementationWorker)
          step := by
            change ProtocolStep inlineConsensusModel config state
              (designEvent inlineConsensusModel .unanimousActionable) _
            simpa [ready.atMeta, designEvent, inlineConsensusModel, designRouter,
              AdvanceCondition.attemptKeys] using
              ProtocolStep.ofAction ready.dispatchShape ready.wellFormed action }⟩
    | compatiblePlans =>
        let action : ProtocolAction inlineConsensusModel config state
            (.boundedPass state.stage .metaLayerConvergence {})
            { state with
              passesUsed := state.passesUsed + 1
              designSituation := some .unanimousActionable } :=
          .designConvergence state ready.budgetAuthorized ready.live ready.isolated
            ready.atMeta ready.recorded ready.withinBudget
        exact ⟨{
          recorded := ready.recorded
          final := recordEvent state _
          step := by
            change ProtocolStep inlineConsensusModel config state
              (designEvent inlineConsensusModel .compatiblePlans) _
            simpa [ready.atMeta, designEvent, inlineConsensusModel, designRouter] using
              ProtocolStep.ofAction ready.dispatchShape ready.wellFormed action }⟩
    | boundedStall =>
        let action : ProtocolAction inlineConsensusModel config state (.abstain state.stage)
            { state with phase := .abstained } :=
          .abstain state ready.budgetAuthorized ready.live
            (.designStall ready.atMeta ready.recorded)
        exact ⟨{
          recorded := ready.recorded
          final := recordEvent state _
          step := by
            change ProtocolStep inlineConsensusModel config state
              (designEvent inlineConsensusModel .boundedStall) _
            simpa [ready.atMeta, designEvent, inlineConsensusModel, designRouter] using
              ProtocolStep.ofAction ready.dispatchShape ready.wellFormed action }⟩
    | singlePerspective =>
        let action : ProtocolAction inlineConsensusModel config state (.abstain state.stage)
            { state with phase := .abstained } :=
          .abstain state ready.budgetAuthorized ready.live
            (.designFakeConsensus ready.atMeta ready.recorded)
        exact ⟨{
          recorded := ready.recorded
          final := recordEvent state _
          step := by
            change ProtocolStep inlineConsensusModel config state
              (designEvent inlineConsensusModel .singlePerspective) _
            simpa [ready.atMeta, designEvent, inlineConsensusModel, designRouter] using
              ProtocolStep.ofAction ready.dispatchShape ready.wellFormed action }⟩
  · intro config state results ready
    let condition : AdvanceCondition inlineConsensusModel config state :=
      .review ready.atReview results ready.authorized
    let action : ProtocolAction inlineConsensusModel config state
        (.advance state.stage .fixOrDone condition.attemptKeys)
        (condition.nextState .fixOrDone) :=
      .advance state .fixOrDone ready.budgetAuthorized ready.live ready.isolated
        condition ready.attemptsFresh
        (by change Stage.Successor state.stage .fixOrDone
            simp [ready.atReview, Stage.Successor, Stage.next])
    exact ⟨{
      final := recordEvent state (condition.nextState .fixOrDone)
      step := by
        change ProtocolStep inlineConsensusModel config state
          (.advance .reviewTripletWorkers .fixOrDone (results.attemptKeys state)) _
        simpa [ready.atReview, AdvanceCondition.attemptKeys] using
          ProtocolStep.ofAction ready.dispatchShape ready.wellFormed action
      routed := by rfl }⟩
  · intro config state observation ready
    let action : ProtocolAction inlineConsensusModel config state
        (.boundedPass state.stage .terminationGate (observation.attemptKeys state))
        (terminationNextState inlineConsensusModel state observation .engineering) :=
      .terminationGate state ready.budgetAuthorized ready.live ready.isolated ready.atEnd
        ready.reviewDone ready.reviewCurrent ready.noPermit observation ready.authorized
        ready.attemptsFresh .engineering ready.withinBudget
    refine ⟨{
      final := recordEvent state
        (terminationNextState inlineConsensusModel state observation .engineering)
      step := by
        change ProtocolStep inlineConsensusModel config state
          (.boundedPass .fixOrDone .terminationGate (observation.attemptKeys state)) _
        simpa [ready.atEnd] using
          ProtocolStep.ofAction ready.dispatchShape ready.wellFormed action
      routed := ?_ }⟩
    cases routed : inlineConsensusModel.terminationRoute observation <;>
      simp [recordEvent, terminationNextState, routed, terminationExitAfterEvent,
        carriedPermit, ready.noPermit]

end D5.S0.History.Consensus.InlineConsensusProtocolFixtures
