/- GID: D5/S0/History/Consensus/InlineConsensusProtocolFixtures
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusProtocolFixtures
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quantified router transitions consume the observation that selected their exit. -/
import D5.S0.History.Consensus.InlineConsensusExecution

namespace D5.S0.History.Consensus.InlineConsensusProtocolFixtures

open InlineConsensusOptimality

structure DesignRouterReady (config : ProtocolConfig) (state : ProtocolState)
    (situation : DesignSituation) : Prop where
  wellFormed : StateWellFormed state
  budgetAuthorized : PassBudgetAuthorized config
  live : state.phase = .live
  isolated : state.isolation = .available
  atMeta : state.stage = .metaJudge
  recorded : state.designSituation = some situation
  withinBudget : state.passesUsed < config.sharedPassBudget

structure ReviewRouterReady (config : ProtocolConfig) (state : ProtocolState)
    (results : ReviewResults) : Prop where
  wellFormed : StateWellFormed state
  budgetAuthorized : PassBudgetAuthorized config
  live : state.phase = .live
  isolated : state.isolation = .available
  atReview : state.stage = .reviewTripletWorkers
  authorized : results.DispatchAuthorized config state

structure TerminationRouterReady (config : ProtocolConfig) (state : ProtocolState)
    (observation : TerminationObservation) : Prop where
  wellFormed : StateWellFormed state
  budgetAuthorized : PassBudgetAuthorized config
  live : state.phase = .live
  isolated : state.isolation = .available
  atEnd : state.stage = .fixOrDone
  reviewDone : state.reviewExit = some .done
  reviewCurrent : state.reviewEpoch = some state.artifactEpoch
  noPermit : state.terminationExit ≠ some .permitClaim
  authorized : observation.DispatchAuthorized config state
  withinBudget : state.passesUsed < config.sharedPassBudget

def RouterTransitionsExhaustive : Prop :=
  (forall config state situation, DesignRouterReady config state situation ->
    Nonempty (DesignRouteTransition config state situation)) /\
  (forall config state results, ReviewRouterReady config state results ->
    Nonempty (ReviewRouteTransition config state results)) /\
  (forall config state observation, TerminationRouterReady config state observation ->
    Nonempty (TerminationRouteTransition config state observation))

theorem router_transitions_are_exhaustive : RouterTransitionsExhaustive := by
  refine ⟨?_, ?_, ?_⟩
  · intro config state situation ready
    cases situation with
    | unanimousActionable =>
        let condition : AdvanceCondition config state :=
          .metaJudge ready.atMeta .unanimousActionable ready.recorded rfl
        let action : ProtocolAction config state
            (.advance state.stage .implementationWorker)
            (condition.nextState .implementationWorker) :=
          .advance state .implementationWorker ready.budgetAuthorized ready.live ready.isolated
            condition (by simp [ready.atMeta, Stage.Successor, Stage.next])
        exact ⟨{
          recorded := ready.recorded
          final := recordEvent state (condition.nextState .implementationWorker)
          step := by
            simpa [ready.atMeta, designEvent, designRouter] using
              ProtocolStep.ofAction ready.wellFormed action }⟩
    | compatiblePlans =>
        let action : ProtocolAction config state
            (.boundedPass state.stage .metaLayerConvergence)
            { state with
              passesUsed := state.passesUsed + 1
              designSituation := some .unanimousActionable } :=
          .designConvergence state ready.budgetAuthorized ready.live ready.isolated
            ready.atMeta ready.recorded ready.withinBudget
        exact ⟨{
          recorded := ready.recorded
          final := recordEvent state _
          step := by
            simpa [ready.atMeta, designEvent, designRouter] using
              ProtocolStep.ofAction ready.wellFormed action }⟩
    | boundedStall =>
        let action : ProtocolAction config state (.abstain state.stage)
            { state with phase := .abstained } :=
          .abstain state ready.budgetAuthorized ready.live
            (.designStall ready.atMeta ready.recorded)
        exact ⟨{
          recorded := ready.recorded
          final := recordEvent state _
          step := by
            simpa [ready.atMeta, designEvent, designRouter] using
              ProtocolStep.ofAction ready.wellFormed action }⟩
    | singlePerspective =>
        let action : ProtocolAction config state (.abstain state.stage)
            { state with phase := .abstained } :=
          .abstain state ready.budgetAuthorized ready.live
            (.designFakeConsensus ready.atMeta ready.recorded)
        exact ⟨{
          recorded := ready.recorded
          final := recordEvent state _
          step := by
            simpa [ready.atMeta, designEvent, designRouter] using
              ProtocolStep.ofAction ready.wellFormed action }⟩
  · intro config state results ready
    let condition : AdvanceCondition config state :=
      .review ready.atReview results ready.authorized
    let action : ProtocolAction config state
        (.advance state.stage .fixOrDone)
        (condition.nextState .fixOrDone) :=
      .advance state .fixOrDone ready.budgetAuthorized ready.live ready.isolated
        condition (by simp [ready.atReview, Stage.Successor, Stage.next])
    exact ⟨{
      final := recordEvent state (condition.nextState .fixOrDone)
      step := by
        simpa [ready.atReview] using ProtocolStep.ofAction ready.wellFormed action
      routed := by rfl }⟩
  · intro config state observation ready
    let action : ProtocolAction config state
        (.boundedPass state.stage .terminationGate)
        (terminationNextState state observation .engineering) :=
      .terminationGate state ready.budgetAuthorized ready.live ready.isolated ready.atEnd
        ready.reviewDone ready.reviewCurrent ready.noPermit observation ready.authorized
        .engineering ready.withinBudget
    refine ⟨{
      final := recordEvent state (terminationNextState state observation .engineering)
      step := by
        simpa [ready.atEnd] using ProtocolStep.ofAction ready.wellFormed action
      routed := ?_ }⟩
    cases routed : terminationRouter observation <;>
      simp [recordEvent, terminationNextState, routed]

end D5.S0.History.Consensus.InlineConsensusProtocolFixtures
