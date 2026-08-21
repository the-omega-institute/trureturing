/- GID: D5/S0/History/Consensus/InlineConsensusProtocolPins
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusProtocolPins
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One total theorem admits every load-bearing inline-consensus clause. -/
import D5.S0.History.Consensus.InlineConsensusProtocolFixtures

namespace D5.S0.History.Consensus.InlineConsensusProtocolFixtures

open InlineConsensusOptimality

def protocolThinkingDispatch : ThinkingSeat -> Carrier
  | .teleology => .isolatedTokenSubagent
  | .parsimony => .nyxidOracle
  | .fidelity | .naturalOwnership | .proportionalContainment | .worth => .codexCli

def protocolReviewDispatch : ReviewSeat -> Carrier
  | .architecture => .isolatedTokenSubagent
  | .quality => .nyxidOracle
  | .tests => .codexCli

def protocolTerminationDispatch : TerminationSeat -> Carrier
  | .criterionEvidence => .isolatedTokenSubagent
  | .residualGap => .nyxidOracle
  | .claimIntegrity => .codexCli

def protocolDispatchPlan : DispatchPlan :=
  { thinking := protocolThinkingDispatch
    review := protocolReviewDispatch
    termination := protocolTerminationDispatch
    thinkingLayout := by decide
    reviewLayout := by decide
    terminationLayout := by decide }

def allCodexThinkingDispatch : ThinkingSeat -> Carrier := fun _ => .codexCli

def protocolGoalArtifact : GoalArtifact :=
  { rawUserInput := true
    normalizedGoal := true
    constraints := true
    successCriteria := true
    iterationQuestion := true
    harness := true
    revisions := true }

def SuccessfulFixConsumesImplementationCarrier : Prop :=
  forall config state raw,
    ProtocolAction config state (.boundedPass state.stage .fixPass) raw ->
      exists carrier,
        flightKey state.stage .implementation carrier ∈ raw.attemptedFlights

def ImplementationAdvancePreservesPermitPayload : Prop :=
  forall config state target (atStage : state.stage = .implementationWorker)
      (result : WorkerReport Unit)
      (authorized : AuthorizedReport config state .implementation result),
    let condition : AdvanceCondition config state := .implementation atStage result authorized
    (condition.nextState target).terminationExit = state.terminationExit /\
      (condition.nextState target).terminationEpoch = state.terminationEpoch

inductive ClauseId
  | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10
  deriving DecidableEq, Fintype, Repr

def ClauseObject : ClauseId -> Prop
  | .s1 =>
      Stage.next .intake = some .chooseWorkerMode /\
      Stage.next .chooseWorkerMode = some .thinkingPanelWorkers /\
      Stage.next .thinkingPanelWorkers = some .metaJudge /\
      Stage.next .metaJudge = some .implementationWorker /\
      Stage.next .implementationWorker = some .reviewTripletWorkers /\
      Stage.next .reviewTripletWorkers = some .fixOrDone /\
      Stage.next .fixOrDone = none
  | .s2 =>
      (Carrier.priorityRank .codexCli = 0 /\ Carrier.priorityRank .nyxidOracle = 1 /\
        Carrier.priorityRank .isolatedTokenSubagent = 2 /\
        Carrier.priorityRank .abstain = 3) /\
      MultiSeatLayout protocolThinkingDispatch /\
      MultiSeatLayout protocolReviewDispatch /\
      MultiSeatLayout protocolTerminationDispatch /\
      Not (MultiSeatLayout allCodexThinkingDispatch) /\
      (forall config state role carrier, FallbackAssigned config state role carrier ->
        (triedAt state state.stage role).Nonempty /\
        selectCarrier (config.eligible state.stage role)
          (triedAt state state.stage role) = carrier) /\
      SuccessfulFixConsumesImplementationCarrier
  | .s3 =>
      (forall config state final role carrier attempts,
        ProtocolStep config state (.flightFailure state.stage role carrier attempts) final ->
          0 < attempts /\ attempts = config.retryBudget state.stage role carrier) /\
      (forall config state role carrier, FallbackAssigned config state role carrier ->
        exists failedCarrier,
          flightKey state.stage role failedCarrier ∈ state.exhaustedFlights) /\
      (forall config start events final,
        Execution inlineConsensusModel config start events final ->
          WithinRetryBudgets config events)
  | .s4 =>
      (forall exited artifact envelope verdict sentinel,
        Complete .codexCli (.codex exited artifact envelope verdict sentinel) <->
          exited = true /\ artifact = true /\ envelope = true /\ verdict = true /\
            sentinel = true) /\
      (forall terminal envelope verdict,
        Complete .nyxidOracle (.nyxid terminal envelope verdict) <->
          terminal = true /\ envelope = true /\ verdict = true) /\
      (forall envelope verdict,
        Complete .isolatedTokenSubagent (.subagent envelope verdict) <->
          envelope = true /\ verdict = true) /\
      (forall proxy carrier, carrier ≠ .abstain ->
        Not (Complete carrier (evidenceFromProxyOnly carrier proxy)))
  | .s5 =>
      (forall config state final event, state.phase = .abstained ->
        Not (ProtocolStep config state event final))
  | .s6 =>
      (forall config state role (Verdict : Type) (report : WorkerReport Verdict),
        AuthorizedReport config state role report ->
          report.view.IsolatedComplete config.goalArtifact) /\
      (forall config state final event, state.isolation = .unavailable ->
        ProtocolStep config state event final -> exists stage, event = .abstain stage) /\
      GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
        (⟨protocolGoalArtifact, Finset.univ⟩ : GoalArtifactSnapshot) /\
      Not (GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
        (⟨protocolGoalArtifact, {}⟩ : GoalArtifactSnapshot))
  | .s7 =>
      (priorExposure .codexCli = .repoPriorExposed /\
        priorExposure .nyxidOracle = .externalPriorExposed /\
        priorExposure .isolatedTokenSubagent = .callerPriorExposed /\
        priorExposure .abstain = .noCarrier) /\
      priorExposure .codexCli ≠ priorExposure .nyxidOracle /\
      forall latent, correlatedConclusion .codexCli latent =
        correlatedConclusion .nyxidOracle latent
  | .s8 =>
      RouterTransitionsExhaustive /\
      (forall observation, (exists index, observation index = .reject) ->
        reviewRouter observation = .fix) /\
      (forall observation, Not (ExactRoster observation.roster) ->
        terminationRouter observation = .rejectFakeConsensus) /\
      (forall observation, ExactRoster observation.roster ->
        (exists seat, (observation.result seat).isUnsatisfiedBool = true) ->
        terminationRouter observation = .continueAgainstGap) /\
      (forall config start final event,
        start.terminationExit = some .permitClaim ->
        ProtocolStep config start event final -> Not (FinishPrecondition final)) /\
      NoStaleTerminationPermitAfterFix /\
      ImplementationAdvancePreservesPermitPayload
  | .s9 =>
      Fintype.card TerminationSeat = 3 /\
      Sound optimalTerminationRule /\
      (forall rule, Sound rule -> RuleLE rule optimalTerminationRule) /\
      (forall rule, Greatest rule -> rule = optimalTerminationRule) /\
      (forall observation, terminationRouter observation ≠ .permitClaim ->
        optimalTerminationRule observation = false)
  | .s10 =>
      defaultSharedPassBudget = 5 /\
      BoundedPassKind.LegalAt .metaLayerConvergence .metaJudge /\
      BoundedPassKind.LegalAt .repeatedReview .fixOrDone /\
      BoundedPassKind.LegalAt .fixPass .fixOrDone /\
      BoundedPassKind.LegalAt .terminationGate .fixOrDone /\
      forall config (run : MaximalRun inlineConsensusModel config),
        sharedPassCount run.events <= config.sharedPassBudget /\
        run.events.length <= explicitRunBound config

def RequiredFixtureSuite : Prop := forall clause, ClauseObject clause

theorem required_fixture_suite_is_pinned : RequiredFixtureSuite := by
  have legal_preassigned_layout :
      MultiSeatLayout protocolThinkingDispatch /\
      MultiSeatLayout protocolReviewDispatch /\
      MultiSeatLayout protocolTerminationDispatch := by decide
  have illegal_all_codex_layout_is_rejected :
      Not (MultiSeatLayout allCodexThinkingDispatch) := by decide
  have successful_fix_consumes_implementation_carrier :
      SuccessfulFixConsumesImplementationCarrier := by
    intro config state raw action
    cases action with
    | fixAndReview budget live isolated atEnd needsFix implementation implementationAuthorized
        results reviewAuthorized withinBudget =>
        exact ⟨implementation.carrier, by simp⟩
  have design_and_review_router_exits_have_executable_transitions :
      RouterTransitionsExhaustive := router_transitions_are_exhaustive
  have implementation_branch_preserves_permit_payload :
      ImplementationAdvancePreservesPermitPayload := by
    intro config state target atStage result authorized
    exact ⟨rfl, rfl⟩
  intro clause
  cases clause with
  | s1 => exact stage_order_is_the_protocol_order
  | s2 =>
      exact ⟨carrier_priority_is_the_protocol_priority,
        legal_preassigned_layout.1, legal_preassigned_layout.2.1,
        legal_preassigned_layout.2.2, illegal_all_codex_layout_is_rejected,
        (fun _ _ _ _ fallback => fallback_selection_requires_a_tried_origin fallback),
        successful_fix_consumes_implementation_carrier⟩
  | s3 =>
      exact ⟨fun _ _ _ _ _ _ step =>
        flight_failure_occurs_only_after_precommitted_budget_exhaustion step,
        fun _ _ _ _ fallback => fallback_selection_requires_exhausted_origin fallback,
        fun _ _ _ _ execution =>
          every_execution_uses_prelaunch_retry_commitment execution⟩
  | s4 =>
      refine ⟨by simp [Complete], by simp [Complete], by simp [Complete], ?_⟩
      intro proxy carrier workerCarrier
      cases proxy <;> cases carrier <;> simp_all [Complete, evidenceFromProxyOnly]
  | s5 =>
      intro config state final event abstained
      exact abstained_state_has_no_successor abstained
  | s6 =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro config state role Verdict report authorized
        exact authorized.isolatedView
      · intro config state final event unavailable step
        exact unavailable_isolation_allows_only_abstain unavailable step
      · simp [GoalArtifactSnapshot.ContainsComplete, GoalArtifact.Complete,
          protocolGoalArtifact]
      · intro contains
        have fields : ({} : Finset GoalArtifactField) = Finset.univ :=
          contains.2.2
        have visible : GoalArtifactField.rawUserInput ∈
            ({} : Finset GoalArtifactField) := by
          rw [fields]
          simp
        simp at visible
  | s7 => exact ⟨by decide, by decide, by decide⟩
  | s8 =>
      exact ⟨design_and_review_router_exits_have_executable_transitions,
        review_router_reject_precedence, termination_fake_roster_precedence,
        termination_unsatisfied_precedence,
        fun _ _ _ _ carried step =>
          every_protocol_event_invalidates_carried_permit carried step,
        no_stale_termination_permit_after_fix,
        implementation_branch_preserves_permit_payload⟩
  | s9 =>
      refine ⟨by decide, termination_router_sound_maximal_unique.1,
        termination_router_sound_maximal_unique.2.1,
        termination_router_sound_maximal_unique.2.2, ?_⟩
      intro observation withheld
      simp [optimalTerminationRule, inlineConsensusModel, withheld]
  | s10 =>
      refine ⟨rfl, trivial, trivial, trivial, trivial, ?_⟩
      intro config run
      exact ⟨(every_maximal_run_is_bounded config run).2.2.1,
        (every_maximal_run_is_bounded config run).2.2.2⟩

end D5.S0.History.Consensus.InlineConsensusProtocolFixtures
