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
    implementation := .codexCli
    review := protocolReviewDispatch
    termination := protocolTerminationDispatch
    thinkingLayout := by decide
    reviewLayout := by decide
    terminationLayout := by decide }

def allCodexThinkingDispatch : ThinkingSeat -> Carrier := fun _ => .codexCli

def protocolEligibility : Stage -> SeatRole -> Eligibility :=
  fun _ _ carrier => carrier != .abstain

def mismatchedImplementationEligibility : Stage -> SeatRole -> Eligibility :=
  fun stage role carrier =>
    if stage == .implementationWorker && role == .implementation then
      carrier == .nyxidOracle
    else
      protocolEligibility stage role carrier

def protocolGoalArtifact : GoalArtifact :=
  { rawUserInput := some .digestA
    normalizedGoal := some .digestA
    constraints := some .digestA
    successCriteria := some .digestA
    iterationQuestion := some .digestA
    harness := some .digestA
    revisions := some .digestA }

def protocolAlternateGoalArtifact : GoalArtifact :=
  { protocolGoalArtifact with rawUserInput := some .digestB }

theorem protocol_initial_plan_is_compatible :
    InitialPlanCompatible protocolEligibility protocolDispatchPlan := by
  intro stage role carrier planned
  cases stage <;> cases role <;> cases carrier <;>
    simp_all [DispatchPlan.carrierAt, protocolDispatchPlan, protocolThinkingDispatch,
      protocolReviewDispatch, protocolTerminationDispatch, protocolEligibility,
      CarrierLegalAt, SeatRole.LegalAt, SeatRole.IsThinking, SeatRole.IsReview,
      SeatRole.IsTermination]

theorem mismatched_initial_plan_is_rejected :
    mismatchedImplementationEligibility .implementationWorker .implementation .codexCli =
        false /\
      mismatchedImplementationEligibility .implementationWorker .implementation
        .nyxidOracle = true /\
      Not (InitialPlanCompatible mismatchedImplementationEligibility protocolDispatchPlan) := by
  refine ⟨by decide, by decide, ?_⟩
  exact initial_plan_ineligible_is_rejected
    (eligible := mismatchedImplementationEligibility) (plan := protocolDispatchPlan)
    (stage := .implementationWorker) (role := .implementation) (carrier := .codexCli)
    rfl rfl

theorem two_distinct_complete_goal_artifacts_exist :
    exists first second : GoalArtifact,
      first.Complete /\ second.Complete /\ first ≠ second := by
  refine ⟨protocolGoalArtifact, protocolAlternateGoalArtifact, ?_, ?_, ?_⟩
  · simp [GoalArtifact.Complete, protocolGoalArtifact]
  · simp [GoalArtifact.Complete, protocolAlternateGoalArtifact, protocolGoalArtifact]
  · intro same
    have rawInput := congrArg GoalArtifact.rawUserInput same
    simp [protocolAlternateGoalArtifact, protocolGoalArtifact] at rawInput

theorem complete_goal_snapshot_is_accepted :
    GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
      (⟨protocolGoalArtifact, Finset.univ⟩ : GoalArtifactSnapshot) := by
  exact ⟨by simp [GoalArtifact.Complete, protocolGoalArtifact], rfl, rfl⟩

theorem full_snapshot_with_wrong_artifact_is_rejected :
    Not (GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
      (⟨protocolAlternateGoalArtifact, Finset.univ⟩ : GoalArtifactSnapshot)) := by
  intro contains
  have rawInput := congrArg GoalArtifact.rawUserInput contains.2.1
  simp [protocolAlternateGoalArtifact, protocolGoalArtifact] at rawInput

theorem empty_visible_fields_are_rejected :
    Not (GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
      (⟨protocolGoalArtifact, {}⟩ : GoalArtifactSnapshot)) := by
  intro contains
  have fields : ({} : Finset GoalArtifactField) = Finset.univ := contains.2.2
  have visible : GoalArtifactField.rawUserInput ∈ ({} : Finset GoalArtifactField) := by
    rw [fields]
    simp
  simp at visible

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
      Stage.next .fixOrDone = none /\
      (forall (source first second : Stage), source.Successor first ->
        source.Successor second -> first = second)
  | .s2 =>
      (Carrier.priorityRank .codexCli = 0 /\ Carrier.priorityRank .nyxidOracle = 1 /\
        Carrier.priorityRank .isolatedTokenSubagent = 2 /\
        Carrier.priorityRank .abstain = 3) /\
      (forall eligible tried, (eligibleUntried eligible tried).Nonempty ->
        selectCarrier eligible tried ∈ eligibleUntried eligible tried) /\
      (forall eligible tried carrier, carrier ∈ eligibleUntried eligible tried ->
        Carrier.priorityRank (selectCarrier eligible tried) <= Carrier.priorityRank carrier) /\
      (forall eligible tried, (eligibleUntried eligible tried).Nonempty ->
        selectCarrier eligible tried ∈ eligibleUntried eligible tried /\
          forall other, other ∈ eligibleUntried eligible tried ->
            (forall carrier, carrier ∈ eligibleUntried eligible tried ->
              Carrier.priorityRank other <= Carrier.priorityRank carrier) ->
            other = selectCarrier eligible tried) /\
      (forall eligible tried,
        selectCarrier eligible tried = .abstain <-> eligibleUntried eligible tried = {}) /\
      MultiSeatLayout protocolThinkingDispatch /\
      MultiSeatLayout protocolReviewDispatch /\
      MultiSeatLayout protocolTerminationDispatch /\
      Not (MultiSeatLayout allCodexThinkingDispatch) /\
      protocolDispatchPlan.implementation = .codexCli /\
      InitialPlanCompatible protocolEligibility protocolDispatchPlan /\
      (forall (eligible : Stage -> SeatRole -> Eligibility) (plan : DispatchPlan)
          (stage : Stage) (role : SeatRole) (carrier : Carrier),
        plan.carrierAt stage role = some carrier ->
        eligible stage role carrier = false ->
        Not (InitialPlanCompatible eligible plan)) /\
      (mismatchedImplementationEligibility .implementationWorker .implementation .codexCli =
          false /\
        mismatchedImplementationEligibility .implementationWorker .implementation
          .nyxidOracle = true /\
        Not (InitialPlanCompatible mismatchedImplementationEligibility protocolDispatchPlan)) /\
      (forall config state role carrier, FallbackAssigned config state role carrier ->
        (triedAt state state.stage role).Nonempty /\
        selectCarrier (config.eligible state.stage role)
          (triedAt state state.stage role) = carrier) /\
      (forall config state role carrier, FallbackAssigned config state role carrier ->
        exists failedCarrier,
          flightKey state.stage role failedCarrier ∈ state.exhaustedFlights) /\
      SuccessfulFixConsumesImplementationCarrier /\
      (forall config (run : MaximalRun inlineConsensusModel config),
        NoCarrierReopened run.events) /\
      (forall config state role, role.LegalAt state.stage ->
        triedAt state state.stage role = {} ->
          (exists carrier,
            InitiallyAssigned config state role carrier /\
              CarrierLegalAt state.stage role carrier /\
              config.eligible state.stage role carrier = true) \/
          selectCarrier (config.eligible state.stage role)
            (triedAt state state.stage role) = .abstain)
  | .s3 =>
      (forall config state final role carrier attempts,
        ProtocolStep config state (.flightFailure state.stage role carrier attempts) final ->
          0 < attempts /\ attempts = config.retryBudget state.stage role carrier) /\
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
      (forall config state final stage,
        ProtocolStep config state (.abstain stage) final -> final.phase = .abstained) /\
      (forall config state final event, state.phase = .abstained ->
        Not (ProtocolStep config state event final))
  | .s6 =>
      (forall config state role (Verdict : Type) (report : WorkerReport Verdict),
        AuthorizedReport config state role report ->
          report.view.IsolatedComplete config.goalArtifact) /\
      (forall config state final event, state.isolation = .unavailable ->
        ProtocolStep config state event final -> exists stage, event = .abstain stage) /\
      (exists first second : GoalArtifact,
        first.Complete /\ second.Complete /\ first ≠ second) /\
      GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
        (⟨protocolGoalArtifact, Finset.univ⟩ : GoalArtifactSnapshot) /\
      Not (GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
        (⟨protocolAlternateGoalArtifact, Finset.univ⟩ : GoalArtifactSnapshot)) /\
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
      designRouter .unanimousActionable = .implement /\
      designRouter .compatiblePlans = .metaLayerConvergence /\
      designRouter .boundedStall = .abstainEscalate /\
      designRouter .singlePerspective = .rejectFakeConsensus /\
      (forall observation, (exists index, observation index = .reject) ->
        reviewRouter observation = .fix) /\
      (forall observation, (forall index, observation index != .reject) ->
        (exists index, observation index = .approve) -> reviewRouter observation = .done) /\
      (forall observation, (forall index, observation index = .comment) ->
        reviewRouter observation = .userDecisionOrBoundedPass) /\
      (forall roster, exactRosterBool roster = true <-> ExactRoster roster) /\
      (forall observation, terminationRouter observation = .permitClaim <->
        ExactRoster observation.roster /\ allSatisfied observation) /\
      (forall observation, Not (ExactRoster observation.roster) ->
        terminationRouter observation = .rejectFakeConsensus) /\
      (forall observation, ExactRoster observation.roster ->
        (exists seat, (observation.result seat).isUnsatisfiedBool = true) ->
        terminationRouter observation = .continueAgainstGap) /\
      (forall observation, ExactRoster observation.roster ->
        Not (allSatisfied observation) ->
        (forall seat, (observation.result seat).isUnsatisfiedBool = false) ->
        terminationRouter observation = .escalateEvidenceGap)
  | .s9 =>
      Fintype.card TerminationSeat = 3 /\
      (forall observation, terminationAdmits observation = true <->
        ExactRoster observation.roster /\ allSatisfied observation) /\
      Sound optimalTerminationRule /\
      (forall rule, Sound rule -> RuleLE rule optimalTerminationRule) /\
      (forall rule, Greatest rule -> rule = optimalTerminationRule) /\
      Sound alwaysAbstain /\
      StrictBelow alwaysAbstain optimalTerminationRule /\
      StrictBelow optimalTerminationRule majorityAdmit /\
      Not (Sound majorityAdmit) /\
      (forall observation, terminationRouter observation ≠ .permitClaim ->
        optimalTerminationRule observation = false) /\
      (forall config start final event, ProtocolStep config start event final ->
        final.eventEpoch = start.eventEpoch + 1) /\
      (forall config state final,
        ProtocolStep config state (.boundedPass state.stage .terminationGate) final ->
          state.reviewExit = some .done /\
          state.reviewEpoch = some state.artifactEpoch) /\
      (forall config start final event,
        start.terminationExit = some .permitClaim ->
        ProtocolStep config start event final -> Not (FinishPrecondition final)) /\
      NoStaleTerminationPermitAfterFix /\
      ImplementationAdvancePreservesPermitPayload
  | .s10 =>
      defaultSharedPassBudget = 5 /\
      (forall config, PassBudgetAuthorized config <->
        config.sharedPassBudget <= defaultSharedPassBudget \/
          config.ownerAuthorizedAboveDefault = true) /\
      (forall config start events final,
        Execution inlineConsensusModel config start events final ->
          PassBudgetAuthorized config) /\
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
  | s1 =>
      rcases stage_order_is_the_protocol_order with ⟨h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h7, stage_successor_is_unique⟩
  | s2 =>
      exact ⟨carrier_priority_is_the_protocol_priority,
        selectCarrier_mem, selectCarrier_minimal, selectCarrier_is_unique_minimum,
        selectCarrier_eq_abstain_iff,
        legal_preassigned_layout.1, legal_preassigned_layout.2.1,
        legal_preassigned_layout.2.2, illegal_all_codex_layout_is_rejected,
        rfl, protocol_initial_plan_is_compatible,
        (fun _ _ _ _ _ planned ineligible =>
          initial_plan_ineligible_is_rejected planned ineligible),
        mismatched_initial_plan_is_rejected,
        (fun _ _ _ _ fallback => fallback_selection_requires_a_tried_origin fallback),
        (fun _ _ _ _ fallback => fallback_selection_requires_exhausted_origin fallback),
        successful_fix_consumes_implementation_carrier,
        every_maximal_run_never_reopens_carrier,
        legal_worker_stage_initially_progresses_or_abstains⟩
  | s3 =>
      exact ⟨fun _ _ _ _ _ _ step =>
        flight_failure_occurs_only_after_precommitted_budget_exhaustion step,
        fun _ _ _ _ execution =>
          every_execution_uses_prelaunch_retry_commitment execution⟩
  | s4 =>
      refine ⟨by simp [Complete], by simp [Complete], by simp [Complete], ?_⟩
      intro proxy carrier workerCarrier
      cases proxy <;> cases carrier <;> simp_all [Complete, evidenceFromProxyOnly]
  | s5 =>
      exact ⟨(fun _ _ _ _ step => abstain_event_enters_absorbing_state step),
        fun _ _ _ _ abstained => abstained_state_has_no_successor abstained⟩
  | s6 =>
      refine ⟨?_, ?_, two_distinct_complete_goal_artifacts_exist,
        complete_goal_snapshot_is_accepted,
        full_snapshot_with_wrong_artifact_is_rejected,
        empty_visible_fields_are_rejected⟩
      · intro config state role Verdict report authorized
        exact authorized.isolatedView
      · intro config state final event unavailable step
        exact unavailable_isolation_allows_only_abstain unavailable step
  | s7 => exact ⟨by decide, by decide, by decide⟩
  | s8 =>
      exact ⟨design_and_review_router_exits_have_executable_transitions,
        by decide, by decide, by decide, design_router_rejects_single_perspective,
        review_router_reject_precedence, review_router_approve_without_reject,
        review_router_all_comment, exact_roster_bool_iff, termination_router_permit_iff,
        termination_fake_roster_precedence, termination_unsatisfied_precedence,
        termination_evidence_gap_precedence⟩
  | s9 =>
      rcases termination_router_sound_maximal_unique with
        ⟨sound, greatest, unique, abstainSound, abstainStrict, majorityStrict,
          majorityUnsound⟩
      exact ⟨by decide, termination_admits_iff, sound, greatest, unique,
        abstainSound, abstainStrict,
        majorityStrict, majorityUnsound, nonpermitting_observation_cannot_admit,
        (fun _ _ _ _ step => every_protocol_event_increments_epoch step),
        (fun _ _ _ step => termination_gate_requires_current_done_review step),
        (fun _ _ _ _ carried step =>
          every_protocol_event_invalidates_carried_permit carried step),
        no_stale_termination_permit_after_fix,
        implementation_branch_preserves_permit_payload⟩
  | s10 =>
      refine ⟨rfl, (fun _ => Iff.rfl),
        (fun _ _ _ _ execution => every_execution_uses_authorized_shared_budget execution),
        trivial, trivial, trivial, trivial, ?_⟩
      intro config run
      exact ⟨(every_maximal_run_is_bounded config run).2.2.1,
        (every_maximal_run_is_bounded config run).2.2.2⟩

end D5.S0.History.Consensus.InlineConsensusProtocolFixtures
