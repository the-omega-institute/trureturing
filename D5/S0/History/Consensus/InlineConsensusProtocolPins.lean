/- GID: D5/S0/History/Consensus/InlineConsensusProtocolPins
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusProtocolPins
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Aggregate mutation pins for the complete inline consensus protocol contract. -/
import D5.S0.History.Consensus.InlineConsensusProtocolFixtures
namespace D5.S0.History.Consensus.InlineConsensusProtocolFixtures
open InlineConsensusOptimality
def CompletionContract : Prop :=
  (forall exited artifact envelope verdict sentinel,
    Complete .codexCli (.codex exited artifact envelope verdict sentinel) <->
      exited = true /\ artifact = true /\ envelope = true /\ verdict = true /\ sentinel = true) /\
  (forall terminal envelope verdict,
    Complete .nyxidOracle (.nyxid terminal envelope verdict) <->
      terminal = true /\ envelope = true /\ verdict = true) /\
  (forall envelope verdict,
    Complete .isolatedTokenSubagent (.subagent envelope verdict) <->
      envelope = true /\ verdict = true) /\
  Not (Complete .nyxidOracle completeCodexObservation) /\
  Not (Complete .codexCli completeNyxidObservation) /\
  (forall field, Not (Complete .codexCli (missingCompletionConjunct field))) /\
  (forall proxy carrier, carrier != .abstain ->
    Not (Complete carrier (evidenceFromProxyOnly carrier proxy)))
theorem completion_contract_is_complete : CompletionContract := by
  refine ⟨by simp [Complete], by simp [Complete], by simp [Complete],
    codex_evidence_cannot_complete_nyxid, nyxid_evidence_cannot_complete_codex,
    ?_, completion_proxy_is_never_completion⟩
  intro field
  cases field <;> simp [Complete, missingCompletionConjunct]
def IsolationContract : Prop :=
  Nonempty (SeatView ≃ GoalArtifactSnapshot × SeatRole × PriorExposure) /\
    (forall view : SeatView, view.goalArtifact = .complete) /\
    (forall config state final event, state.isolation = .unavailable ->
      ProtocolStep config state event final -> exists stage, event = .abstain stage)
theorem isolation_contract_is_complete : IsolationContract :=
  ⟨⟨seat_view_information_content⟩, seat_view_contains_complete_goal,
    unavailable_isolation_allows_only_abstain⟩
def RouterEquations : Prop :=
  designRouter .unanimousActionable = .implement /\
    designRouter .compatiblePlans = .metaLayerConvergence /\
    designRouter .boundedStall = .abstainEscalate /\
    designRouter .singlePerspective = .rejectFakeConsensus /\
    reviewRouter (fun _ => .reject) = .fix /\
    reviewRouter (fun _ => .approve) = .done /\
    reviewRouter (fun _ => .comment) = .userDecisionOrBoundedPass /\
    terminationRouter permittedObservation = .permitClaim /\
    terminationRouter fakeRosterObservation = .rejectFakeConsensus /\
    terminationRouter unsatisfiedObservation = .continueAgainstGap /\
    terminationRouter abstainObservation = .escalateEvidenceGap /\
    terminationRouter invalidObservation = .escalateEvidenceGap /\
    terminationRouter missingObservation = .escalateEvidenceGap
theorem all_router_equations_hold : RouterEquations := by
  exact ⟨rfl, rfl, rfl, rfl, review_router_truth_table.1,
    review_router_truth_table.2.1, review_router_truth_table.2.2,
    termination_router_permits_exact_unanimous_satisfaction,
    by decide, by decide, by decide, by decide, by decide⟩
def ExecutableRouterRows : Prop :=
  RouterTransitionsExhaustive /\
    ProtocolStep fixtureConfig designImplementStart
      (.advance .metaJudge .implementationWorker) designImplementFinal /\
    ProtocolStep fixtureConfig designCompatibleStart
      (.boundedPass .metaJudge .metaLayerConvergence) designConvergenceFinal /\
    ProtocolStep fixtureConfig designCompatibleStart
      (.boundedPass .metaJudge .metaLayerConvergence) designConvergenceExhaustedFinal /\
    ProtocolStep fixtureConfig designStallStart (.abstain .metaJudge) designStallFinal /\
    ProtocolStep fixtureConfig designFakeConsensusStart
      (.abstain .metaJudge) designFakeConsensusFinal /\
    ProtocolStep fixtureConfig stalePermitFixStart
      (.boundedPass .fixOrDone .fixPass) stalePermitFixFinal /\
    ProtocolStep fixtureConfig terminationEvaluationStart
      (.boundedPass .fixOrDone .terminationGate) terminationEvaluationFinal /\
    ProtocolStep fixtureConfig allCommentReviewStart
      (.boundedPass .fixOrDone .repeatedReview) allCommentRepeatedReviewFinal /\
    ProtocolStep fixtureConfig allCommentReviewStart
      (.abstain .fixOrDone) allCommentUserDecisionFinal /\
    ProtocolStep fixtureConfig terminationRoutingStart
      (.boundedPass .fixOrDone .terminationGate) terminationFakeFinal /\
    ProtocolStep fixtureConfig terminationRoutingStart
      (.boundedPass .fixOrDone .terminationGate) terminationUnsatisfiedFinal /\
    ProtocolStep fixtureConfig terminationRoutingStart
      (.boundedPass .fixOrDone .terminationGate) terminationAbstainFinal /\
    ProtocolStep fixtureConfig terminationRoutingStart
      (.boundedPass .fixOrDone .terminationGate) terminationInvalidFinal /\
    ProtocolStep fixtureConfig terminationRoutingStart
      (.boundedPass .fixOrDone .terminationGate) terminationMissingFinal
theorem executable_router_rows_are_complete : ExecutableRouterRows := by
  exact ⟨router_transitions_are_exhaustive, designImplementStep, designConvergenceStep,
    designConvergenceExhaustedStep, designStallStep, designFakeConsensusStep,
    stalePermitFixStep, terminationEvaluationStep, allCommentRepeatedReviewStep,
    allCommentUserDecisionStep, terminationFakeStep, terminationUnsatisfiedStep,
    terminationAbstainStep, terminationInvalidStep, terminationMissingStep⟩
def TerminationMetaJudgeExclusion : Prop :=
  Nonempty (TerminationObservation ≃ TerminationRoster ×
    (TerminationSeatResult .criterionEvidence × TerminationSeatResult .residualGap ×
      TerminationSeatResult .claimIntegrity)) /\
    Fintype.card TerminationSeat = 3 /\
    (forall observation, terminationRouter observation ≠ .permitClaim ->
      optimalTerminationRule observation = false)
theorem termination_meta_judge_exclusion_is_complete : TerminationMetaJudgeExclusion :=
  ⟨⟨termination_observation_information_content⟩,
    termination_roster_has_exactly_three_named_seat_types,
    nonpermitting_observation_cannot_admit⟩
inductive ClauseId | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10
  deriving DecidableEq, Fintype, Repr
/-- Each entry is the full internal proposition assigned to one protocol clause. -/
def ClauseObject : ClauseId -> Prop
  | .s1 => Stage.next .intake = some .chooseWorkerMode /\
      Stage.next .chooseWorkerMode = some .thinkingPanelWorkers /\
      Stage.next .thinkingPanelWorkers = some .metaJudge /\
      Stage.next .metaJudge = some .implementationWorker /\
      Stage.next .implementationWorker = some .reviewTripletWorkers /\
      Stage.next .reviewTripletWorkers = some .fixOrDone /\ Stage.next .fixOrDone = none
  | .s2 => (Carrier.priorityRank .codexCli = 0 /\ Carrier.priorityRank .nyxidOracle = 1 /\
      Carrier.priorityRank .isolatedTokenSubagent = 2 /\ Carrier.priorityRank .abstain = 3) /\
      (forall eligible tried, (eligibleUntried eligible tried).Nonempty ->
        selectCarrier eligible tried ∈ eligibleUntried eligible tried /\
        forall other, other ∈ eligibleUntried eligible tried ->
          (forall carrier, carrier ∈ eligibleUntried eligible tried ->
            Carrier.priorityRank other <= Carrier.priorityRank carrier) ->
          other = selectCarrier eligible tried) /\
      Not (SelectedWorkerEvidence fixtureConfig implementationSelectionStart .implementation
        completedNyxidImplementationResult) /\
      Not (SelectedWorkerEvidence fixtureConfig stalePermitFixFinal .implementation
        completedImplementationResult) /\
      Not (exists carrier,
        CarrierLegalAt (initialState fixtureConfig).stage .implementation carrier)
  | .s3 => forall stage role carrier, fixtureConfig.retryBudget stage role carrier = 2
  | .s4 => CompletionContract
  | .s5 => (Execution inlineConsensusModel fixtureConfig thinkingExhaustedStart
      thinkingAbstainEvents thinkingAbstainFinal /\
      forall event, event ∈ thinkingAbstainEvents -> event = .abstain .thinkingPanelWorkers) /\
      (forall config state, state.phase = .abstained -> forall event final,
        Not (ProtocolStep config state event final))
  | .s6 => IsolationContract
  | .s7 => (priorExposure .codexCli = .repoPriorExposed /\
      priorExposure .nyxidOracle = .externalPriorExposed /\
      priorExposure .isolatedTokenSubagent = .callerPriorExposed /\
      priorExposure .abstain = .noCarrier) /\
      priorExposure .codexCli != priorExposure .nyxidOracle /\
      forall latent, correlatedConclusion .codexCli latent =
        correlatedConclusion .nyxidOracle latent
  | .s8 => RouterEquations /\ ExecutableRouterRows
  | .s9 => TerminationMetaJudgeExclusion /\ Sound optimalTerminationRule /\
      (forall rule, Sound rule -> RuleLE rule optimalTerminationRule) /\
      (forall rule, Greatest rule -> rule = optimalTerminationRule)
  | .s10 => fixtureConfig.sharedPassBudget = 5 /\
      BoundedPassKind.LegalAt .metaLayerConvergence .metaJudge /\
      BoundedPassKind.LegalAt .repeatedReview .fixOrDone /\
      BoundedPassKind.LegalAt .fixPass .fixOrDone /\
      BoundedPassKind.LegalAt .terminationGate .fixOrDone /\
      terminationEvaluationFinal.passesUsed = terminationEvaluationStart.passesUsed + 1 /\
      forall final, Not (ProtocolStep fixtureConfig terminationBudgetCeilingState
        (.boundedPass .fixOrDone .terminationGate) final)
theorem clause_object_index_is_total : forall clause, ClauseObject clause := by
  intro clause
  cases clause
  · exact stage_order_is_the_protocol_order
  · exact ⟨carrier_priority_is_the_protocol_priority,
      selectCarrier_is_unique_minimum, lower_priority_carrier_cannot_displace_available_codex,
      repeated_carrier_attempt_after_success_is_rejected,
      implementation_role_cannot_justify_intake_exhaustion⟩
  · exact retry_budget_is_fixed_per_flight
  · exact completion_contract_is_complete
  · exact ⟨thinking_abstain_skips_all_dependent_stages, abstained_state_has_no_successor⟩
  · exact isolation_contract_is_complete
  · exact ⟨prior_exposure_is_per_carrier,
      heterogeneous_carriers_need_not_have_independent_priors⟩
  · exact ⟨all_router_equations_hold, executable_router_rows_are_complete⟩
  · exact ⟨termination_meta_judge_exclusion_is_complete,
      termination_router_sound_maximal_unique⟩
  · exact ⟨shared_pass_budget_default_is_five,
      bounded_pass_kinds_have_only_legal_loci.1,
      bounded_pass_kinds_have_only_legal_loci.2.1,
      bounded_pass_kinds_have_only_legal_loci.2.2.1,
      bounded_pass_kinds_have_only_legal_loci.2.2.2,
      termination_roster_evaluation_consumes_exactly_one_shared_pass.2.1,
      termination_roster_evaluation_is_blocked_at_budget_ceiling⟩
def ClauseCoveragePin : Prop :=
  CompletionContract /\ IsolationContract /\ RouterEquations /\
    TerminationMetaJudgeExclusion /\ forall clause, ClauseObject clause
theorem clause_coverage_pin_is_pinned : ClauseCoveragePin :=
  ⟨completion_contract_is_complete, isolation_contract_is_complete,
    all_router_equations_hold, termination_meta_judge_exclusion_is_complete,
    clause_object_index_is_total⟩
def PermitFreshnessPin : Prop :=
  NoStaleTerminationPermitAfterFix /\
    (forall final, Not (ProtocolStep fixtureConfig allRejectReviewFinal
      (.boundedPass .fixOrDone .terminationGate) final)) /\
    stalePermitFixStart.terminationExit = some .permitClaim /\
    stalePermitFixFinal.terminationExit = none /\
    forall final, Not (ProtocolStep fixtureConfig stalePermitFixFinal .finish final)
theorem permit_freshness_pin_is_pinned : PermitFreshnessPin :=
  ⟨no_stale_termination_permit_after_fix,
    old_all_reject_stale_permit_sequence_is_unreachable, rfl, rfl,
    any_fix_after_a_permitting_evaluation_invalidates_that_permit.2.2.2⟩
def CarrierGovernancePin : Prop :=
  (forall eligible tried, (eligibleUntried eligible tried).Nonempty ->
    selectCarrier eligible tried ∈ eligibleUntried eligible tried /\
      forall other, other ∈ eligibleUntried eligible tried ->
        (forall carrier, carrier ∈ eligibleUntried eligible tried ->
          Carrier.priorityRank other <= Carrier.priorityRank carrier) ->
        other = selectCarrier eligible tried) /\
    Not (SelectedWorkerEvidence fixtureConfig implementationSelectionStart .implementation
      completedNyxidImplementationResult) /\
    Not (SelectedWorkerEvidence fixtureConfig stalePermitFixFinal .implementation
      completedImplementationResult) /\
    Not (exists carrier, CarrierLegalAt (initialState fixtureConfig).stage .implementation carrier)
theorem carrier_governance_pin_is_pinned : CarrierGovernancePin :=
  ⟨selectCarrier_is_unique_minimum, lower_priority_carrier_cannot_displace_available_codex,
    repeated_carrier_attempt_after_success_is_rejected,
    implementation_role_cannot_justify_intake_exhaustion⟩
def ExecutableRoutingPin : Prop :=
  RouterTransitionsExhaustive /\ ExecutableRouterRows /\
    ProtocolStep fixtureConfig designCompatibleStart
      (.boundedPass .metaJudge .metaLayerConvergence) designConvergenceExhaustedFinal /\
    ProtocolStep fixtureConfig allCommentReviewStart
      (.abstain .fixOrDone) allCommentUserDecisionFinal
theorem executable_routing_pin_is_pinned : ExecutableRoutingPin :=
  ⟨router_transitions_are_exhaustive, executable_router_rows_are_complete,
    designConvergenceExhaustedStep, allCommentUserDecisionStep⟩
def RequiredFixtureSuite : Prop :=
    (Stage.next .intake = some .chooseWorkerMode /\
      Stage.next .chooseWorkerMode = some .thinkingPanelWorkers /\
      Stage.next .thinkingPanelWorkers = some .metaJudge /\
      Stage.next .metaJudge = some .implementationWorker /\
      Stage.next .implementationWorker = some .reviewTripletWorkers /\
      Stage.next .reviewTripletWorkers = some .fixOrDone /\ Stage.next .fixOrDone = none) /\
      (forall (source first second : Stage), source.Successor first ->
        source.Successor second -> first = second) /\
      (Carrier.priorityRank .codexCli = 0 /\ Carrier.priorityRank .nyxidOracle = 1 /\
        Carrier.priorityRank .isolatedTokenSubagent = 2 /\ Carrier.priorityRank .abstain = 3) /\
      (priorExposure .codexCli = .repoPriorExposed /\
        priorExposure .nyxidOracle = .externalPriorExposed /\
        priorExposure .isolatedTokenSubagent = .callerPriorExposed /\
        priorExposure .abstain = .noCarrier) /\
      designRouter .singlePerspective = .rejectFakeConsensus /\
      (inlineConsensusModel.stageRelation = Stage.Successor /\
        inlineConsensusModel.carrierSelector = selectCarrier /\
        inlineConsensusModel.carrierLegalAt = CarrierLegalAt /\
        inlineConsensusModel.completionPredicate = Complete /\
        inlineConsensusModel.seatView = SeatView /\
        inlineConsensusModel.thinkingResults = ThinkingResults /\
        inlineConsensusModel.thinkingSituationFrom = thinkingSituation /\
        inlineConsensusModel.reviewResults = ReviewResults /\
        inlineConsensusModel.priorDisclosure = priorExposure /\
        inlineConsensusModel.designRoute = designRouter /\
        inlineConsensusModel.reviewRoute = reviewRouter /\
        inlineConsensusModel.terminationRoute = terminationRouter /\
        inlineConsensusModel.rosterContract = ExactRoster /\
        inlineConsensusModel.passLegalAt = BoundedPassKind.LegalAt /\
        inlineConsensusModel.transition = ProtocolStep) /\
      (forall roster, exactRosterBool roster = true <-> ExactRoster roster) /\
      (forall {seat : TerminationSeat} (result : TerminationSeatResult seat),
        result.isSatisfiedBool = true <-> result.IsSatisfied) /\
      (forall observation, terminationAdmits observation = true <->
        ExactRoster observation.roster /\ allSatisfied observation) /\
      (Sound optimalTerminationRule /\
        (forall rule, Sound rule -> RuleLE rule optimalTerminationRule) /\
        (forall rule, Greatest rule -> rule = optimalTerminationRule)) /\
      (forall config (run : MaximalRun inlineConsensusModel config),
        WithinRetryBudgets config run.events /\ NoCarrierReopened run.events /\
        sharedPassCount run.events <= config.sharedPassBudget /\
        run.events.length <= explicitRunBound config) /\
      selectCarrier allEligible {} = .codexCli /\
      selectCarrier allEligible {.codexCli} = .nyxidOracle /\
      selectCarrier (fun _ => false) {} = .abstain /\
      Complete .codexCli completeCodexObservation /\
      Complete .nyxidOracle completeNyxidObservation /\
      Complete .isolatedTokenSubagent completeSubagentObservation /\
      Not (Complete .nyxidOracle completeCodexObservation) /\
      Not (Complete .codexCli completeNyxidObservation) /\
      Not (Complete .codexCli (missingCompletionConjunct .carrierExit)) /\
      Not (Complete .codexCli (missingCompletionConjunct .resultArtifact)) /\
      Not (Complete .codexCli (missingCompletionConjunct .envelope)) /\
      Not (Complete .codexCli (missingCompletionConjunct .verdict)) /\
      Not (Complete .codexCli (missingCompletionConjunct .sentinel)) /\
      (forall proxy carrier, carrier != .abstain ->
        Not (Complete carrier (evidenceFromProxyOnly carrier proxy))) /\
      (priorExposure .codexCli != priorExposure .nyxidOracle /\
        forall latent, correlatedConclusion .codexCli latent =
          correlatedConclusion .nyxidOracle latent) /\
      (forall result : CompletedSeatResult, Complete result.carrier result.completionObservation /\
        result.view.exposure = priorExposure result.carrier) /\
      Fintype.card TerminationSeat = 3 /\
      terminationRouter permittedObservation = .permitClaim /\
      terminationAdmits permittedObservation = true /\
      terminationAdmits fakeRosterObservation = false /\
      terminationAdmits unsatisfiedObservation = false /\
      terminationAdmits abstainObservation = false /\
      terminationAdmits invalidObservation = false /\
      terminationAdmits missingObservation = false /\
      Sound alwaysAbstain /\ StrictBelow alwaysAbstain terminationAdmits /\
      StrictBelow terminationAdmits majorityAdmit /\ Not (Sound majorityAdmit) /\
      (reviewRouter (fun _ => .reject) = .fix /\
        reviewRouter (fun _ => .approve) = .done /\
        reviewRouter (fun _ => .comment) = .userDecisionOrBoundedPass) /\
      Fintype.card ThinkingSeat = 6 /\ Fintype.card ReviewSeat = 3 /\
      (thinkingSituation fixturePlanCompatibility unanimousThinkingResults = .unanimousActionable /\
        designRouter (thinkingSituation fixturePlanCompatibility unanimousThinkingResults) =
          .implement) /\
      (thinkingSituation fixturePlanCompatibility compatibleThinkingResults = .compatiblePlans /\
        designRouter (thinkingSituation fixturePlanCompatibility compatibleThinkingResults) =
          .metaLayerConvergence) /\
      (thinkingSituation fixturePlanCompatibility conflictingThinkingResults = .boundedStall /\
        designRouter (thinkingSituation fixturePlanCompatibility conflictingThinkingResults) =
          .abstainEscalate) /\
      (thinkingSituation fixturePlanCompatibility singlePerspectiveThinkingResults =
          .singlePerspective /\
        designRouter (thinkingSituation fixturePlanCompatibility singlePerspectiveThinkingResults) =
          .rejectFakeConsensus) /\
      fixtureConfig.sharedPassBudget = 5 /\
      (forall stage role carrier, fixtureConfig.retryBudget stage role carrier = 2) /\
      (BoundedPassKind.LegalAt .metaLayerConvergence .metaJudge /\
        BoundedPassKind.LegalAt .repeatedReview .fixOrDone /\
        BoundedPassKind.LegalAt .fixPass .fixOrDone /\
        BoundedPassKind.LegalAt .terminationGate .fixOrDone) /\
      (Execution inlineConsensusModel fixtureConfig thinkingExhaustedStart
          thinkingAbstainEvents thinkingAbstainFinal /\
        forall event, event ∈ thinkingAbstainEvents -> event = .abstain .thinkingPanelWorkers) /\
      (forall config state, state.phase = .abstained -> forall event final,
        Not (ProtocolStep config state event final)) /\
      Execution inlineConsensusModel unavailableIsolationConfig
        (initialState unavailableIsolationConfig) [.abstain .intake] unavailableIsolationFinal /\
      (forall state, state.isolation = .unavailable -> forall final,
        Not (ProtocolStep fixtureConfig state .finish final)) /\
      (forall state, state.isolation = .unavailable -> forall role carrier attempts final,
        Not (ProtocolStep fixtureConfig state
          (.flightFailure state.stage role carrier attempts) final)) /\
      (forall state, state.isolation = .unavailable -> forall kind final,
        Not (ProtocolStep fixtureConfig state (.boundedPass state.stage kind) final)) /\
      (forall state, state.isolation = .unavailable -> forall final,
        Not (ProtocolStep fixtureConfig state (.boundedPass state.stage .fixPass) final)) /\
      (forall config state final event, state.isolation = .unavailable ->
        ProtocolStep config state event final -> exists stage, event = .abstain stage) /\
      (ProtocolStep fixtureConfig terminationEvaluationStart
          (.boundedPass .fixOrDone .terminationGate) terminationEvaluationFinal /\
        terminationEvaluationFinal.passesUsed = terminationEvaluationStart.passesUsed + 1 /\
        terminationEvaluationFinal.terminationExit = some .permitClaim) /\
      (Not (exists final, ProtocolStep fixtureConfig terminationEvaluationStart .finish final) /\
        ProtocolStep fixtureConfig terminationEvaluationFinal .finish terminationFinishedState) /\
      (forall final, Not (ProtocolStep fixtureConfig terminationBudgetCeilingState
        (.boundedPass .fixOrDone .terminationGate) final)) /\
      Not (PassBudgetAuthorized unauthorizedOverBudgetConfig) /\
      (forall start event final,
        Not (ProtocolStep unauthorizedOverBudgetConfig start event final)) /\
      (forall start events final,
        Not (Execution inlineConsensusModel unauthorizedOverBudgetConfig start events final)) /\
      reviewRouter (reviewObservation allRejectReviewResults) = .fix /\
      allRejectReviewFinal.reviewExit = some .fix /\
      Not (exists final, ProtocolStep fixtureConfig allRejectReviewFinal .finish final) /\
      ClauseCoveragePin /\ PermitFreshnessPin /\ CarrierGovernancePin /\ ExecutableRoutingPin /\
      (forall clause, ClauseObject clause)
theorem required_fixture_suite_is_pinned : RequiredFixtureSuite := by
  unfold RequiredFixtureSuite
  exact ⟨stage_order_is_the_protocol_order, stage_successor_is_unique,
    carrier_priority_is_the_protocol_priority, prior_exposure_is_per_carrier,
    design_router_rejects_single_perspective, inline_consensus_model_internal_wiring,
    exact_roster_bool_iff, seat_result_satisfied_bool_iff, termination_admits_iff,
    termination_router_sound_maximal_unique, every_maximal_run_is_bounded,
    carrier_selection_starts_with_codex,
    carrier_selection_reopens_at_highest_priority_untried,
    carrier_selection_abstains_when_exhausted,
    codex_completion_requires_all_five_conjuncts,
    nyxid_completion_uses_structured_terminal_status_without_sentinel,
    subagent_completion_uses_valid_envelope_without_sentinel,
    codex_evidence_cannot_complete_nyxid, nyxid_evidence_cannot_complete_codex,
    missing_carrier_exit_fails_completion, missing_result_artifact_fails_completion,
    invalid_envelope_fails_completion, disallowed_verdict_fails_completion,
    missing_sentinel_fails_completion, completion_proxy_is_never_completion,
    heterogeneous_carriers_need_not_have_independent_priors,
    completed_seat_results_carry_completion_and_disclosure,
    termination_roster_has_exactly_three_named_seat_types,
    termination_router_permits_exact_unanimous_satisfaction,
    positive_permit_row_is_admitted, termination_router_rejects_fake_roster,
    termination_router_withholds_on_unsatisfied, termination_router_withholds_on_abstain,
    termination_router_withholds_on_invalid, termination_router_withholds_on_missing,
    always_abstain_is_sound, always_abstain_is_strictly_below_optimal,
    majority_admit_is_strictly_above_optimal, majority_admit_is_not_sound,
    review_router_truth_table, thinking_panel_has_exactly_six_named_role_indices,
    review_triplet_has_exactly_three_named_role_indices,
    design_row_unanimous_actionable_is_reachable,
    design_row_compatible_disagreement_is_reachable,
    design_row_bounded_stall_is_reachable_from_conflicting_proposals,
    design_row_single_perspective_is_reachable,
    shared_pass_budget_default_is_five, retry_budget_is_fixed_per_flight,
    bounded_pass_kinds_have_only_legal_loci, thinking_abstain_skips_all_dependent_stages,
    abstained_state_has_no_successor, unavailable_isolation_reaches_abstained_state,
    unavailable_isolation_cannot_finish, unavailable_isolation_cannot_retry_flight,
    unavailable_isolation_cannot_take_bounded_pass,
    unavailable_isolation_cannot_fix_and_review, unavailable_isolation_allows_only_abstain,
    termination_roster_evaluation_consumes_exactly_one_shared_pass,
    termination_finish_requires_and_uses_recorded_permit,
    termination_roster_evaluation_is_blocked_at_budget_ceiling,
    unauthorized_over_budget_config_is_rejected,
    unauthorized_over_budget_config_has_no_transition,
    unauthorized_over_budget_config_has_no_execution, all_reject_results_route_to_fix,
    all_reject_review_exit_is_retained_in_state,
    all_reject_review_cannot_reach_terminal_claim_without_fix,
    clause_coverage_pin_is_pinned, permit_freshness_pin_is_pinned,
    carrier_governance_pin_is_pinned, executable_routing_pin_is_pinned,
    clause_object_index_is_total⟩
end D5.S0.History.Consensus.InlineConsensusProtocolFixtures
