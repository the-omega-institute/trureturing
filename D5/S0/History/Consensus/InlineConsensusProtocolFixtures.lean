/- GID: D5/S0/History/Consensus/InlineConsensusProtocolFixtures
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusProtocolFixtures
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Named protocol executions and aggregate mutation pins for inline consensus. -/
import D5.S0.History.Consensus.InlineConsensusExecution
namespace D5.S0.History.Consensus.InlineConsensusProtocolFixtures
open InlineConsensusOptimality
def allEligible : Eligibility := fun carrier => carrier != .abstain
theorem carrier_selection_starts_with_codex : selectCarrier allEligible {} = .codexCli := by decide
theorem carrier_selection_reopens_at_highest_priority_untried :
    selectCarrier allEligible {.codexCli} = .nyxidOracle := by decide
theorem carrier_selection_abstains_when_exhausted :
    selectCarrier (fun _ => false) {} = .abstain := by decide
def completeCodexObservation : CompletionObservation := .codex true true true true true
def completeNyxidObservation : CompletionObservation := .nyxid true true true
def completeSubagentObservation : CompletionObservation := .subagent true true
theorem codex_completion_requires_all_five_conjuncts :
    Complete .codexCli completeCodexObservation := by
  simp [Complete, completeCodexObservation]
theorem nyxid_completion_uses_structured_terminal_status_without_sentinel :
    Complete .nyxidOracle completeNyxidObservation := by
  simp [Complete, completeNyxidObservation]
theorem subagent_completion_uses_valid_envelope_without_sentinel :
    Complete .isolatedTokenSubagent completeSubagentObservation := by
  simp [Complete, completeSubagentObservation]
theorem codex_evidence_cannot_complete_nyxid :
    Not (Complete .nyxidOracle completeCodexObservation) := by
  simp [Complete, completeCodexObservation]
theorem nyxid_evidence_cannot_complete_codex :
    Not (Complete .codexCli completeNyxidObservation) := by
  simp [Complete, completeNyxidObservation]
def missingCompletionConjunct : CompletionConjunct -> CompletionObservation
  | .carrierExit =>
      .codex false true true true true
  | .resultArtifact =>
      .codex true false true true true
  | .envelope =>
      .codex true true false true true
  | .verdict =>
      .codex true true true false true
  | .sentinel =>
      .codex true true true true false
private theorem missing_completion_is_incomplete (field : CompletionConjunct) :
    Not (Complete .codexCli (missingCompletionConjunct field)) := by
  cases field <;> simp [missingCompletionConjunct, Complete]
theorem missing_carrier_exit_fails_completion :
    Not (Complete .codexCli (missingCompletionConjunct .carrierExit)) :=
  missing_completion_is_incomplete _
theorem missing_result_artifact_fails_completion :
    Not (Complete .codexCli (missingCompletionConjunct .resultArtifact)) :=
  missing_completion_is_incomplete _
theorem invalid_envelope_fails_completion :
    Not (Complete .codexCli (missingCompletionConjunct .envelope)) :=
  missing_completion_is_incomplete _
theorem disallowed_verdict_fails_completion :
    Not (Complete .codexCli (missingCompletionConjunct .verdict)) :=
  missing_completion_is_incomplete _
theorem missing_sentinel_fails_completion :
    Not (Complete .codexCli (missingCompletionConjunct .sentinel)) :=
  missing_completion_is_incomplete _
theorem completion_proxy_is_never_completion (proxy : ForbiddenCompletionProxy) :
    forall carrier, carrier != .abstain ->
      Not (Complete carrier (evidenceFromProxyOnly carrier proxy)) := by
  cases proxy <;> intro carrier workerCarrier <;> cases carrier <;>
    simp_all [evidenceFromProxyOnly, Complete]
theorem heterogeneous_carriers_need_not_have_independent_priors :
    priorExposure .codexCli != priorExposure .nyxidOracle /\
      forall latent, correlatedConclusion .codexCli latent =
        correlatedConclusion .nyxidOracle latent := by
  decide
def exactRoster : TerminationRoster
  | 0 => some .criterionEvidence
  | 1 => some .residualGap
  | _ => some .claimIntegrity
def fakeRoster : TerminationRoster
  | 0 => some .criterionEvidence
  | 1 => some .criterionEvidence
  | _ => some .claimIntegrity
def completedTerminationResult (seat : TerminationSeat) (verdict : TerminationVerdict) :
    TerminationSeatResult seat :=
  .completed
    { view := ⟨.complete, seat.role, .repoPriorExposed⟩, carrier := .codexCli
      workerCarrier := by decide, completionObservation := completeCodexObservation
      complete := codex_completion_requires_all_five_conjuncts, exposureMatches := rfl }
    rfl verdict
def completedReviewResult (seat : ReviewSeat) (verdict : ReviewVerdict) :
    ReviewSeatResult seat :=
  .completed
    { view := ⟨.complete, seat.role, .repoPriorExposed⟩, carrier := .codexCli
      workerCarrier := by decide, completionObservation := completeCodexObservation
      complete := codex_completion_requires_all_five_conjuncts, exposureMatches := rfl }
    rfl verdict
def completedThinkingResult (seat : ThinkingSeat) (verdict : ThinkingVerdict)
    (plan : Option PlanIdentity) (presentedAsConsensus : Bool) :
    ThinkingSeatResult seat :=
  .completed
    { view := ⟨.complete, seat.role, .repoPriorExposed⟩, carrier := .codexCli
      workerCarrier := by decide, completionObservation := completeCodexObservation
      complete := codex_completion_requires_all_five_conjuncts, exposureMatches := rfl }
    rfl verdict plan presentedAsConsensus
theorem completed_seat_results_carry_completion_and_disclosure (result : CompletedSeatResult) :
    Complete result.carrier result.completionObservation /\
      result.view.exposure = priorExposure result.carrier :=
  ⟨result.complete, result.exposureMatches⟩
def allSatisfiedResults : (seat : TerminationSeat) -> TerminationSeatResult seat :=
  fun seat => completedTerminationResult seat .satisfied
def permittedObservation : TerminationObservation :=
  { roster := exactRoster, result := allSatisfiedResults }
def fakeRosterObservation : TerminationObservation :=
  { roster := fakeRoster, result := allSatisfiedResults }
def unsatisfiedObservation : TerminationObservation :=
  { roster := exactRoster
    result := fun seat => match seat with
      | .criterionEvidence => completedTerminationResult _ .satisfied
      | .residualGap => completedTerminationResult _ .unsatisfied
      | .claimIntegrity => completedTerminationResult _ .satisfied }
def abstainObservation : TerminationObservation :=
  { roster := exactRoster
    result := fun seat => match seat with
      | .criterionEvidence => completedTerminationResult _ .satisfied
      | .residualGap => completedTerminationResult _ .abstain
      | .claimIntegrity => completedTerminationResult _ .satisfied }
def invalidObservation : TerminationObservation :=
  { roster := exactRoster
    result := fun seat => match seat with
      | .criterionEvidence => completedTerminationResult _ .satisfied
      | .residualGap => .invalid
      | .claimIntegrity => completedTerminationResult _ .satisfied }
def missingObservation : TerminationObservation :=
  { roster := exactRoster
    result := fun seat => match seat with
      | .criterionEvidence => completedTerminationResult _ .satisfied
      | .residualGap => .missing
      | .claimIntegrity => completedTerminationResult _ .satisfied }
theorem termination_roster_has_exactly_three_named_seat_types :
    Fintype.card TerminationSeat = 3 := by
  decide
theorem termination_router_permits_exact_unanimous_satisfaction :
    terminationRouter permittedObservation = .permitClaim := by decide
theorem positive_permit_row_is_admitted : terminationAdmits permittedObservation = true := by decide
theorem termination_router_rejects_fake_roster :
    terminationAdmits fakeRosterObservation = false := by decide
theorem termination_router_withholds_on_unsatisfied :
    terminationAdmits unsatisfiedObservation = false := by decide
theorem termination_router_withholds_on_abstain :
    terminationAdmits abstainObservation = false := by decide
theorem termination_router_withholds_on_invalid :
    terminationAdmits invalidObservation = false := by decide
theorem termination_router_withholds_on_missing :
    terminationAdmits missingObservation = false := by decide
theorem always_abstain_is_sound : Sound alwaysAbstain := by
  intro observation admitted
  simp [alwaysAbstain] at admitted
theorem always_abstain_is_strictly_below_optimal : StrictBelow alwaysAbstain terminationAdmits := by
  constructor
  · intro observation admitted
    simp [alwaysAbstain] at admitted
  · exact ⟨permittedObservation, by decide, rfl⟩
theorem majority_admit_is_strictly_above_optimal : StrictBelow terminationAdmits majorityAdmit := by
  constructor
  · intro observation admitted
    obtain ⟨roster, satisfied⟩ := (termination_admits_iff observation).mp admitted
    simp [majorityAdmit, (exact_roster_bool_iff observation.roster).2 roster,
      (seat_result_satisfied_bool_iff _).2 (satisfied .criterionEvidence),
      (seat_result_satisfied_bool_iff _).2 (satisfied .residualGap),
      (seat_result_satisfied_bool_iff _).2 (satisfied .claimIntegrity)]
  · exact ⟨unsatisfiedObservation, by decide, by decide⟩
theorem majority_admit_is_not_sound : Not (Sound majorityAdmit) := by
  intro sound
  have admitted : majorityAdmit unsatisfiedObservation = true := by decide
  have safe := sound unsatisfiedObservation admitted
  apply safe
  right
  refine ⟨.residualGap, ?_⟩
  simp [unsatisfiedObservation, completedTerminationResult, TerminationSeatResult.IsSatisfied]
theorem review_router_truth_table :
    reviewRouter (fun _ => .reject) = .fix /\ reviewRouter (fun _ => .approve) = .done /\
      reviewRouter (fun _ => .comment) = .userDecisionOrBoundedPass := by decide
def fixturePlanCompatibility : PlanCompatibility
  | .planA, .planB | .planB, .planA => true
  | first, second => first == second
def unanimousThinkingResults : ThinkingResults :=
  fun seat => completedThinkingResult seat .propose (some .planA) false
def compatibleThinkingResults : ThinkingResults := fun seat =>
  if seat == .teleology then completedThinkingResult seat .propose (some .planA) false
  else completedThinkingResult seat .revise (some .planB) false
def conflictingThinkingResults : ThinkingResults := fun seat =>
  if seat == .worth then completedThinkingResult seat .propose (some .planC) false
  else completedThinkingResult seat .propose (some .planA) false
def singlePerspectiveThinkingResults : ThinkingResults := fun seat =>
  completedThinkingResult seat .propose (some .planA) (seat == .teleology)
theorem thinking_panel_has_exactly_six_named_role_indices : Fintype.card ThinkingSeat = 6 := by
  decide
theorem review_triplet_has_exactly_three_named_role_indices : Fintype.card ReviewSeat = 3 := by
  decide
theorem design_row_unanimous_actionable_is_reachable :
    thinkingSituation fixturePlanCompatibility unanimousThinkingResults = .unanimousActionable /\
      designRouter (thinkingSituation fixturePlanCompatibility unanimousThinkingResults) =
        .implement := by decide
theorem design_row_compatible_disagreement_is_reachable :
    thinkingSituation fixturePlanCompatibility compatibleThinkingResults = .compatiblePlans /\
      designRouter (thinkingSituation fixturePlanCompatibility compatibleThinkingResults) =
        .metaLayerConvergence := by decide
theorem design_row_bounded_stall_is_reachable_from_conflicting_proposals :
    thinkingSituation fixturePlanCompatibility conflictingThinkingResults = .boundedStall /\
      designRouter (thinkingSituation fixturePlanCompatibility conflictingThinkingResults) =
        .abstainEscalate := by decide
theorem design_row_single_perspective_is_reachable :
    thinkingSituation fixturePlanCompatibility singlePerspectiveThinkingResults =
        .singlePerspective /\
      designRouter (thinkingSituation fixturePlanCompatibility singlePerspectiveThinkingResults) =
        .rejectFakeConsensus := by
  constructor
  · decide
  · exact design_router_rejects_single_perspective
def fixtureConfig : ProtocolConfig :=
  { eligible := fun _ _ => allEligible
    retryBudget := fun _ _ _ => 2
    sharedPassBudget := defaultSharedPassBudget
    ownerAuthorizedAboveDefault := false
    initialIsolation := .available }
theorem shared_pass_budget_default_is_five : fixtureConfig.sharedPassBudget = 5 := by decide
private theorem fixture_pass_budget_is_authorized : PassBudgetAuthorized fixtureConfig := by
  exact Or.inl (by decide)
theorem retry_budget_is_fixed_per_flight (stage role carrier) :
    fixtureConfig.retryBudget stage role carrier = 2 := by rfl
theorem bounded_pass_kinds_have_only_legal_loci :
    BoundedPassKind.LegalAt .metaLayerConvergence .metaJudge /\
      BoundedPassKind.LegalAt .repeatedReview .fixOrDone /\
      BoundedPassKind.LegalAt .fixPass .fixOrDone /\
      BoundedPassKind.LegalAt .terminationGate .fixOrDone := by
  simp [BoundedPassKind.LegalAt]
def thinkingAbstainEvents : List Event := [.abstain .thinkingPanelWorkers]
def thinkingExhaustedStart : ProtocolState :=
  { stage := .thinkingPanelWorkers, phase := .live, passesUsed := 0, isolation := .available
    designSituation := none, reviewExit := none, terminationExit := none
    attemptedFlights := {
      flightKey .thinkingPanelWorkers .teleology .codexCli,
      flightKey .thinkingPanelWorkers .teleology .nyxidOracle,
      flightKey .thinkingPanelWorkers .teleology .isolatedTokenSubagent }
    remainingFlights := ((Finset.univ.erase
      (flightKey .thinkingPanelWorkers .teleology .codexCli)).erase
      (flightKey .thinkingPanelWorkers .teleology .nyxidOracle)).erase
      (flightKey .thinkingPanelWorkers .teleology .isolatedTokenSubagent) }
def thinkingAbstainFinal : ProtocolState :=
  { thinkingExhaustedStart with phase := .abstained }
def thinkingAbstainExecution :
    Execution inlineConsensusModel fixtureConfig thinkingExhaustedStart
      thinkingAbstainEvents thinkingAbstainFinal := by
  refine Execution.cons ?_ (Execution.nil _ fixture_pass_budget_is_authorized)
  apply ProtocolStep.abstain thinkingExhaustedStart fixture_pass_budget_is_authorized rfl
  apply AbstainCondition.carrierExhausted .teleology
  · exact ⟨.codexCli, by
      simp [thinkingExhaustedStart, CarrierLegalAt, SeatRole.LegalAt,
        SeatRole.IsThinking]⟩
  · decide
theorem thinking_abstain_skips_all_dependent_stages :
    Execution inlineConsensusModel fixtureConfig thinkingExhaustedStart
      thinkingAbstainEvents thinkingAbstainFinal /\
    forall event, event ∈ thinkingAbstainEvents -> event = .abstain .thinkingPanelWorkers := by
  refine ⟨thinkingAbstainExecution, ?_⟩
  intro event member
  simpa [thinkingAbstainEvents] using member
theorem abstained_state_has_no_successor
    (config : ProtocolConfig) (state : ProtocolState) (abstained : state.phase = .abstained) :
    forall event final, Not (ProtocolStep config state event final) := by
  intro event final step
  cases step <;> simp_all
def exhaustedConfig : ProtocolConfig :=
  { eligible := fun _ _ _ => false, retryBudget := fun _ _ _ => 1
    sharedPassBudget := defaultSharedPassBudget
    ownerAuthorizedAboveDefault := false, initialIsolation := .available }
def immediateWorkerModeState : ProtocolState :=
  { initialState exhaustedConfig with stage := .chooseWorkerMode }
def immediateAbstainFinal : ProtocolState :=
  { immediateWorkerModeState with phase := .abstained }
def immediateAbstainRun : MaximalRun inlineConsensusModel exhaustedConfig where
  events := [.advance .intake .chooseWorkerMode, .abstain .chooseWorkerMode]
  finalState := immediateAbstainFinal
  execution := by
    refine Execution.cons (middle := immediateWorkerModeState) ?_ ?_
    · exact ProtocolStep.advance (initialState exhaustedConfig) .chooseWorkerMode
        (Or.inl (by decide)) rfl rfl (.intake rfl) rfl
    · refine Execution.cons ?_ (Execution.nil _ (Or.inl (by decide)))
      apply ProtocolStep.abstain immediateWorkerModeState (Or.inl (by decide)) rfl
      apply AbstainCondition.carrierExhausted .teleology
      · exact ⟨.codexCli, by
          simp [immediateWorkerModeState, CarrierLegalAt, SeatRole.LegalAt,
            SeatRole.IsThinking]⟩
      · decide
  maximal := by
    intro event state step
    cases step <;>
      simp [immediateAbstainFinal, immediateWorkerModeState, initialState] at *
def maximal_run_fixture_is_nonempty : MaximalRun inlineConsensusModel exhaustedConfig :=
  immediateAbstainRun
def unavailableIsolationConfig : ProtocolConfig :=
  { fixtureConfig with initialIsolation := .unavailable }
private theorem unavailable_isolation_budget_is_authorized :
    PassBudgetAuthorized unavailableIsolationConfig := by
  exact Or.inl (by
    norm_num [unavailableIsolationConfig, fixtureConfig, defaultSharedPassBudget])
def unavailableIsolationFinal : ProtocolState :=
  { initialState unavailableIsolationConfig with phase := .abstained }
def unavailableIsolationExecution :
    Execution inlineConsensusModel unavailableIsolationConfig
      (initialState unavailableIsolationConfig) [.abstain .intake] unavailableIsolationFinal := by
  refine Execution.cons ?_ (Execution.nil _ unavailable_isolation_budget_is_authorized)
  apply ProtocolStep.abstain (initialState unavailableIsolationConfig)
    unavailable_isolation_budget_is_authorized rfl
  exact AbstainCondition.isolationUnavailable rfl
theorem unavailable_isolation_reaches_abstained_state :
    Execution inlineConsensusModel unavailableIsolationConfig
      (initialState unavailableIsolationConfig) [.abstain .intake] unavailableIsolationFinal :=
  unavailableIsolationExecution
theorem unavailable_isolation_cannot_finish (state : ProtocolState)
    (unavailable : state.isolation = .unavailable) :
    forall final, Not (ProtocolStep fixtureConfig state .finish final) := by
  intro final step
  cases step with
  | finish budget live atEnd isolated reviewDone permitted => simp_all
theorem unavailable_isolation_cannot_retry_flight (state : ProtocolState)
    (unavailable : state.isolation = .unavailable) (role carrier attempts) :
    forall final, Not (ProtocolStep fixtureConfig state
      (.flightFailure state.stage role carrier attempts) final) := by
  intro final step
  cases step with
  | flightFailure role carrier attempts budget live isolated selected worker available
      positive within => simp_all
theorem unavailable_isolation_cannot_take_bounded_pass (state : ProtocolState)
    (unavailable : state.isolation = .unavailable) (kind) :
    forall final, Not (ProtocolStep fixtureConfig state (.boundedPass state.stage kind) final) := by
  intro final step
  cases step <;> simp_all
theorem unavailable_isolation_cannot_fix_and_review (state : ProtocolState)
    (unavailable : state.isolation = .unavailable) :
    forall final,
      Not (ProtocolStep fixtureConfig state (.boundedPass state.stage .fixPass) final) := by
  intro final step
  cases step
  all_goals simp_all
theorem unavailable_isolation_allows_only_abstain (config : ProtocolConfig)
    (state final : ProtocolState) (event : Event) (unavailable : state.isolation = .unavailable)
    (step : ProtocolStep config state event final) :
    exists stage, event = .abstain stage := by
  cases step <;> simp_all
def terminationEvaluationStart : ProtocolState :=
  { initialState fixtureConfig with
    stage := .fixOrDone
    passesUsed := 4
    reviewExit := some .done
    reviewEpoch := some 0 }
def terminationEvaluationFinal : ProtocolState :=
  { terminationEvaluationStart with
    passesUsed := 5
    attemptedFlights := terminationEvaluationStart.attemptedFlights ∪
      permittedObservation.attemptKeys terminationEvaluationStart
    terminationExit := some .permitClaim
    terminationEpoch := some 0 }
private def terminationEvaluationAuthorized :
    permittedObservation.DispatchAuthorized fixtureConfig terminationEvaluationStart := by
  intro seat
  cases seat <;>
    refine ⟨by
      simp [terminationEvaluationStart, CarrierLegalAt, SeatRole.LegalAt,
        TerminationSeat.role, SeatRole.IsTermination], rfl, rfl, by decide, by decide, ?_⟩ <;>
    exact codex_completion_requires_all_five_conjuncts
def terminationEvaluationStep : ProtocolStep fixtureConfig terminationEvaluationStart
    (.boundedPass .fixOrDone .terminationGate) terminationEvaluationFinal := by
  exact ProtocolStep.terminationGate terminationEvaluationStart fixture_pass_budget_is_authorized
    rfl rfl rfl rfl rfl .terminationCandidate rfl permittedObservation
    terminationEvaluationAuthorized (by decide) .permitClaim rfl (by decide)
theorem termination_roster_evaluation_consumes_exactly_one_shared_pass :
    ProtocolStep fixtureConfig terminationEvaluationStart
        (.boundedPass .fixOrDone .terminationGate) terminationEvaluationFinal /\
      terminationEvaluationFinal.passesUsed = terminationEvaluationStart.passesUsed + 1 /\
      terminationEvaluationFinal.terminationExit = some .permitClaim := by
  exact ⟨terminationEvaluationStep, rfl, rfl⟩
def terminationFinishedState : ProtocolState :=
  { terminationEvaluationFinal with phase := .terminal }
theorem termination_finish_requires_and_uses_recorded_permit :
    Not (exists final, ProtocolStep fixtureConfig terminationEvaluationStart .finish final) /\
      ProtocolStep fixtureConfig terminationEvaluationFinal .finish terminationFinishedState := by
  constructor
  · rintro ⟨final, step⟩
    cases step with
    | finish budget live atEnd isolated reviewDone reviewCurrent permitted permitCurrent =>
        simp [terminationEvaluationStart, initialState] at permitted
  · exact ProtocolStep.finish terminationEvaluationFinal fixture_pass_budget_is_authorized
      rfl rfl rfl rfl rfl rfl rfl
def terminationBudgetCeilingState : ProtocolState :=
  { terminationEvaluationStart with passesUsed := fixtureConfig.sharedPassBudget }
theorem termination_roster_evaluation_is_blocked_at_budget_ceiling :
    forall final, Not (ProtocolStep fixtureConfig terminationBudgetCeilingState
      (.boundedPass .fixOrDone .terminationGate) final) := by
  intro final step
  cases step <;> simp_all [terminationBudgetCeilingState, fixtureConfig]
def unauthorizedOverBudgetConfig : ProtocolConfig :=
  { fixtureConfig with sharedPassBudget := 6, ownerAuthorizedAboveDefault := false }
theorem unauthorized_over_budget_config_is_rejected :
    Not (PassBudgetAuthorized unauthorizedOverBudgetConfig) := by
  intro authorized
  rcases authorized with withinDefault | ownerAuthorized
  · norm_num [unauthorizedOverBudgetConfig, fixtureConfig,
      defaultSharedPassBudget] at withinDefault
  · simp [unauthorizedOverBudgetConfig, fixtureConfig] at ownerAuthorized
theorem unauthorized_over_budget_config_has_no_transition :
    forall start event final,
      Not (ProtocolStep unauthorizedOverBudgetConfig start event final) := by
  intro start event final step
  cases step <;>
    simp_all [PassBudgetAuthorized, unauthorizedOverBudgetConfig, fixtureConfig,
      defaultSharedPassBudget]
theorem unauthorized_over_budget_config_has_no_execution :
    forall start events final,
      Not (Execution inlineConsensusModel unauthorizedOverBudgetConfig start events final) := by
  intro start events final execution
  induction execution with
  | nil state authorized => exact unauthorized_over_budget_config_is_rejected authorized
  | cons step rest ih => exact ih
def allRejectReviewResults : ReviewResults :=
  fun seat => completedReviewResult seat .reject
theorem all_reject_results_route_to_fix :
    reviewRouter (reviewObservation allRejectReviewResults) = .fix := by decide
def allRejectReviewStart : ProtocolState :=
  { initialState fixtureConfig with stage := .reviewTripletWorkers }
def allRejectReviewCondition : AdvanceCondition fixtureConfig allRejectReviewStart :=
  .review rfl allRejectReviewResults (by
    intro seat
    cases seat <;>
      refine ⟨by
        simp [allRejectReviewStart, allRejectReviewResults, completedReviewResult,
          ReviewSeatResult.evidence, CarrierLegalAt, SeatRole.LegalAt,
          ReviewSeat.role, SeatRole.IsReview],
        rfl, rfl, by decide, by decide, ?_⟩ <;>
      exact codex_completion_requires_all_five_conjuncts)
def allRejectReviewFinal : ProtocolState :=
  allRejectReviewCondition.nextState .fixOrDone
theorem all_reject_review_exit_is_retained_in_state :
    allRejectReviewFinal.reviewExit = some .fix := by rfl
def allRejectReviewExecution :
    Execution inlineConsensusModel fixtureConfig allRejectReviewStart
      [.advance .reviewTripletWorkers .fixOrDone] allRejectReviewFinal := by
  refine Execution.cons ?_ (Execution.nil _ fixture_pass_budget_is_authorized)
  have successor : allRejectReviewStart.stage.Successor .fixOrDone := by rfl
  exact ProtocolStep.advance allRejectReviewStart .fixOrDone
    fixture_pass_budget_is_authorized rfl rfl allRejectReviewCondition successor
theorem all_reject_review_cannot_reach_terminal_claim_without_fix :
    Not (exists final, ProtocolStep fixtureConfig allRejectReviewFinal .finish final) := by
  rintro ⟨final, step⟩
  cases step with
  | finish budget live atEnd isolated reviewDone permitted =>
      have retained := all_reject_review_exit_is_retained_in_state
      rw [retained] at reviewDone
      cases reviewDone
def completedImplementationResult : CompletedSeatResult :=
  { view := ⟨.complete, .implementation, .repoPriorExposed⟩
    carrier := .codexCli
    workerCarrier := by decide
    completionObservation := completeCodexObservation
    complete := codex_completion_requires_all_five_conjuncts
    exposureMatches := rfl }
def completedNyxidImplementationResult : CompletedSeatResult :=
  { view := ⟨.complete, .implementation, .externalPriorExposed⟩
    carrier := .nyxidOracle
    workerCarrier := by decide
    completionObservation := completeNyxidObservation
    complete := nyxid_completion_uses_structured_terminal_status_without_sentinel
    exposureMatches := rfl }
def implementationSelectionStart : ProtocolState :=
  { initialState fixtureConfig with stage := .implementationWorker }
theorem lower_priority_carrier_cannot_displace_available_codex :
    Not (SelectedWorkerEvidence fixtureConfig implementationSelectionStart .implementation
      completedNyxidImplementationResult) := by
  intro authorized
  have selected := authorized.selected
  have wrong : selectCarrier allEligible {} = .nyxidOracle := by
    simpa [fixtureConfig, implementationSelectionStart, initialState, triedAt,
      completedNyxidImplementationResult] using selected
  rw [carrier_selection_starts_with_codex] at wrong
  contradiction
theorem implementation_role_cannot_justify_intake_exhaustion :
    Not (exists carrier, CarrierLegalAt (initialState fixtureConfig).stage
      .implementation carrier) := by
  rintro ⟨carrier, legal⟩
  simp [CarrierLegalAt, SeatRole.LegalAt, initialState] at legal
def allApproveReviewResults : ReviewResults :=
  fun seat => completedReviewResult seat .approve
def stalePermitFixStart : ProtocolState :=
  { terminationEvaluationFinal with
    passesUsed := 3
    reviewExit := some .fix }
private def stalePermitImplementationAuthorized :
    SelectedWorkerEvidence fixtureConfig stalePermitFixStart .implementation
      completedImplementationResult := by
  refine ⟨?_, rfl, rfl, ?_, ?_, codex_completion_requires_all_five_conjuncts⟩
  · simp [completedImplementationResult, stalePermitFixStart, terminationEvaluationFinal,
      terminationEvaluationStart, CarrierLegalAt, SeatRole.LegalAt]
  · decide
  · decide
private def stalePermitReviewAuthorized :
    allApproveReviewResults.DispatchAuthorized fixtureConfig stalePermitFixStart := by
  intro seat
  cases seat <;>
    refine ⟨by
      simp [stalePermitFixStart, terminationEvaluationFinal, terminationEvaluationStart,
        allApproveReviewResults, completedReviewResult, ReviewSeatResult.evidence,
        CarrierLegalAt, SeatRole.LegalAt, ReviewSeat.role, SeatRole.IsReview],
      rfl, rfl, by decide, by decide,
      codex_completion_requires_all_five_conjuncts⟩
def stalePermitFixFinal : ProtocolState :=
  { stalePermitFixStart with
    passesUsed := stalePermitFixStart.passesUsed + 1
    attemptedFlights := insert
      (flightKey stalePermitFixStart.stage .implementation completedImplementationResult.carrier)
      (stalePermitFixStart.attemptedFlights ∪
        allApproveReviewResults.attemptKeys stalePermitFixStart)
    artifactEpoch := stalePermitFixStart.artifactEpoch + 1
    reviewExit := some (reviewRouter (reviewObservation allApproveReviewResults))
    reviewEpoch := some (stalePermitFixStart.artifactEpoch + 1)
    terminationExit := none
    terminationEpoch := none }
def stalePermitFixStep : ProtocolStep fixtureConfig stalePermitFixStart
    (.boundedPass .fixOrDone .fixPass) stalePermitFixFinal := by
  exact ProtocolStep.fixAndReview stalePermitFixStart fixture_pass_budget_is_authorized
    rfl rfl rfl rfl .repair rfl completedImplementationResult
    stalePermitImplementationAuthorized allApproveReviewResults
    stalePermitReviewAuthorized (by decide)
theorem any_fix_after_a_permitting_evaluation_invalidates_that_permit :
    ProtocolStep fixtureConfig stalePermitFixStart
        (.boundedPass .fixOrDone .fixPass) stalePermitFixFinal /\
      stalePermitFixStart.terminationExit = some .permitClaim /\
      stalePermitFixFinal.terminationExit = none /\
      forall final, Not (ProtocolStep fixtureConfig stalePermitFixFinal .finish final) := by
  refine ⟨stalePermitFixStep, rfl, rfl, ?_⟩
  exact (no_stale_termination_permit_after_fix fixtureConfig stalePermitFixStart
    stalePermitFixFinal stalePermitFixStep).2.2
theorem old_all_reject_stale_permit_sequence_is_unreachable :
    forall final, Not (ProtocolStep fixtureConfig allRejectReviewFinal
      (.boundedPass .fixOrDone .terminationGate) final) := by
  intro final step
  have required := termination_gate_requires_current_done_review step
  rw [all_reject_review_exit_is_retained_in_state] at required
  cases required.1
theorem successful_fix_consumes_implementation_carrier :
    flightKey .fixOrDone .implementation .codexCli ∈ stalePermitFixFinal.attemptedFlights := by
  decide
theorem repeated_carrier_attempt_after_success_is_rejected :
    Not (SelectedWorkerEvidence fixtureConfig stalePermitFixFinal .implementation
      completedImplementationResult) := by
  intro authorized
  apply authorized.untried
  decide
def designImplementStart : ProtocolState :=
  { initialState fixtureConfig with
    stage := .metaJudge
    designSituation := some .unanimousActionable }
def designImplementCondition : AdvanceCondition fixtureConfig designImplementStart :=
  .metaJudge rfl .unanimousActionable rfl rfl .advance
def designImplementFinal : ProtocolState :=
  designImplementCondition.nextState .implementationWorker
def designImplementStep : ProtocolStep fixtureConfig designImplementStart
    (.advance .metaJudge .implementationWorker) designImplementFinal := by
  exact .advance designImplementStart .implementationWorker fixture_pass_budget_is_authorized
    rfl rfl designImplementCondition rfl
def designCompatibleStart : ProtocolState :=
  { initialState fixtureConfig with
    stage := .metaJudge
    designSituation := some .compatiblePlans }
def designConvergenceFinal : ProtocolState :=
  { designCompatibleStart with
    passesUsed := 1
    designSituation := some .unanimousActionable }
def designConvergenceStep : ProtocolStep fixtureConfig designCompatibleStart
    (.boundedPass .metaJudge .metaLayerConvergence) designConvergenceFinal := by
  exact .designConvergence designCompatibleStart .planA fixture_pass_budget_is_authorized
    rfl rfl rfl rfl rfl (.converge (.implementable .planA)) rfl (by decide)
def designConvergenceExhaustedFinal : ProtocolState :=
  { designCompatibleStart with passesUsed := 1, phase := .abstained }
def designConvergenceExhaustedStep : ProtocolStep fixtureConfig designCompatibleStart
    (.boundedPass .metaJudge .metaLayerConvergence) designConvergenceExhaustedFinal := by
  exact .designConvergenceExhausted designCompatibleStart fixture_pass_budget_is_authorized
    rfl rfl rfl rfl rfl (.converge .exhausted) rfl (by decide)
def designStallStart : ProtocolState :=
  { initialState fixtureConfig with stage := .metaJudge, designSituation := some .boundedStall }
def designStallFinal : ProtocolState := { designStallStart with phase := .abstained }
def designStallStep : ProtocolStep fixtureConfig designStallStart
    (.abstain .metaJudge) designStallFinal := by
  exact .abstain designStallStart fixture_pass_budget_is_authorized rfl
    (.stageOutcome (.designStall designStallStart rfl .boundedStall rfl rfl .abstainEscalate))
def designFakeConsensusStart : ProtocolState :=
  { initialState fixtureConfig with
    stage := .metaJudge, designSituation := some .singlePerspective }
def designFakeConsensusFinal : ProtocolState :=
  { designFakeConsensusStart with phase := .abstained }
def designFakeConsensusStep : ProtocolStep fixtureConfig designFakeConsensusStart
    (.abstain .metaJudge) designFakeConsensusFinal := by
  exact .abstain designFakeConsensusStart fixture_pass_budget_is_authorized rfl
    (.stageOutcome (.designFakeConsensus designFakeConsensusStart rfl .singlePerspective
      rfl rfl .rejectFakeConsensus))
def allCommentReviewStart : ProtocolState :=
  { initialState fixtureConfig with
    stage := .fixOrDone
    reviewExit := some .userDecisionOrBoundedPass
    reviewEpoch := some 0 }
private def allCommentRepeatedReviewAuthorized :
    allApproveReviewResults.DispatchAuthorized fixtureConfig allCommentReviewStart := by
  intro seat
  cases seat <;>
    refine ⟨by
      simp [allCommentReviewStart, allApproveReviewResults, completedReviewResult,
        ReviewSeatResult.evidence, CarrierLegalAt, SeatRole.LegalAt,
        ReviewSeat.role, SeatRole.IsReview], rfl, rfl, by decide, by decide,
      codex_completion_requires_all_five_conjuncts⟩
def allCommentRepeatedReviewFinal : ProtocolState :=
  { allCommentReviewStart with
    passesUsed := 1
    attemptedFlights := allCommentReviewStart.attemptedFlights ∪
      allApproveReviewResults.attemptKeys allCommentReviewStart
    reviewExit := some .done
    reviewEpoch := some 0
    terminationExit := none
    terminationEpoch := none }
def allCommentRepeatedReviewStep : ProtocolStep fixtureConfig allCommentReviewStart
    (.boundedPass .fixOrDone .repeatedReview) allCommentRepeatedReviewFinal := by
  exact .repeatedReview allCommentReviewStart fixture_pass_budget_is_authorized rfl rfl rfl rfl
    (.anotherBoundedPass) rfl allApproveReviewResults allCommentRepeatedReviewAuthorized (by decide)
def allCommentUserDecisionFinal : ProtocolState :=
  { allCommentReviewStart with phase := .abstained }
def allCommentUserDecisionStep : ProtocolStep fixtureConfig allCommentReviewStart
    (.abstain .fixOrDone) allCommentUserDecisionFinal := by
  exact .abstain allCommentReviewStart fixture_pass_budget_is_authorized rfl
    (.stageOutcome (.reviewUserDecision allCommentReviewStart rfl rfl .requestUserDecision))
theorem design_and_review_router_exits_have_executable_transitions :
    Nonempty (DesignRouteTransition .implement) /\
      Nonempty (DesignRouteTransition .metaLayerConvergence) /\
      Nonempty (DesignRouteTransition .abstainEscalate) /\
      Nonempty (DesignRouteTransition .rejectFakeConsensus) /\
      Nonempty (ReviewRouteTransition .fix) /\
      Nonempty (ReviewRouteTransition .done) /\
      Nonempty (ReviewRouteTransition .userDecisionOrBoundedPass) := by
  exact ⟨⟨.implement designImplementStep⟩,
    ⟨.convergenceSucceeded designConvergenceStep rfl⟩,
    ⟨.stalled designStallStep rfl⟩, ⟨.fakeConsensus designFakeConsensusStep rfl⟩,
    ⟨.repair stalePermitFixStep⟩, ⟨.terminationCandidate terminationEvaluationStep⟩,
    ⟨.repeatedPass allCommentRepeatedReviewStep⟩⟩
theorem convergence_and_all_comment_branches_are_both_executable :
    Nonempty (DesignRouteTransition .metaLayerConvergence) /\
      Nonempty (ReviewRouteTransition .userDecisionOrBoundedPass) :=
  ⟨⟨.convergenceExhausted designConvergenceExhaustedStep rfl⟩,
    ⟨.userDecision allCommentUserDecisionStep⟩⟩
def terminationRoutingStart : ProtocolState :=
  { initialState fixtureConfig with
    stage := .fixOrDone
    reviewExit := some .done
    reviewEpoch := some 0 }
private def completedTerminationAuthorizedAtRoutingStart (seat : TerminationSeat)
    (verdict : TerminationVerdict) :
    (completedTerminationResult seat verdict).DispatchAuthorized
      fixtureConfig terminationRoutingStart := by
  cases seat <;>
    refine ⟨by
      simp [terminationRoutingStart, CarrierLegalAt, SeatRole.LegalAt,
        TerminationSeat.role, SeatRole.IsTermination], rfl, rfl,
      by decide, by decide, codex_completion_requires_all_five_conjuncts⟩
private def fakeRoutingAuthorized :
    fakeRosterObservation.DispatchAuthorized fixtureConfig terminationRoutingStart := by
  intro seat
  simpa [fakeRosterObservation, allSatisfiedResults] using
    completedTerminationAuthorizedAtRoutingStart seat .satisfied
private def unsatisfiedRoutingAuthorized :
    unsatisfiedObservation.DispatchAuthorized fixtureConfig terminationRoutingStart := by
  intro seat
  cases seat
  · exact completedTerminationAuthorizedAtRoutingStart _ .satisfied
  · exact completedTerminationAuthorizedAtRoutingStart _ .unsatisfied
  · exact completedTerminationAuthorizedAtRoutingStart _ .satisfied
private def abstainRoutingAuthorized :
    abstainObservation.DispatchAuthorized fixtureConfig terminationRoutingStart := by
  intro seat
  cases seat
  · exact completedTerminationAuthorizedAtRoutingStart _ .satisfied
  · exact completedTerminationAuthorizedAtRoutingStart _ .abstain
  · exact completedTerminationAuthorizedAtRoutingStart _ .satisfied
private def invalidRoutingAuthorized :
    invalidObservation.DispatchAuthorized fixtureConfig terminationRoutingStart := by
  intro seat
  cases seat
  · exact completedTerminationAuthorizedAtRoutingStart _ .satisfied
  · trivial
  · exact completedTerminationAuthorizedAtRoutingStart _ .satisfied
private def missingRoutingAuthorized :
    missingObservation.DispatchAuthorized fixtureConfig terminationRoutingStart := by
  intro seat
  cases seat
  · exact completedTerminationAuthorizedAtRoutingStart _ .satisfied
  · trivial
  · exact completedTerminationAuthorizedAtRoutingStart _ .satisfied
def terminationFakeFinal : ProtocolState :=
  { terminationRoutingStart with
    passesUsed := 1
    attemptedFlights := terminationRoutingStart.attemptedFlights ∪
      fakeRosterObservation.attemptKeys terminationRoutingStart
    phase := .abstained
    terminationExit := some .rejectFakeConsensus
    terminationEpoch := none }
def terminationFakeStep : ProtocolStep fixtureConfig terminationRoutingStart
    (.boundedPass .fixOrDone .terminationGate) terminationFakeFinal := by
  exact .terminationFakeConsensus terminationRoutingStart fixture_pass_budget_is_authorized
    rfl rfl rfl rfl rfl fakeRosterObservation fakeRoutingAuthorized (by decide)
    .rejectFakeConsensus rfl (by decide)
def terminationUnsatisfiedFinal : ProtocolState :=
  { terminationRoutingStart with
    passesUsed := 1
    attemptedFlights := terminationRoutingStart.attemptedFlights ∪
      unsatisfiedObservation.attemptKeys terminationRoutingStart
    reviewExit := some .fix
    reviewEpoch := none
    terminationExit := some .continueAgainstGap
    terminationEpoch := none }
def terminationUnsatisfiedStep : ProtocolStep fixtureConfig terminationRoutingStart
    (.boundedPass .fixOrDone .terminationGate) terminationUnsatisfiedFinal := by
  exact .terminationGapEngineering terminationRoutingStart fixture_pass_budget_is_authorized
    rfl rfl rfl rfl rfl unsatisfiedObservation unsatisfiedRoutingAuthorized (by decide)
    (.continueAgainstGap .engineering) rfl (by decide)
def terminationAbstainFinal : ProtocolState :=
  { terminationRoutingStart with
    passesUsed := 1
    attemptedFlights := terminationRoutingStart.attemptedFlights ∪
      abstainObservation.attemptKeys terminationRoutingStart
    phase := .abstained
    terminationExit := some .escalateEvidenceGap
    terminationEpoch := none }
def terminationAbstainStep : ProtocolStep fixtureConfig terminationRoutingStart
    (.boundedPass .fixOrDone .terminationGate) terminationAbstainFinal := by
  exact .terminationEvidenceGap terminationRoutingStart fixture_pass_budget_is_authorized
    rfl rfl rfl rfl rfl abstainObservation abstainRoutingAuthorized (by decide)
    .escalateEvidenceGap rfl (by decide)
def terminationInvalidFinal : ProtocolState :=
  { terminationAbstainFinal with
    attemptedFlights := terminationRoutingStart.attemptedFlights ∪
      invalidObservation.attemptKeys terminationRoutingStart }
def terminationInvalidStep : ProtocolStep fixtureConfig terminationRoutingStart
    (.boundedPass .fixOrDone .terminationGate) terminationInvalidFinal := by
  exact .terminationEvidenceGap terminationRoutingStart fixture_pass_budget_is_authorized
    rfl rfl rfl rfl rfl invalidObservation invalidRoutingAuthorized (by decide)
    .escalateEvidenceGap rfl (by decide)
def terminationMissingFinal : ProtocolState :=
  { terminationAbstainFinal with
    attemptedFlights := terminationRoutingStart.attemptedFlights ∪
      missingObservation.attemptKeys terminationRoutingStart }
def terminationMissingStep : ProtocolStep fixtureConfig terminationRoutingStart
    (.boundedPass .fixOrDone .terminationGate) terminationMissingFinal := by
  exact .terminationEvidenceGap terminationRoutingStart fixture_pass_budget_is_authorized
    rfl rfl rfl rfl rfl missingObservation missingRoutingAuthorized (by decide)
    .escalateEvidenceGap rfl (by decide)
theorem termination_nonpermit_rows_have_prescribed_transitions :
    ProtocolStep fixtureConfig terminationRoutingStart
        (.boundedPass .fixOrDone .terminationGate) terminationFakeFinal /\
      ProtocolStep fixtureConfig terminationRoutingStart
        (.boundedPass .fixOrDone .terminationGate) terminationUnsatisfiedFinal /\
      ProtocolStep fixtureConfig terminationRoutingStart
        (.boundedPass .fixOrDone .terminationGate) terminationAbstainFinal /\
      ProtocolStep fixtureConfig terminationRoutingStart
        (.boundedPass .fixOrDone .terminationGate) terminationInvalidFinal /\
      ProtocolStep fixtureConfig terminationRoutingStart
        (.boundedPass .fixOrDone .terminationGate) terminationMissingFinal :=
  ⟨terminationFakeStep, terminationUnsatisfiedStep, terminationAbstainStep,
    terminationInvalidStep, terminationMissingStep⟩
theorem router_transitions_are_exhaustive : RouterTransitionsExhaustive := by
  refine ⟨?_, ?_, ?_⟩
  · intro exit
    cases exit
    · exact ⟨.implement designImplementStep⟩
    · exact ⟨.convergenceSucceeded designConvergenceStep rfl⟩
    · exact ⟨.stalled designStallStep rfl⟩
    · exact ⟨.fakeConsensus designFakeConsensusStep rfl⟩
  · intro exit
    cases exit
    · exact ⟨.repair stalePermitFixStep⟩
    · exact ⟨.terminationCandidate terminationEvaluationStep⟩
    · exact ⟨.repeatedPass allCommentRepeatedReviewStep⟩
  · intro exit
    cases exit
    · exact ⟨.fakeConsensus terminationFakeStep rfl⟩
    · exact ⟨.permit terminationEvaluationStep rfl⟩
    · exact ⟨.continueAgainstGap terminationUnsatisfiedStep rfl⟩
    · exact ⟨.evidenceGap terminationAbstainStep rfl⟩
end D5.S0.History.Consensus.InlineConsensusProtocolFixtures
