/- GID: D5/S0/History/Consensus/InlineConsensusProtocolFixtures
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusProtocolFixtures
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Named protocol executions and aggregate mutation pins for inline consensus. -/
import D5.S0.History.Consensus.InlineConsensusOptimality
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
      BoundedPassKind.LegalAt .repeatedReview .reviewTripletWorkers /\
      BoundedPassKind.LegalAt .fixPass .fixOrDone /\
      BoundedPassKind.LegalAt .terminationGate .fixOrDone := by
  simp [BoundedPassKind.LegalAt]
def thinkingAbstainEvents : List Event := [.abstain .thinkingPanelWorkers]
def thinkingExhaustedStart : ProtocolState :=
  { stage := .thinkingPanelWorkers, phase := .live, passesUsed := 0, isolation := .available
    designSituation := none, reviewExit := none, terminationExit := none
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
  decide
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
def immediateAbstainFinal : ProtocolState :=
  { initialState exhaustedConfig with phase := .abstained }
def immediateAbstainRun : MaximalRun inlineConsensusModel exhaustedConfig where
  events := [.abstain .intake]
  finalState := immediateAbstainFinal
  execution := by
    refine Execution.cons ?_ (Execution.nil _ (Or.inl (by decide)))
    apply ProtocolStep.abstain (initialState exhaustedConfig) (Or.inl (by decide)) rfl
    apply AbstainCondition.carrierExhausted .implementation
    decide
  maximal := by
    intro event state step
    cases step <;> simp [immediateAbstainFinal, initialState] at *
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
  cases step <;> simp_all
theorem unavailable_isolation_allows_only_abstain (config : ProtocolConfig)
    (state final : ProtocolState) (event : Event) (unavailable : state.isolation = .unavailable)
    (step : ProtocolStep config state event final) :
    exists stage, event = .abstain stage := by
  cases step <;> simp_all
def terminationEvaluationStart : ProtocolState :=
  { initialState fixtureConfig with
    stage := .fixOrDone
    passesUsed := 4
    reviewExit := some .done }
def terminationEvaluationFinal : ProtocolState :=
  { terminationEvaluationStart with
    passesUsed := 5
    terminationExit := some .permitClaim }
def terminationEvaluationStep : ProtocolStep fixtureConfig terminationEvaluationStart
    (.boundedPass .fixOrDone .terminationGate) terminationEvaluationFinal := by
  exact ProtocolStep.terminationGate terminationEvaluationStart fixture_pass_budget_is_authorized
    rfl rfl rfl permittedObservation (by decide)
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
    | finish budget live atEnd isolated reviewDone permitted =>
        simp [terminationEvaluationStart, initialState] at permitted
  · exact ProtocolStep.finish terminationEvaluationFinal fixture_pass_budget_is_authorized
      rfl rfl rfl rfl rfl
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
  .review rfl allRejectReviewResults
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
inductive ClauseId | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10
  deriving DecidableEq, Fintype, Repr
/-- This indexes the model's named objects. It does not prove correspondence to external prose. -/
def ClauseObject : ClauseId -> Prop
  | .s1 => Stage.next .intake = some .chooseWorkerMode /\
      Stage.next .chooseWorkerMode = some .thinkingPanelWorkers /\
      Stage.next .thinkingPanelWorkers = some .metaJudge /\
      Stage.next .metaJudge = some .implementationWorker /\
      Stage.next .implementationWorker = some .reviewTripletWorkers /\
      Stage.next .reviewTripletWorkers = some .fixOrDone /\ Stage.next .fixOrDone = none
  | .s2 => (Carrier.priorityRank .codexCli = 0 /\
      Carrier.priorityRank .nyxidOracle = 1 /\
      Carrier.priorityRank .isolatedTokenSubagent = 2 /\
      Carrier.priorityRank .abstain = 3) /\
      selectCarrier allEligible {} = .codexCli /\
      selectCarrier allEligible {.codexCli} = .nyxidOracle /\
      selectCarrier (fun _ => false) {} = .abstain
  | .s3 => forall stage role carrier, fixtureConfig.retryBudget stage role carrier = 2
  | .s4 => Complete .codexCli completeCodexObservation /\
      Complete .nyxidOracle completeNyxidObservation /\
      Complete .isolatedTokenSubagent completeSubagentObservation /\
      Not (Complete .nyxidOracle completeCodexObservation) /\
      Not (Complete .codexCli completeNyxidObservation)
  | .s5 => Execution inlineConsensusModel fixtureConfig thinkingExhaustedStart
      thinkingAbstainEvents thinkingAbstainFinal /\
      forall event, event ∈ thinkingAbstainEvents -> event = .abstain .thinkingPanelWorkers
  | .s6 => forall config state final event, state.isolation = .unavailable ->
      ProtocolStep config state event final -> exists stage, event = .abstain stage
  | .s7 => (priorExposure .codexCli = .repoPriorExposed /\
      priorExposure .nyxidOracle = .externalPriorExposed /\
      priorExposure .isolatedTokenSubagent = .callerPriorExposed /\
      priorExposure .abstain = .noCarrier) /\
      priorExposure .codexCli != priorExposure .nyxidOracle /\
      forall latent, correlatedConclusion .codexCli latent =
        correlatedConclusion .nyxidOracle latent
  | .s8 => designRouter .singlePerspective = .rejectFakeConsensus /\
      thinkingSituation fixturePlanCompatibility unanimousThinkingResults = .unanimousActionable /\
      thinkingSituation fixturePlanCompatibility compatibleThinkingResults = .compatiblePlans /\
      thinkingSituation fixturePlanCompatibility conflictingThinkingResults = .boundedStall /\
      thinkingSituation fixturePlanCompatibility singlePerspectiveThinkingResults =
        .singlePerspective /\
      reviewRouter (fun _ => .reject) = .fix /\ reviewRouter (fun _ => .approve) = .done /\
      reviewRouter (fun _ => .comment) = .userDecisionOrBoundedPass /\
      terminationRouter permittedObservation = .permitClaim /\
      terminationAdmits fakeRosterObservation = false /\
      terminationAdmits unsatisfiedObservation = false /\
      terminationAdmits abstainObservation = false /\
      terminationAdmits invalidObservation = false /\ terminationAdmits missingObservation = false
  | .s9 => Sound optimalTerminationRule /\
      (forall rule, Sound rule -> RuleLE rule optimalTerminationRule) /\
      (forall rule, Greatest rule -> rule = optimalTerminationRule)
  | .s10 => fixtureConfig.sharedPassBudget = 5 /\
      BoundedPassKind.LegalAt .metaLayerConvergence .metaJudge /\
      BoundedPassKind.LegalAt .repeatedReview .reviewTripletWorkers /\
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
      carrier_selection_starts_with_codex,
      carrier_selection_reopens_at_highest_priority_untried,
      carrier_selection_abstains_when_exhausted⟩
  · exact retry_budget_is_fixed_per_flight
  · exact ⟨codex_completion_requires_all_five_conjuncts,
      nyxid_completion_uses_structured_terminal_status_without_sentinel,
      subagent_completion_uses_valid_envelope_without_sentinel,
      codex_evidence_cannot_complete_nyxid, nyxid_evidence_cannot_complete_codex⟩
  · exact thinking_abstain_skips_all_dependent_stages
  · intro config state final event unavailable step
    exact unavailable_isolation_allows_only_abstain config state final event unavailable step
  · exact ⟨prior_exposure_is_per_carrier,
      heterogeneous_carriers_need_not_have_independent_priors⟩
  · exact ⟨design_router_rejects_single_perspective,
      design_row_unanimous_actionable_is_reachable.1,
      design_row_compatible_disagreement_is_reachable.1,
      design_row_bounded_stall_is_reachable_from_conflicting_proposals.1,
      design_row_single_perspective_is_reachable.1, review_router_truth_table.1,
      review_router_truth_table.2.1, review_router_truth_table.2.2,
      termination_router_permits_exact_unanimous_satisfaction,
      termination_router_rejects_fake_roster, termination_router_withholds_on_unsatisfied,
      termination_router_withholds_on_abstain, termination_router_withholds_on_invalid,
      termination_router_withholds_on_missing⟩
  · exact termination_router_sound_maximal_unique
  · exact ⟨shared_pass_budget_default_is_five,
      bounded_pass_kinds_have_only_legal_loci.1,
      bounded_pass_kinds_have_only_legal_loci.2.1,
      bounded_pass_kinds_have_only_legal_loci.2.2.1,
      bounded_pass_kinds_have_only_legal_loci.2.2.2,
      termination_roster_evaluation_consumes_exactly_one_shared_pass.2.1,
      termination_roster_evaluation_is_blocked_at_budget_ceiling⟩
def RequiredFixtureSuite : Prop :=
    (Stage.next .intake = some .chooseWorkerMode /\
      Stage.next .chooseWorkerMode = some .thinkingPanelWorkers /\
      Stage.next .thinkingPanelWorkers = some .metaJudge /\
      Stage.next .metaJudge = some .implementationWorker /\
      Stage.next .implementationWorker = some .reviewTripletWorkers /\
      Stage.next .reviewTripletWorkers = some .fixOrDone /\
      Stage.next .fixOrDone = none) /\
      (forall (source first second : Stage), source.Successor first ->
        source.Successor second -> first = second) /\
      (Carrier.priorityRank .codexCli = 0 /\
        Carrier.priorityRank .nyxidOracle = 1 /\
        Carrier.priorityRank .isolatedTokenSubagent = 2 /\
        Carrier.priorityRank .abstain = 3) /\
      (priorExposure .codexCli = .repoPriorExposed /\
        priorExposure .nyxidOracle = .externalPriorExposed /\
        priorExposure .isolatedTokenSubagent = .callerPriorExposed /\
        priorExposure .abstain = .noCarrier) /\
      designRouter .singlePerspective = .rejectFakeConsensus /\
      (inlineConsensusModel.stageRelation = Stage.Successor /\
        inlineConsensusModel.carrierSelector = selectCarrier /\
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
        WithinRetryBudgets config run.events /\
        NoCarrierReopened run.events /\
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
        BoundedPassKind.LegalAt .repeatedReview .reviewTripletWorkers /\
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
    clause_object_index_is_total⟩
end D5.S0.History.Consensus.InlineConsensusProtocolFixtures
