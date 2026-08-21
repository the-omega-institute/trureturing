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
def missingCompletionConjunct : CompletionConjunct -> CompletionObservation
  | .carrierExit =>
      { carrierExitedZero := false, resultArtifactExists := true, envelopeValid := true,
        verdictAllowed := true, sentinelExists := true }
  | .resultArtifact =>
      { carrierExitedZero := true, resultArtifactExists := false, envelopeValid := true,
        verdictAllowed := true, sentinelExists := true }
  | .envelope =>
      { carrierExitedZero := true, resultArtifactExists := true, envelopeValid := false,
        verdictAllowed := true, sentinelExists := true }
  | .verdict =>
      { carrierExitedZero := true, resultArtifactExists := true, envelopeValid := true,
        verdictAllowed := false, sentinelExists := true }
  | .sentinel =>
      { carrierExitedZero := true, resultArtifactExists := true, envelopeValid := true,
        verdictAllowed := true, sentinelExists := false }
private theorem missing_completion_is_incomplete (field : CompletionConjunct) :
    Not (Complete (missingCompletionConjunct field)) := by
  cases field <;> simp [missingCompletionConjunct, Complete]
theorem missing_carrier_exit_fails_completion :
    Not (Complete (missingCompletionConjunct .carrierExit)) := missing_completion_is_incomplete _
theorem missing_result_artifact_fails_completion :
    Not (Complete (missingCompletionConjunct .resultArtifact)) := missing_completion_is_incomplete _
theorem invalid_envelope_fails_completion :
    Not (Complete (missingCompletionConjunct .envelope)) := missing_completion_is_incomplete _
theorem disallowed_verdict_fails_completion :
    Not (Complete (missingCompletionConjunct .verdict)) := missing_completion_is_incomplete _
theorem missing_sentinel_fails_completion :
    Not (Complete (missingCompletionConjunct .sentinel)) := missing_completion_is_incomplete _
theorem completion_proxy_is_never_completion (proxy : ForbiddenCompletionProxy) :
    Not (Complete (evidenceFromProxyOnly proxy)) := by
  cases proxy <;> simp [evidenceFromProxyOnly, Complete]
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
def completeObservation : CompletionObservation := ⟨true, true, true, true, true⟩
theorem complete_observation_satisfies_all_five_conjuncts : Complete completeObservation := by
  simp [Complete, completeObservation]
def completedTerminationResult (seat : TerminationSeat) (verdict : TerminationVerdict) :
    TerminationSeatResult seat :=
  .completed
    { view := ⟨.complete, seat.role, .repoPriorExposed⟩, carrier := .codexCli
      workerCarrier := by decide, completionObservation := completeObservation
      complete := complete_observation_satisfies_all_five_conjuncts, exposureMatches := rfl }
    rfl verdict
def completedReviewResult (seat : ReviewSeat) (verdict : ReviewVerdict) :
    ReviewSeatResult seat :=
  .completed
    { view := ⟨.complete, seat.role, .repoPriorExposed⟩, carrier := .codexCli
      workerCarrier := by decide, completionObservation := completeObservation
      complete := complete_observation_satisfies_all_five_conjuncts, exposureMatches := rfl }
    rfl verdict
def completedThinkingResult (seat : ThinkingSeat) (verdict : ThinkingVerdict) :
    ThinkingSeatResult seat :=
  .completed
    { view := ⟨.complete, seat.role, .repoPriorExposed⟩, carrier := .codexCli
      workerCarrier := by decide, completionObservation := completeObservation
      complete := complete_observation_satisfies_all_five_conjuncts, exposureMatches := rfl }
    rfl verdict
theorem completed_seat_results_carry_completion_and_disclosure (result : CompletedSeatResult) :
    Complete result.completionObservation /\ result.view.exposure = priorExposure result.carrier :=
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
theorem termination_roster_has_exactly_three_named_seat_types : Fintype.card TerminationSeat = 3 := by
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
def allProposeThinkingResults : ThinkingResults :=
  fun seat => completedThinkingResult seat .propose
theorem thinking_panel_has_exactly_six_named_role_indices : Fintype.card ThinkingSeat = 6 := by
  decide
theorem review_triplet_has_exactly_three_named_role_indices : Fintype.card ReviewSeat = 3 := by
  decide
theorem thinking_router_is_derived_from_the_six_results :
    thinkingSituation allProposeThinkingResults = .unanimousActionable := by decide
def fixtureConfig : ProtocolConfig :=
  { eligible := fun _ _ => allEligible
    retryBudget := fun _ _ _ => 2
    sharedPassBudget := defaultSharedPassBudget
    ownerAuthorizedAboveDefault := false
    initialIsolation := .available }
theorem shared_pass_budget_default_is_five : fixtureConfig.sharedPassBudget = 5 := by decide
theorem fixture_pass_budget_is_authorized : PassBudgetAuthorized fixtureConfig := by
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
    designSituation := none, reviewExit := none
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
def immediateAbstainFinal : ProtocolState := { initialState exhaustedConfig with phase := .abstained }
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
theorem unavailable_isolation_budget_is_authorized :
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
  | finish budget live atEnd isolated reviewDone observation permitted => simp_all
def unauthorizedOverBudgetConfig : ProtocolConfig :=
  { fixtureConfig with sharedPassBudget := 6, ownerAuthorizedAboveDefault := false }
theorem unauthorized_over_budget_config_is_rejected :
    Not (PassBudgetAuthorized unauthorizedOverBudgetConfig) := by
  intro authorized
  rcases authorized with withinDefault | ownerAuthorized
  · norm_num [unauthorizedOverBudgetConfig, fixtureConfig, defaultSharedPassBudget] at withinDefault
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
  | finish budget live atEnd isolated reviewDone observation permitted =>
      have retained := all_reject_review_exit_is_retained_in_state
      rw [retained] at reviewDone
      cases reviewDone
theorem required_fixture_suite_is_pinned :
    terminationRouter permittedObservation = .permitClaim /\
      terminationAdmits permittedObservation = true /\
      terminationAdmits fakeRosterObservation = false /\
      terminationAdmits unsatisfiedObservation = false /\
      terminationAdmits abstainObservation = false /\
      terminationAdmits invalidObservation = false /\
      terminationAdmits missingObservation = false /\
      StrictBelow alwaysAbstain terminationAdmits /\
      Sound alwaysAbstain /\
      StrictBelow terminationAdmits majorityAdmit /\
      Not (Sound majorityAdmit) /\
      Complete completeObservation /\
      Not (Complete (missingCompletionConjunct .carrierExit)) /\
      Not (Complete (missingCompletionConjunct .resultArtifact)) /\
      Not (Complete (missingCompletionConjunct .envelope)) /\
      Not (Complete (missingCompletionConjunct .verdict)) /\
      Not (Complete (missingCompletionConjunct .sentinel)) /\
      (forall proxy, Not (Complete (evidenceFromProxyOnly proxy))) /\
      (priorExposure .codexCli != priorExposure .nyxidOracle /\
        forall latent, correlatedConclusion .codexCli latent =
          correlatedConclusion .nyxidOracle latent) /\
      selectCarrier allEligible {} = .codexCli /\
      selectCarrier allEligible {.codexCli} = .nyxidOracle /\
      selectCarrier (fun _ => false) {} = .abstain /\
      (reviewRouter (fun _ => .reject) = .fix /\
        reviewRouter (fun _ => .approve) = .done /\
        reviewRouter (fun _ => .comment) = .userDecisionOrBoundedPass) /\
      Fintype.card ThinkingSeat = 6 /\
      Fintype.card ReviewSeat = 3 /\
      thinkingSituation allProposeThinkingResults = .unanimousActionable /\
      reviewRouter (reviewObservation allRejectReviewResults) = .fix /\
      allRejectReviewFinal.reviewExit = some .fix /\
      Not (exists final, ProtocolStep fixtureConfig allRejectReviewFinal .finish final) /\
      Not (PassBudgetAuthorized unauthorizedOverBudgetConfig) /\
      (forall start events final,
        Not (Execution inlineConsensusModel unauthorizedOverBudgetConfig start events final)) /\
      Execution inlineConsensusModel unavailableIsolationConfig
        (initialState unavailableIsolationConfig) [.abstain .intake] unavailableIsolationFinal /\
      (forall state, state.isolation = .unavailable ->
        forall final, Not (ProtocolStep fixtureConfig state .finish final)) := by
  exact ⟨termination_router_permits_exact_unanimous_satisfaction,
    positive_permit_row_is_admitted,
    termination_router_rejects_fake_roster,
    termination_router_withholds_on_unsatisfied,
    termination_router_withholds_on_abstain,
    termination_router_withholds_on_invalid,
    termination_router_withholds_on_missing,
    always_abstain_is_strictly_below_optimal,
    always_abstain_is_sound,
    majority_admit_is_strictly_above_optimal,
    majority_admit_is_not_sound,
    complete_observation_satisfies_all_five_conjuncts,
    missing_carrier_exit_fails_completion,
    missing_result_artifact_fails_completion,
    invalid_envelope_fails_completion,
    disallowed_verdict_fails_completion,
    missing_sentinel_fails_completion,
    completion_proxy_is_never_completion,
    heterogeneous_carriers_need_not_have_independent_priors,
    carrier_selection_starts_with_codex,
    carrier_selection_reopens_at_highest_priority_untried,
    carrier_selection_abstains_when_exhausted,
    review_router_truth_table,
    thinking_panel_has_exactly_six_named_role_indices,
    review_triplet_has_exactly_three_named_role_indices,
    thinking_router_is_derived_from_the_six_results,
    all_reject_results_route_to_fix,
    all_reject_review_exit_is_retained_in_state,
    all_reject_review_cannot_reach_terminal_claim_without_fix,
    unauthorized_over_budget_config_is_rejected,
    unauthorized_over_budget_config_has_no_execution,
    unavailable_isolation_reaches_abstained_state,
    unavailable_isolation_cannot_finish⟩
end D5.S0.History.Consensus.InlineConsensusProtocolFixtures
