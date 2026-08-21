/- GID: D5/S0/History/Consensus/InlineConsensusExecution
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every event invalidates an existing permit and finite runs consume finite resources. -/
import D5.S0.History.Consensus.InlineConsensusOptimality

namespace D5.S0.History.Consensus.InlineConsensusOptimality

theorem every_protocol_event_increments_epoch {config : ProtocolConfig}
    {start final : ProtocolState} {event : Event}
    (step : ProtocolStep config start event final) :
    final.eventEpoch = start.eventEpoch + 1 :=
  ProtocolStep.event_epoch_strict step

theorem every_protocol_event_invalidates_carried_permit {config : ProtocolConfig}
    {start final : ProtocolState} {event : Event}
    (carried : start.terminationExit = some .permitClaim)
    (step : ProtocolStep config start event final) :
    Not (FinishPrecondition final) := by
  rcases step with ⟨wellFormed, raw, action, rfl⟩
  intro ready
  have stale : start.terminationEpoch = some (start.eventEpoch + 1) := by
    simpa [recordEvent, permitEpochAfterEvent, carried] using ready.2.2.2.2.2.2
  have epochBound := wellFormed _ stale
  omega

def NoStaleTerminationPermitAfterFix : Prop :=
  forall config start repaired,
    ProtocolStep config start (.boundedPass start.stage .fixPass) repaired ->
      Not (FinishPrecondition repaired)

theorem no_stale_termination_permit_after_fix : NoStaleTerminationPermitAfterFix := by
  intro config start repaired step
  by_cases carried : start.terminationExit = some .permitClaim
  · exact every_protocol_event_invalidates_carried_permit carried step
  · intro ready
    rcases step with ⟨wellFormed, raw, action, rfl⟩
    cases action with
    | fixAndReview budget live isolated atEnd needsFix implementation implementationAuthorized
        results reviewAuthorized withinBudget =>
        apply carried
        simpa [FinishPrecondition, recordEvent] using ready.2.2.2.2.2.1

theorem termination_gate_requires_current_done_review {config : ProtocolConfig}
    {state final : ProtocolState}
    (step : ProtocolStep config state
      (.boundedPass state.stage .terminationGate) final) :
    state.reviewExit = some .done /\ state.reviewEpoch = some state.artifactEpoch := by
  rcases step with ⟨wellFormed, raw, action, rfl⟩
  cases action
  all_goals simp_all

theorem flight_failure_occurs_only_after_precommitted_budget_exhaustion
    {config : ProtocolConfig} {state final : ProtocolState}
    {role : SeatRole} {carrier : Carrier} {attempts : Nat}
    (step : ProtocolStep config state
      (.flightFailure state.stage role carrier attempts) final) :
    0 < attempts /\ attempts = config.retryBudget state.stage role carrier := by
  rcases step with ⟨wellFormed, raw, action, rfl⟩
  cases action
  all_goals simp_all

theorem fallback_selection_requires_a_tried_origin {config : ProtocolConfig}
    {state : ProtocolState} {role : SeatRole} {carrier : Carrier}
    (fallback : FallbackAssigned config state role carrier) :
    (triedAt state state.stage role).Nonempty /\
      selectCarrier (config.eligible state.stage role)
        (triedAt state state.stage role) = carrier :=
  fallback.2

theorem fallback_selection_requires_exhausted_origin {config : ProtocolConfig}
    {state : ProtocolState} {role : SeatRole} {carrier : Carrier}
    (fallback : FallbackAssigned config state role carrier) :
    exists failedCarrier,
      flightKey state.stage role failedCarrier ∈ state.exhaustedFlights :=
  fallback.1

theorem exact_roster_bool_iff (roster : TerminationRoster) :
    exactRosterBool roster = true <-> ExactRoster roster := by
  simp only [exactRosterBool, ExactRoster, Bool.and_eq_true, bne_iff_ne]
  tauto

private theorem all_satisfied_bool_iff (observation : TerminationObservation) :
    allSatisfiedBool observation = true <-> allSatisfied observation := by
  simp only [allSatisfiedBool, Bool.and_eq_true, allSatisfied]
  constructor
  · rintro ⟨⟨criterion, residual⟩, claim⟩ seat
    cases seat <;> assumption
  · intro satisfied
    exact ⟨⟨satisfied .criterionEvidence, satisfied .residualGap⟩,
      satisfied .claimIntegrity⟩

theorem termination_router_permit_iff (observation : TerminationObservation) :
    terminationRouter observation = .permitClaim <->
      ExactRoster observation.roster /\ allSatisfied observation := by
  rw [← exact_roster_bool_iff, ← all_satisfied_bool_iff]
  cases roster : exactRosterBool observation.roster <;>
    cases satisfied : allSatisfiedBool observation <;>
    cases unsatisfied : anyUnsatisfiedBool observation <;>
    simp [terminationRouter, roster, satisfied, unsatisfied]

theorem termination_admits_iff (observation : TerminationObservation) :
    terminationAdmits observation = true <->
      ExactRoster observation.roster /\ allSatisfied observation := by
  simp [terminationAdmits, termination_router_permit_iff]

private theorem hazard_free_iff (observation : TerminationObservation) :
    Not (TerminationHazard observation) <->
      ExactRoster observation.roster /\ allSatisfied observation := by
  constructor
  · intro safe
    constructor
    · by_contra fake
      exact safe (Or.inl fake)
    · intro seat
      cases value : (observation.result seat).isSatisfiedBool
      · exact False.elim (safe (Or.inr ⟨seat, value⟩))
      · rfl
  · rintro ⟨roster, satisfied⟩ hazard
    rcases hazard with fake | danger
    · exact fake roster
    · obtain ⟨seat, notSatisfied⟩ := danger
      rw [satisfied seat] at notSatisfied
      contradiction

private theorem termination_admits_sound : Sound terminationAdmits := by
  intro observation admitted
  exact (hazard_free_iff observation).mpr ((termination_admits_iff observation).mp admitted)

private theorem termination_admits_greatest : Greatest terminationAdmits := by
  constructor
  · exact termination_admits_sound
  · intro rule sound
    rw [Pi.le_def]
    intro observation
    rw [Bool.le_iff_imp]
    intro admitted
    apply (termination_admits_iff observation).mpr
    apply (hazard_free_iff observation).mp
    exact sound observation admitted

private theorem rule_le_iff_le (left right : Rule) :
    RuleLE left right <-> left <= right := by
  simp [RuleLE, Pi.le_def, Bool.le_iff_imp]

private def terminationWitnessArtifact : GoalArtifact :=
  { rawUserInput := some .digestA
    normalizedGoal := some .digestA
    constraints := some .digestA
    successCriteria := some .digestA
    iterationQuestion := some .digestA
    harness := some .digestA
    revisions := some .digestA }

private def terminationWitnessResult (seat : TerminationSeat)
    (verdict : TerminationVerdict) : TerminationSeatResult seat :=
  .completed
    { view :=
        { goalArtifact := ⟨terminationWitnessArtifact, Finset.univ⟩
          role := seat.role
          exposure := .repoPriorExposed
          sameRoundPeerOutputs := {} }
      carrier := .codexCli
      completionObservation := .codex true true true true true
      verdict }
    rfl

private def exactTerminationWitnessRoster : TerminationRoster
  | 0 => some .criterionEvidence
  | 1 => some .residualGap
  | _ => some .claimIntegrity

def safeAdmittedObservation : TerminationObservation :=
  { roster := exactTerminationWitnessRoster
    result := fun seat => terminationWitnessResult seat .satisfied }

def hazardousMajorityObservation : TerminationObservation :=
  { roster := exactTerminationWitnessRoster
    result := fun
      | .criterionEvidence => terminationWitnessResult .criterionEvidence .satisfied
      | .residualGap => terminationWitnessResult .residualGap .unsatisfied
      | .claimIntegrity => terminationWitnessResult .claimIntegrity .satisfied }

private theorem always_abstain_sound : Sound alwaysAbstain := by
  intro observation admitted
  simp [alwaysAbstain] at admitted

private theorem always_abstain_strictly_below_optimal :
    StrictBelow alwaysAbstain optimalTerminationRule := by
  constructor
  · intro observation admitted
    simp [alwaysAbstain] at admitted
  · exact ⟨safeAdmittedObservation, by decide, rfl⟩

private theorem optimal_strictly_below_majority :
    StrictBelow optimalTerminationRule majorityAdmit := by
  constructor
  · intro observation admitted
    change terminationAdmits observation = true at admitted
    have safe := (termination_admits_iff observation).mp admitted
    have roster : exactRosterBool observation.roster = true :=
      (exact_roster_bool_iff observation.roster).mpr safe.1
    have criterion := safe.2 .criterionEvidence
    have residual := safe.2 .residualGap
    have claim := safe.2 .claimIntegrity
    simp [majorityAdmit, roster, criterion, residual, claim]
  · exact ⟨hazardousMajorityObservation, by decide, by decide⟩

private theorem majority_admit_is_not_sound : Not (Sound majorityAdmit) := by
  intro sound
  have admitted : majorityAdmit hazardousMajorityObservation = true := by decide
  have safe := sound hazardousMajorityObservation admitted
  apply safe
  right
  exact ⟨.residualGap, by decide⟩

theorem termination_router_sound_maximal_unique :
    Sound optimalTerminationRule /\
      (forall rule, Sound rule -> RuleLE rule optimalTerminationRule) /\
      (forall rule, Greatest rule -> rule = optimalTerminationRule) /\
      Sound alwaysAbstain /\
      StrictBelow alwaysAbstain optimalTerminationRule /\
      StrictBelow optimalTerminationRule majorityAdmit /\
      Not (Sound majorityAdmit) := by
  change Sound terminationAdmits /\
    (forall rule, Sound rule -> RuleLE rule terminationAdmits) /\
    (forall rule, Greatest rule -> rule = terminationAdmits) /\
    Sound alwaysAbstain /\ StrictBelow alwaysAbstain terminationAdmits /\
    StrictBelow terminationAdmits majorityAdmit /\ Not (Sound majorityAdmit)
  refine ⟨termination_admits_sound, ?_, ?_, always_abstain_sound,
    always_abstain_strictly_below_optimal, optimal_strictly_below_majority,
    majority_admit_is_not_sound⟩
  · intro rule sound
    exact (rule_le_iff_le rule terminationAdmits).mpr (termination_admits_greatest.2 sound)
  · intro rule greatest
    exact IsGreatest.unique greatest termination_admits_greatest

theorem nonpermitting_observation_cannot_admit (observation : TerminationObservation)
    (withheld : terminationRouter observation ≠ .permitClaim) :
    optimalTerminationRule observation = false := by
  simp [optimalTerminationRule, inlineConsensusModel, withheld]

theorem review_router_reject_precedence (observation : ReviewObservation)
    (rejects : exists index, observation index = .reject) :
    reviewRouter observation = .fix := by
  obtain ⟨index, rejected⟩ := rejects
  fin_cases index <;> simp_all [reviewRouter, reviewHasBool]

theorem review_router_approve_without_reject (observation : ReviewObservation)
    (noReject : forall index, observation index != .reject)
    (approves : exists index, observation index = .approve) :
    reviewRouter observation = .done := by
  obtain ⟨index, approved⟩ := approves
  fin_cases index <;>
    simp_all [reviewRouter, reviewHasBool, Bool.or_eq_true]

theorem review_router_all_comment (observation : ReviewObservation)
    (comments : forall index, observation index = .comment) :
    reviewRouter observation = .userDecisionOrBoundedPass := by
  have zero := comments 0
  have one := comments 1
  have two := comments 2
  simp [reviewRouter, reviewHasBool, zero, one, two]

theorem termination_fake_roster_precedence (observation : TerminationObservation)
    (fake : Not (ExactRoster observation.roster)) :
    terminationRouter observation = .rejectFakeConsensus := by
  have rejected : exactRosterBool observation.roster = false := by
    cases value : exactRosterBool observation.roster
    · rfl
    · exact False.elim (fake ((exact_roster_bool_iff observation.roster).mp value))
  simp [terminationRouter, rejected]

private theorem unsatisfied_is_not_satisfied {seat : TerminationSeat}
    (result : TerminationSeatResult seat)
    (unsatisfied : result.isUnsatisfiedBool = true) :
    result.isSatisfiedBool = false := by
  cases result with
  | completed report roleMatches =>
      cases report.verdict <;> simp_all [TerminationSeatResult.isUnsatisfiedBool,
        TerminationSeatResult.isSatisfiedBool]
  | invalid | missing => simp_all [TerminationSeatResult.isUnsatisfiedBool]

theorem termination_unsatisfied_precedence (observation : TerminationObservation)
    (roster : ExactRoster observation.roster)
    (unsatisfied : exists seat,
      (observation.result seat).isUnsatisfiedBool = true) :
    terminationRouter observation = .continueAgainstGap := by
  have rosterBool : exactRosterBool observation.roster = true :=
    (exact_roster_bool_iff observation.roster).mpr roster
  obtain ⟨seat, seatUnsatisfied⟩ := unsatisfied
  have seatNotSatisfied := unsatisfied_is_not_satisfied (observation.result seat) seatUnsatisfied
  fin_cases seat <;>
    simp_all [terminationRouter, allSatisfiedBool, anyUnsatisfiedBool]

theorem termination_evidence_gap_precedence (observation : TerminationObservation)
    (roster : ExactRoster observation.roster)
    (notSatisfied : Not (allSatisfied observation))
    (noUnsatisfied : forall seat,
      (observation.result seat).isUnsatisfiedBool = false) :
    terminationRouter observation = .escalateEvidenceGap := by
  have rosterBool : exactRosterBool observation.roster = true :=
    (exact_roster_bool_iff observation.roster).mpr roster
  have satisfiedBool : allSatisfiedBool observation = false := by
    cases value : allSatisfiedBool observation
    · rfl
    · exact False.elim (notSatisfied ((all_satisfied_bool_iff observation).mp value))
  have unsatisfiedBool : anyUnsatisfiedBool observation = false := by
    simp [anyUnsatisfiedBool, noUnsatisfied]
  simp [terminationRouter, rosterBool, satisfiedBool, unsatisfiedBool]

inductive Execution (model : InlineConsensusModel) (config : ProtocolConfig) :
    ProtocolState -> List Event -> ProtocolState -> Prop
  | nil (state : ProtocolState) (budgetAuthorized : PassBudgetAuthorized config) :
      Execution model config state [] state
  | cons {start middle final : ProtocolState} {event : Event} {events : List Event}
      (step : model.transition config start event middle)
      (rest : Execution model config middle events final) :
      Execution model config start (event :: events) final

def stageRemaining (stage : Stage) : Nat := 6 - stage.rank

def liveCredit : RunPhase -> Nat
  | .live => 1
  | .terminal | .abstained => 0

def potential (config : ProtocolConfig) (state : ProtocolState) : Nat :=
  state.remainingFlights.card + stageRemaining state.stage +
    (config.sharedPassBudget - state.passesUsed) + liveCredit state.phase

def explicitRunBound (config : ProtocolConfig) : Nat :=
  Fintype.card FlightKey + 7 + config.sharedPassBudget

def WithinRetryBudgets (config : ProtocolConfig) (events : List Event) : Prop :=
  forall event, event ∈ events -> match event with
    | .flightFailure stage role carrier attempts =>
        0 < attempts /\ attempts = config.retryBudget stage role carrier
    | _ => True

def flightKeys : List Event -> List FlightKey
  | [] => []
  | .flightFailure stage role carrier _ :: events =>
      flightKey stage role carrier :: flightKeys events
  | _ :: events => flightKeys events

def NoCarrierReopened (events : List Event) : Prop := (flightKeys events).Nodup

def sharedPassCount : List Event -> Nat
  | [] => 0
  | .boundedPass _ _ :: events => sharedPassCount events + 1
  | _ :: events => sharedPassCount events

structure MaximalRun (model : InlineConsensusModel) (config : ProtocolConfig) where
  events : List Event
  finalState : ProtocolState
  execution : Execution model config (initialState config) events finalState
  maximal : forall event state, Not (model.transition config finalState event state)

private theorem step_potential_lt {config : ProtocolConfig} {start final : ProtocolState}
    {event : Event} (step : ProtocolStep config start event final) :
    potential config final < potential config start := by
  rcases step with ⟨wellFormed, raw, action, rfl⟩
  cases action with
  | flightFailure role carrier attempts budget live isolated legal eligible untried
      assigned available positive exhausted =>
      have smaller := Finset.card_erase_lt_of_mem available
      simp only [potential, recordEvent] at smaller ⊢
      omega
  | advance target budget live isolated authorized successor =>
      have stageDecrease : stageRemaining target < stageRemaining start.stage := by
        cases source : start.stage <;>
          simp [Stage.Successor, Stage.next, source] at successor <;>
          subst target <;> simp [stageRemaining, Stage.rank]
      cases authorized <;> simp_all [potential, recordEvent, AdvanceCondition.nextState]
  | designConvergence => simp [potential, recordEvent]; omega
  | designConvergenceExhausted => simp_all [potential, recordEvent, liveCredit]; omega
  | repeatedReview => simp [potential, recordEvent]; omega
  | fixAndReview => simp [potential, recordEvent]; omega
  | terminationGate budget live isolated atEnd reviewDone reviewCurrent noPermit
      observation authorized owner withinBudget =>
      cases routed : terminationRouter observation
      · simp [potential, recordEvent, terminationNextState, routed, liveCredit]
        omega
      · simp [potential, recordEvent, terminationNextState, routed, liveCredit]
        omega
      · by_cases engineering : owner = .engineering
        · simp [potential, recordEvent, terminationNextState, routed, engineering,
            liveCredit, live]
          omega
        · simp [potential, recordEvent, terminationNextState, routed, engineering,
            liveCredit, live]
          omega
      · simp [potential, recordEvent, terminationNextState, routed, liveCredit]
        omega
  | finish => simp_all [potential, recordEvent, liveCredit, FinishPrecondition]
  | abstain => simp_all [potential, recordEvent, liveCredit]

private theorem execution_length_add_potential_le {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    events.length + potential config final <= potential config start := by
  induction execution with
  | nil => simp
  | cons step rest ih =>
      simp only [List.length_cons]
      have decreases := step_potential_lt step
      omega

private theorem execution_within_retry_budgets {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    WithinRetryBudgets config events := by
  induction execution with
  | nil => simp [WithinRetryBudgets]
  | cons step rest ih =>
      intro queried member
      rcases List.mem_cons.mp member with rfl | tail
      · rcases step with ⟨wellFormed, raw, action, rfl⟩
        cases action <;> simp_all
      · exact ih queried tail

theorem every_execution_uses_prelaunch_retry_commitment {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    WithinRetryBudgets config events :=
  execution_within_retry_budgets execution

theorem every_execution_uses_authorized_shared_budget {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    PassBudgetAuthorized config := by
  induction execution with
  | nil state budgetAuthorized => exact budgetAuthorized
  | cons step rest ih => exact ih

theorem abstained_state_has_no_successor {config : ProtocolConfig}
    {state final : ProtocolState} {event : Event}
    (abstained : state.phase = .abstained) :
    Not (ProtocolStep config state event final) := by
  intro step
  rcases step with ⟨wellFormed, raw, action, rfl⟩
  cases action <;> simp_all [FinishPrecondition]

theorem abstain_event_enters_absorbing_state {config : ProtocolConfig}
    {state final : ProtocolState} {stage : Stage}
    (step : ProtocolStep config state (.abstain stage) final) :
    final.phase = .abstained := by
  rcases step with ⟨wellFormed, raw, action, rfl⟩
  cases action
  all_goals simp_all [recordEvent]

theorem unavailable_isolation_allows_only_abstain {config : ProtocolConfig}
    {state final : ProtocolState} {event : Event}
    (unavailable : state.isolation = .unavailable)
    (step : ProtocolStep config state event final) :
    exists stage, event = .abstain stage := by
  rcases step with ⟨wellFormed, raw, action, rfl⟩
  cases action <;> simp_all [FinishPrecondition]

private theorem step_remainingFlights_subset {config : ProtocolConfig}
    {start final : ProtocolState} {event : Event}
    (step : ProtocolStep config start event final) :
    final.remainingFlights ⊆ start.remainingFlights := by
  rcases step with ⟨wellFormed, raw, action, rfl⟩
  cases action with
  | flightFailure => exact Finset.erase_subset _ _
  | advance target budget live isolated authorized successor =>
      cases authorized <;> simp [recordEvent, AdvanceCondition.nextState]
  | designConvergence => simp [recordEvent]
  | designConvergenceExhausted => simp [recordEvent]
  | repeatedReview => simp [recordEvent]
  | fixAndReview => simp [recordEvent]
  | terminationGate budget live isolated atEnd reviewDone reviewCurrent noPermit
      observation authorized owner withinBudget =>
      cases routed : terminationRouter observation
      · simp [recordEvent, terminationNextState, routed]
      · simp [recordEvent, terminationNextState, routed]
      · by_cases engineering : owner = .engineering <;>
          simp [recordEvent, terminationNextState, routed, engineering]
      · simp [recordEvent, terminationNextState, routed]
  | finish => simp [recordEvent]
  | abstain => simp [recordEvent]

private theorem execution_keys_mem_start {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    forall key, key ∈ flightKeys events -> key ∈ start.remainingFlights := by
  induction execution with
  | nil => simp [flightKeys]
  | cons step rest ih =>
      rcases step with ⟨wellFormed, raw, action, rfl⟩
      cases action with
      | flightFailure role carrier attempts budget live isolated legal eligible untried
          assigned available positive exhausted =>
          intro key member
          simp only [flightKeys, List.mem_cons] at member
          rcases member with rfl | member
          · exact available
          · exact Finset.mem_of_mem_erase (ih key member)
      | advance target budget live isolated authorized successor =>
          cases authorized <;>
            simpa [flightKeys, recordEvent, AdvanceCondition.nextState] using ih
      | designConvergence => simpa [flightKeys, recordEvent] using ih
      | designConvergenceExhausted => simpa [flightKeys, recordEvent] using ih
      | repeatedReview => simpa [flightKeys, recordEvent] using ih
      | fixAndReview => simpa [flightKeys, recordEvent] using ih
      | terminationGate budget live isolated atEnd reviewDone reviewCurrent noPermit
          observation authorized owner withinBudget =>
          cases routed : terminationRouter observation
          · simpa [flightKeys, recordEvent, terminationNextState, routed] using ih
          · simpa [flightKeys, recordEvent, terminationNextState, routed] using ih
          · by_cases engineering : owner = .engineering <;>
              simpa [flightKeys, recordEvent, terminationNextState, routed,
                engineering] using ih
          · simpa [flightKeys, recordEvent, terminationNextState, routed] using ih
      | finish => simpa [flightKeys, recordEvent] using ih
      | abstain => simpa [flightKeys, recordEvent] using ih

private theorem execution_no_carrier_reopened {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    NoCarrierReopened events := by
  induction execution with
  | nil => simp [NoCarrierReopened, flightKeys]
  | cons step rest ih =>
      rcases step with ⟨wellFormed, raw, action, rfl⟩
      cases action with
      | flightFailure role carrier attempts budget live isolated legal eligible untried
          assigned available positive exhausted =>
          simp only [NoCarrierReopened, flightKeys, List.nodup_cons]
          constructor
          · intro reopened
            have remaining := execution_keys_mem_start rest _ reopened
            exact (Finset.mem_erase.mp remaining).1 rfl
          · exact ih
      | _ => simpa [NoCarrierReopened, flightKeys] using ih

private theorem execution_shared_pass_count_le {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    sharedPassCount events <= config.sharedPassBudget - start.passesUsed := by
  induction execution with
  | nil => simp [sharedPassCount]
  | cons step rest ih =>
      rcases step with ⟨wellFormed, raw, action, rfl⟩
      cases action with
      | flightFailure => simpa [sharedPassCount, recordEvent] using ih
      | advance target budget live isolated authorized successor =>
          cases authorized <;>
            simpa [sharedPassCount, recordEvent, AdvanceCondition.nextState] using ih
      | designConvergence budget live isolated atMeta recorded withinBudget =>
          simp only [sharedPassCount]
          simp only [recordEvent] at ih
          omega
      | designConvergenceExhausted budget live isolated atMeta recorded withinBudget =>
          simp only [sharedPassCount]
          simp only [recordEvent] at ih
          omega
      | repeatedReview budget live isolated atEnd needsPass results authorized withinBudget =>
          simp only [sharedPassCount]
          simp only [recordEvent] at ih
          omega
      | fixAndReview budget live isolated atEnd needsFix implementation implementationAuthorized
          results reviewAuthorized withinBudget =>
          simp only [sharedPassCount]
          simp only [recordEvent] at ih
          omega
      | terminationGate budget live isolated atEnd reviewDone reviewCurrent noPermit
          observation authorized owner withinBudget =>
          simp only [sharedPassCount]
          cases routed : terminationRouter observation
          · simp [recordEvent, terminationNextState, routed] at ih
            omega
          · simp [recordEvent, terminationNextState, routed] at ih
            omega
          · by_cases engineering : owner = .engineering
            · simp [recordEvent, terminationNextState, routed, engineering] at ih
              omega
            · simp [recordEvent, terminationNextState, routed, engineering] at ih
              omega
          · simp [recordEvent, terminationNextState, routed] at ih
            omega
      | finish => simpa [sharedPassCount, recordEvent] using ih
      | abstain => simpa [sharedPassCount, recordEvent] using ih

theorem every_maximal_run_is_bounded (config : ProtocolConfig)
    (run : MaximalRun inlineConsensusModel config) :
    WithinRetryBudgets config run.events /\ NoCarrierReopened run.events /\
      sharedPassCount run.events <= config.sharedPassBudget /\
      run.events.length <= explicitRunBound config := by
  refine ⟨execution_within_retry_budgets run.execution,
    execution_no_carrier_reopened run.execution, ?_, ?_⟩
  · exact (execution_shared_pass_count_le run.execution).trans (Nat.sub_le _ _)
  · have bounded := execution_length_add_potential_le run.execution
    have initialPotential : potential config (initialState config) = explicitRunBound config := by
      simp [potential, initialState, explicitRunBound, stageRemaining, Stage.rank, liveCredit]
      omega
    rw [initialPotential] at bounded
    omega

theorem every_maximal_run_never_reopens_carrier (config : ProtocolConfig)
    (run : MaximalRun inlineConsensusModel config) :
    NoCarrierReopened run.events :=
  (every_maximal_run_is_bounded config run).2.1

def designEvent : DesignExit -> Event
  | .implement => .advance .metaJudge .implementationWorker
  | .metaLayerConvergence => .boundedPass .metaJudge .metaLayerConvergence
  | .abstainEscalate | .rejectFakeConsensus => .abstain .metaJudge

structure DesignRouteTransition (config : ProtocolConfig) (state : ProtocolState)
    (situation : DesignSituation) : Type where
  recorded : state.designSituation = some situation
  final : ProtocolState
  step : ProtocolStep config state (designEvent (designRouter situation)) final

structure ReviewRouteTransition (config : ProtocolConfig) (state : ProtocolState)
    (results : ReviewResults) : Type where
  final : ProtocolState
  step : ProtocolStep config state (.advance .reviewTripletWorkers .fixOrDone) final
  routed : final.reviewExit = some (reviewRouter (reviewObservation results))

structure TerminationRouteTransition (config : ProtocolConfig) (state : ProtocolState)
    (observation : TerminationObservation) : Type where
  final : ProtocolState
  step : ProtocolStep config state
    (.boundedPass .fixOrDone .terminationGate) final
  routed : final.terminationExit = some (terminationRouter observation)

end D5.S0.History.Consensus.InlineConsensusOptimality
