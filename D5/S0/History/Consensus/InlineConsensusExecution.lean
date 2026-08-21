/- GID: D5/S0/History/Consensus/InlineConsensusExecution
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every event invalidates an existing permit and finite runs consume finite resources. -/
import D5.S0.History.Consensus.InlineConsensusOptimality

namespace D5.S0.History.Consensus.InlineConsensusOptimality
theorem constant_conclusions_are_independent : ConstantConclusionsAreIndependent := by
  intro first second
  cases first <;> cases second <;>
    decide
theorem heterogeneous_correlated_conclusions_are_not_independent :
    Not (UniformIndependent
      (correlatedConclusion .codexCli) (correlatedConclusion .nyxidOracle)) := by
  decide
theorem every_protocol_event_increments_epoch {model : InlineConsensusModel}
    {config : ProtocolConfig}
    {start final : ProtocolState} {event : Event}
    (step : ProtocolStep model config start event final) :
    final.eventEpoch = start.eventEpoch + 1 :=
  ProtocolStep.event_epoch_strict step
theorem every_protocol_event_invalidates_carried_permit {model : InlineConsensusModel}
    {config : ProtocolConfig}
    {start final : ProtocolState} {event : Event}
    (carried : start.terminationExit = some .permitClaim)
    (step : ProtocolStep model config start event final) :
    Not (FinishPrecondition final) := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  intro ready
  by_cases rawPermit : raw.terminationExit = some .permitClaim
  · have cleared : (recordEvent start raw).terminationExit = none := by
      simp [recordEvent, terminationExitAfterEvent, carriedPermit, carried, rawPermit]
    have permit : (recordEvent start raw).terminationExit = some .permitClaim :=
      ready.2.2.2.2.2.1
    rw [cleared] at permit
    contradiction
  · exact rawPermit (by
      simpa [recordEvent, terminationExitAfterEvent, carriedPermit, carried, rawPermit]
        using ready.2.2.2.2.2.1)
theorem every_protocol_event_clears_carried_permit {model : InlineConsensusModel}
    {config : ProtocolConfig} {start final : ProtocolState} {event : Event}
    (carried : start.terminationExit = some .permitClaim)
    (step : ProtocolStep model config start event final) :
    final.terminationExit ≠ some .permitClaim := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  by_cases rawPermit : raw.terminationExit = some .permitClaim
  · simp [recordEvent, terminationExitAfterEvent, carriedPermit, carried, rawPermit]
  · simp [recordEvent, terminationExitAfterEvent, carriedPermit, carried, rawPermit]
def RecoverablePermitInvalidation (model : InlineConsensusModel) : Prop :=
  forall (config : ProtocolConfig) (before invalidated : ProtocolState) (event : Event)
      (observation : TerminationObservation) (_owner : TerminationGapOwner),
    before.terminationExit = some .permitClaim ->
    ProtocolStep model config before event invalidated ->
    PassBudgetAuthorized config ->
    StateWellFormed invalidated ->
    invalidated.phase = .live -> invalidated.isolation = .available ->
    invalidated.stage = .fixOrDone -> invalidated.reviewExit = some .done ->
    invalidated.reviewEpoch = some invalidated.artifactEpoch ->
    observation.DispatchAuthorized model config invalidated ->
    Disjoint (observation.attemptKeys invalidated) invalidated.attemptedFlights ->
    invalidated.passesUsed < config.sharedPassBudget ->
    exists reevaluated, model.transition config invalidated
      (.boundedPass invalidated.stage .terminationGate
        (observation.attemptKeys invalidated)) reevaluated
theorem carried_permit_invalidation_is_recoverable (model : InlineConsensusModel) :
    RecoverablePermitInvalidation model := by
  intro config before invalidated event observation owner carried invalidating budgetAuthorized
    wellFormed live isolated atEnd reviewDone reviewCurrent authorized attemptsFresh withinBudget
  have noPermit : invalidated.terminationExit ≠ some .permitClaim :=
    every_protocol_event_clears_carried_permit carried invalidating
  have shape : model.dispatchShape config.dispatchPlan := invalidating.1
  let action : ProtocolAction model config invalidated
      (.boundedPass invalidated.stage .terminationGate
        (observation.attemptKeys invalidated))
      (terminationNextState model invalidated observation owner) :=
    .terminationGate invalidated budgetAuthorized
      live isolated atEnd reviewDone reviewCurrent noPermit observation authorized attemptsFresh
      owner withinBudget
  refine ⟨recordEvent invalidated (terminationNextState model invalidated observation owner), ?_⟩
  exact ProtocolStep.ofAction shape wellFormed action

def NoStaleTerminationPermitAfterFix : Prop :=
  forall model config start attempted repaired,
    ProtocolStep model config start (.boundedPass start.stage .fixPass attempted) repaired ->
      Not (FinishPrecondition repaired)

theorem no_stale_termination_permit_after_fix : NoStaleTerminationPermitAfterFix := by
  intro model config start attempted repaired step
  by_cases carried : start.terminationExit = some .permitClaim
  · exact every_protocol_event_invalidates_carried_permit carried step
  · intro ready
    rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
    cases action with
    | fixAndReview budget live isolated atEnd needsFix implementation implementationAuthorized
        results reviewAuthorized attemptsFresh withinBudget =>
        apply carried
        simpa [FinishPrecondition, recordEvent, terminationExitAfterEvent, carriedPermit,
          carried] using ready.2.2.2.2.2.1

theorem termination_gate_requires_current_done_review {model : InlineConsensusModel}
    {config : ProtocolConfig}
    {state final : ProtocolState}
    {attempted : Finset FlightKey}
    (step : ProtocolStep model config state
      (.boundedPass state.stage .terminationGate attempted) final) :
    state.reviewExit = some .done /\ state.reviewEpoch = some state.artifactEpoch := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action
  all_goals simp_all

theorem flight_failure_occurs_only_after_precommitted_budget_exhaustion
    {config : ProtocolConfig} {state final : ProtocolState}
    {role : SeatRole} {carrier : Carrier} {attempts : Nat}
    {model : InlineConsensusModel}
    (step : ProtocolStep model config state
      (.flightFailure state.stage role carrier attempts) final) :
    0 < attempts /\ attempts = config.retryBudget state.stage role carrier := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action
  all_goals simp_all

theorem fallback_selection_requires_a_tried_origin {model : InlineConsensusModel}
    {config : ProtocolConfig}
    {state : ProtocolState} {role : SeatRole} {carrier : Carrier}
    (fallback : FallbackAssigned model config state role carrier) :
    (triedAt state state.stage role).Nonempty /\
      model.fallbackSelector (config.eligible state.stage role)
        (triedAt state state.stage role) = carrier :=
  fallback.2

theorem fallback_selection_requires_exhausted_origin {model : InlineConsensusModel}
    {config : ProtocolConfig}
    {state : ProtocolState} {role : SeatRole} {carrier : Carrier}
    (fallback : FallbackAssigned model config state role carrier) :
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
    inlineConsensusModel.terminationRoute observation = .permitClaim <->
      inlineConsensusModel.rosterContract observation.roster /\ allSatisfied observation := by
  change terminationRouter observation = .permitClaim <->
    ExactRoster observation.roster /\ allSatisfied observation
  rw [← exact_roster_bool_iff, ← all_satisfied_bool_iff]
  cases roster : exactRosterBool observation.roster <;>
    cases satisfied : allSatisfiedBool observation <;>
    cases unsatisfied : anyUnsatisfiedBool observation <;>
    simp [terminationRouter, roster, satisfied, unsatisfied]

theorem termination_admits_iff (observation : TerminationObservation) :
    terminationAdmits inlineConsensusModel observation = true <->
      inlineConsensusModel.rosterContract observation.roster /\ allSatisfied observation := by
  simp [terminationAdmits, termination_router_permit_iff]

private theorem hazard_free_iff (observation : TerminationObservation) :
    Not (TerminationHazard inlineConsensusModel observation) <->
      inlineConsensusModel.rosterContract observation.roster /\ allSatisfied observation := by
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

private theorem termination_admits_sound :
    Sound inlineConsensusModel (terminationAdmits inlineConsensusModel) := by
  intro observation admitted
  exact (hazard_free_iff observation).mpr ((termination_admits_iff observation).mp admitted)

private theorem termination_admits_greatest :
    Greatest inlineConsensusModel (terminationAdmits inlineConsensusModel) := by
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

private theorem always_abstain_sound : Sound inlineConsensusModel alwaysAbstain := by
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
    change terminationAdmits inlineConsensusModel observation = true at admitted
    have safe := (termination_admits_iff observation).mp admitted
    have roster : exactRosterBool observation.roster = true :=
      (exact_roster_bool_iff observation.roster).mpr safe.1
    have criterion := safe.2 .criterionEvidence
    have residual := safe.2 .residualGap
    have claim := safe.2 .claimIntegrity
    simp [majorityAdmit, roster, criterion, residual, claim]
  · exact ⟨hazardousMajorityObservation, by decide, by decide⟩

private theorem majority_admit_is_not_sound :
    Not (Sound inlineConsensusModel majorityAdmit) := by
  intro sound
  have admitted : majorityAdmit hazardousMajorityObservation = true := by decide
  have safe := sound hazardousMajorityObservation admitted
  apply safe
  right
  exact ⟨.residualGap, by decide⟩

theorem termination_router_sound_maximal_unique :
    Sound inlineConsensusModel optimalTerminationRule /\
      (forall rule, Sound inlineConsensusModel rule -> RuleLE rule optimalTerminationRule) /\
      (forall rule, Greatest inlineConsensusModel rule -> rule = optimalTerminationRule) /\
      Sound inlineConsensusModel alwaysAbstain /\
      StrictBelow alwaysAbstain optimalTerminationRule /\
      StrictBelow optimalTerminationRule majorityAdmit /\
      Not (Sound inlineConsensusModel majorityAdmit) := by
  change Sound inlineConsensusModel (terminationAdmits inlineConsensusModel) /\
    (forall rule, Sound inlineConsensusModel rule ->
      RuleLE rule (terminationAdmits inlineConsensusModel)) /\
    (forall rule, Greatest inlineConsensusModel rule ->
      rule = terminationAdmits inlineConsensusModel) /\
    Sound inlineConsensusModel alwaysAbstain /\
    StrictBelow alwaysAbstain (terminationAdmits inlineConsensusModel) /\
    StrictBelow (terminationAdmits inlineConsensusModel) majorityAdmit /\
    Not (Sound inlineConsensusModel majorityAdmit)
  refine ⟨termination_admits_sound, ?_, ?_, always_abstain_sound,
    always_abstain_strictly_below_optimal, optimal_strictly_below_majority,
    majority_admit_is_not_sound⟩
  · intro rule sound
    exact (rule_le_iff_le rule (terminationAdmits inlineConsensusModel)).mpr
      (termination_admits_greatest.2 sound)
  · intro rule greatest
    exact IsGreatest.unique greatest termination_admits_greatest
theorem nonpermitting_observation_cannot_admit (observation : TerminationObservation)
    (withheld : inlineConsensusModel.terminationRoute observation ≠ .permitClaim) :
    optimalTerminationRule observation = false := by
  have globalWithheld : terminationRouter observation ≠ .permitClaim := by
    simpa [inlineConsensusModel] using withheld
  simp [optimalTerminationRule, terminationAdmits, inlineConsensusModel, globalWithheld]
theorem review_router_reject_precedence (observation : ReviewObservation)
    (rejects : exists index, observation index = .reject) :
    inlineConsensusModel.reviewRoute observation = .fix := by
  change reviewRouter observation = .fix
  obtain ⟨index, rejected⟩ := rejects
  fin_cases index <;> simp_all [reviewRouter, reviewHasBool]
theorem review_router_approve_without_reject (observation : ReviewObservation)
    (noReject : forall index, observation index != .reject)
    (approves : exists index, observation index = .approve) :
    inlineConsensusModel.reviewRoute observation = .done := by
  change reviewRouter observation = .done
  obtain ⟨index, approved⟩ := approves
  fin_cases index <;>
    simp_all [reviewRouter, reviewHasBool, Bool.or_eq_true]
theorem review_router_all_comment (observation : ReviewObservation)
    (comments : forall index, observation index = .comment) :
    inlineConsensusModel.reviewRoute observation = .userDecisionOrBoundedPass := by
  change reviewRouter observation = .userDecisionOrBoundedPass
  have zero := comments 0
  have one := comments 1
  have two := comments 2
  simp [reviewRouter, reviewHasBool, zero, one, two]
theorem termination_fake_roster_precedence (observation : TerminationObservation)
    (fake : Not (inlineConsensusModel.rosterContract observation.roster)) :
    inlineConsensusModel.terminationRoute observation = .rejectFakeConsensus := by
  change terminationRouter observation = .rejectFakeConsensus
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
    (roster : inlineConsensusModel.rosterContract observation.roster)
    (unsatisfied : exists seat,
      (observation.result seat).isUnsatisfiedBool = true) :
    inlineConsensusModel.terminationRoute observation = .continueAgainstGap := by
  change terminationRouter observation = .continueAgainstGap
  have rosterBool : exactRosterBool observation.roster = true :=
    (exact_roster_bool_iff observation.roster).mpr roster
  obtain ⟨seat, seatUnsatisfied⟩ := unsatisfied
  have seatNotSatisfied := unsatisfied_is_not_satisfied (observation.result seat) seatUnsatisfied
  fin_cases seat <;>
    simp_all [terminationRouter, allSatisfiedBool, anyUnsatisfiedBool]
theorem termination_evidence_gap_precedence (observation : TerminationObservation)
    (roster : inlineConsensusModel.rosterContract observation.roster)
    (notSatisfied : Not (allSatisfied observation))
    (noUnsatisfied : forall seat,
      (observation.result seat).isUnsatisfiedBool = false) :
    inlineConsensusModel.terminationRoute observation = .escalateEvidenceGap := by
  change terminationRouter observation = .escalateEvidenceGap
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

def Event.workerAttemptKeys : Event -> Finset FlightKey
  | .flightFailure stage role carrier _ => {flightKey stage role carrier}
  | .advance _ _ attempted | .boundedPass _ _ attempted => attempted
  | .finish | .abstain _ => {}

noncomputable def workerAttemptHistory : List Event -> List FlightKey
  | [] => []
  | event :: events => event.workerAttemptKeys.toList ++ workerAttemptHistory events

def NoCarrierReopened (events : List Event) : Prop :=
  (workerAttemptHistory events).Nodup

def sharedPassCount : List Event -> Nat
  | [] => 0
  | .boundedPass _ _ _ :: events => sharedPassCount events + 1
  | _ :: events => sharedPassCount events

structure MaximalRun (model : InlineConsensusModel) (config : ProtocolConfig) where
  events : List Event
  finalState : ProtocolState
  execution : Execution model config (initialState config) events finalState
  maximal : forall event state, Not (model.transition config finalState event state)

private theorem step_potential_lt {config : ProtocolConfig}
    {start final : ProtocolState} {event : Event}
    (step : ProtocolStep inlineConsensusModel config start event final) :
    potential config final < potential config start := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action with
  | flightFailure role carrier attempts budget live isolated legal eligible untried
      assigned available positive exhausted =>
      have smaller := Finset.card_erase_lt_of_mem available
      simp only [potential, recordEvent] at smaller ⊢
      omega
  | advance target budget live isolated authorized attemptsFresh successor =>
      have stageDecrease : stageRemaining target < stageRemaining start.stage := by
        change Stage.Successor start.stage target at successor
        cases source : start.stage <;>
          simp [Stage.Successor, Stage.next, source] at successor <;>
          subst target <;> simp [stageRemaining, Stage.rank]
      cases authorized <;> simp_all [potential, recordEvent, AdvanceCondition.nextState]
  | designConvergence => simp [potential, recordEvent]; omega
  | designConvergenceExhausted => simp_all [potential, recordEvent, liveCredit]; omega
  | repeatedReview => simp [potential, recordEvent]; omega
  | fixAndReview => simp [potential, recordEvent]; omega
  | terminationGate budget live isolated atEnd reviewDone reviewCurrent noPermit
      observation authorized attemptsFresh owner withinBudget =>
      cases routed : inlineConsensusModel.terminationRoute observation
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
      · rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
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
    Not (ProtocolStep inlineConsensusModel config state event final) := by
  intro step
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action <;> simp_all [FinishPrecondition]

theorem abstain_event_enters_absorbing_state {config : ProtocolConfig}
    {state final : ProtocolState} {stage : Stage}
    (step : ProtocolStep inlineConsensusModel config state (.abstain stage) final) :
    final.phase = .abstained := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action
  all_goals simp_all [recordEvent]

theorem unavailable_isolation_allows_only_abstain {config : ProtocolConfig}
    {state final : ProtocolState} {event : Event}
    (unavailable : state.isolation = .unavailable)
    (step : ProtocolStep inlineConsensusModel config state event final) :
    exists stage, event = .abstain stage := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action <;> simp_all [FinishPrecondition]

def noWorkerAvailable : Eligibility := fun _ => false

def nyxidOnlyAvailable : Eligibility
  | .nyxidOracle => true
  | _ => false

def ChooseWorkerModeRouting (model : InlineConsensusModel) : Prop :=
  model.fallbackSelector noWorkerAvailable {} = .abstain /\
    model.fallbackSelector nyxidOnlyAvailable {} = .nyxidOracle /\
    forall config state,
      config.workerModeEligibility = noWorkerAvailable ->
      model.dispatchShape config.dispatchPlan -> StateWellFormed state ->
      PassBudgetAuthorized config -> state.phase = .live ->
      state.stage = .chooseWorkerMode -> state.attemptedFlights = {} ->
      exists final,
        model.transition config state (.abstain .chooseWorkerMode) final /\
          final.phase = .abstained /\ final.attemptedFlights = {} /\
          workerAttemptHistory [.abstain .chooseWorkerMode] = []

theorem inline_choose_worker_mode_routes_before_launch :
    ChooseWorkerModeRouting inlineConsensusModel := by
  refine ⟨by decide, by decide, ?_⟩
  intro config state eligibility shape wellFormed budgetAuthorized live atStage noAttempts
  have unavailable : inlineConsensusModel.fallbackSelector
      config.workerModeEligibility {} = .abstain := by
    simp [eligibility, inlineConsensusModel, selectCarrier, eligibleUntried, noWorkerAvailable]
  let action : ProtocolAction inlineConsensusModel config state (.abstain state.stage)
      { state with phase := .abstained } :=
    .abstain state budgetAuthorized live (.workerModeUnavailable atStage unavailable)
  refine ⟨recordEvent state { state with phase := .abstained }, ?_, ?_, ?_, ?_⟩
  · change ProtocolStep inlineConsensusModel config state
      (.abstain .chooseWorkerMode) _
    simpa [atStage] using ProtocolStep.ofAction shape wellFormed action
  · simp [recordEvent]
  · simpa [recordEvent] using noAttempts
  · simp [workerAttemptHistory, Event.workerAttemptKeys]

private theorem step_remainingFlights_subset {config : ProtocolConfig}
    {start final : ProtocolState} {event : Event}
    (step : ProtocolStep inlineConsensusModel config start event final) :
    final.remainingFlights ⊆ start.remainingFlights := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action with
  | flightFailure => exact Finset.erase_subset _ _
  | advance target budget live isolated authorized attemptsFresh successor =>
      cases authorized <;> simp [recordEvent, AdvanceCondition.nextState]
  | designConvergence => simp [recordEvent]
  | designConvergenceExhausted => simp [recordEvent]
  | repeatedReview => simp [recordEvent]
  | fixAndReview => simp [recordEvent]
  | terminationGate budget live isolated atEnd reviewDone reviewCurrent noPermit
      observation authorized attemptsFresh owner withinBudget =>
      cases routed : inlineConsensusModel.terminationRoute observation
      · simp [recordEvent, terminationNextState, routed]
      · simp [recordEvent, terminationNextState, routed]
      · by_cases engineering : owner = .engineering <;>
          simp [recordEvent, terminationNextState, routed, engineering]
      · simp [recordEvent, terminationNextState, routed]
  | finish => simp [recordEvent]
  | abstain => simp [recordEvent]

private theorem step_attempts_fresh {model : InlineConsensusModel}
    {config : ProtocolConfig} {start final : ProtocolState} {event : Event}
    (step : ProtocolStep model config start event final) :
    Disjoint event.workerAttemptKeys start.attemptedFlights := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action with
  | flightFailure role carrier attempts budget live isolated legal eligible untried
      assigned available positive exhausted =>
      simp only [Event.workerAttemptKeys]
      rw [Finset.disjoint_singleton_left]
      simpa [Event.workerAttemptKeys, triedAt] using untried
  | advance target budget live isolated authorized attemptsFresh successor =>
      simpa [Event.workerAttemptKeys] using attemptsFresh
  | repeatedReview budget live isolated atEnd needsPass results authorized attemptsFresh
      withinBudget => simpa [Event.workerAttemptKeys] using attemptsFresh
  | fixAndReview budget live isolated atEnd needsFix implementation implementationAuthorized
      results reviewAuthorized attemptsFresh withinBudget =>
      simpa [Event.workerAttemptKeys] using attemptsFresh
  | terminationGate budget live isolated atEnd reviewDone reviewCurrent noPermit
      observation authorized attemptsFresh owner withinBudget =>
      simpa [Event.workerAttemptKeys] using attemptsFresh
  | designConvergence | designConvergenceExhausted | finish | abstain =>
      simp [Event.workerAttemptKeys]

private theorem step_attempted_mono {model : InlineConsensusModel}
    {config : ProtocolConfig} {start final : ProtocolState} {event : Event}
    (step : ProtocolStep model config start event final) :
    start.attemptedFlights ⊆ final.attemptedFlights := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action with
  | advance target budget live isolated authorized attemptsFresh successor =>
      cases authorized <;>
        simp [recordEvent, AdvanceCondition.nextState]
  | fixAndReview budget live isolated atEnd needsFix implementation implementationAuthorized
      results reviewAuthorized attemptsFresh withinBudget =>
      intro key old
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ old)
  | terminationGate budget live isolated atEnd reviewDone reviewCurrent noPermit
      observation authorized attemptsFresh owner withinBudget =>
      cases routed : model.terminationRoute observation <;>
        simp [recordEvent, terminationNextState, routed] ;
        split <;> simp_all
  | _ => simp [recordEvent]

private theorem step_attempts_mem_final {model : InlineConsensusModel}
    {config : ProtocolConfig} {start final : ProtocolState} {event : Event}
    (step : ProtocolStep model config start event final) :
    event.workerAttemptKeys ⊆ final.attemptedFlights := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action with
  | advance target budget live isolated authorized attemptsFresh successor =>
      cases authorized <;>
        simp [Event.workerAttemptKeys, recordEvent, AdvanceCondition.nextState,
          AdvanceCondition.attemptKeys]
  | terminationGate budget live isolated atEnd reviewDone reviewCurrent noPermit
      observation authorized attemptsFresh owner withinBudget =>
      cases routed : model.terminationRoute observation <;>
        simp [Event.workerAttemptKeys, recordEvent, terminationNextState, routed] ;
        split <;> simp_all
  | _ => simp [Event.workerAttemptKeys, recordEvent]

private theorem execution_attempts_fresh_of_start {model : InlineConsensusModel}
    {config : ProtocolConfig} {start final : ProtocolState} {events : List Event}
    (execution : Execution model config start events final) :
    forall key, key ∈ workerAttemptHistory events -> key ∉ start.attemptedFlights := by
  induction execution with
  | nil => simp [workerAttemptHistory]
  | @cons start middle final event events step rest ih =>
      intro key member
      simp only [workerAttemptHistory, List.mem_append, Finset.mem_toList] at member
      rcases member with current | later
      · exact fun old => Finset.disjoint_left.mp (step_attempts_fresh step) current old
      · exact fun old => ih key later (step_attempted_mono step old)
private theorem execution_no_carrier_reopened {model : InlineConsensusModel}
    {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution model config start events final) :
    NoCarrierReopened events := by
  induction execution with
  | nil => simp [NoCarrierReopened, workerAttemptHistory]
  | @cons start middle final event events step rest ih =>
      rw [NoCarrierReopened]
      simp only [workerAttemptHistory, List.nodup_append, Finset.nodup_toList]
      refine ⟨trivial, ih, ?_⟩
      intro key current later laterMember same
      subst later
      exact execution_attempts_fresh_of_start rest key laterMember
        (step_attempts_mem_final step (Finset.mem_toList.mp current))

private theorem execution_shared_pass_count_le {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    sharedPassCount events <= config.sharedPassBudget - start.passesUsed := by
  induction execution with
  | nil => simp [sharedPassCount]
  | cons step rest ih =>
      rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
      cases action with
      | flightFailure => simpa [sharedPassCount, recordEvent] using ih
      | advance target budget live isolated authorized attemptsFresh successor =>
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
      | repeatedReview budget live isolated atEnd needsPass results authorized attemptsFresh
          withinBudget =>
          simp only [sharedPassCount]
          simp only [recordEvent] at ih
          omega
      | fixAndReview budget live isolated atEnd needsFix implementation implementationAuthorized
          results reviewAuthorized attemptsFresh withinBudget =>
          simp only [sharedPassCount]
          simp only [recordEvent] at ih
          omega
      | terminationGate budget live isolated atEnd reviewDone reviewCurrent noPermit
          observation authorized attemptsFresh owner withinBudget =>
          simp only [sharedPassCount]
          cases routed : inlineConsensusModel.terminationRoute observation
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

def AllWorkerAttemptsRecorded (model : InlineConsensusModel) : Prop :=
  (forall stage role carrier attempts,
    (Event.flightFailure stage role carrier attempts).workerAttemptKeys =
      {flightKey stage role carrier}) /\
  (forall source target attempted,
    (Event.advance source target attempted).workerAttemptKeys = attempted) /\
  (forall stage kind attempted,
    (Event.boundedPass stage kind attempted).workerAttemptKeys = attempted) /\
  forall config (run : MaximalRun model config), NoCarrierReopened run.events

theorem all_worker_attempts_are_recorded (model : InlineConsensusModel) :
    AllWorkerAttemptsRecorded model := by
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, ?_⟩
  intro config run
  exact execution_no_carrier_reopened run.execution

def designEvent (model : InlineConsensusModel) (situation : DesignSituation) : Event :=
  match model.designRoute situation with
  | .implement => .advance .metaJudge .implementationWorker {}
  | .metaLayerConvergence => .boundedPass .metaJudge .metaLayerConvergence {}
  | .abstainEscalate | .rejectFakeConsensus => .abstain .metaJudge

structure DesignRouteTransition (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState) (situation : DesignSituation) : Type where
  recorded : state.designSituation = some situation
  final : ProtocolState
  step : model.transition config state (designEvent model situation) final

structure ReviewRouteTransition (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState) (results : ReviewResults) : Type where
  final : ProtocolState
  step : model.transition config state
    (.advance .reviewTripletWorkers .fixOrDone (results.attemptKeys state)) final
  routed : final.reviewExit = some (model.reviewRoute (reviewObservation results))

structure TerminationRouteTransition (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState) (observation : TerminationObservation) : Type where
  final : ProtocolState
  step : model.transition config state
    (.boundedPass .fixOrDone .terminationGate (observation.attemptKeys state)) final
  routed : final.terminationExit = some (model.terminationRoute observation)

end D5.S0.History.Consensus.InlineConsensusOptimality
