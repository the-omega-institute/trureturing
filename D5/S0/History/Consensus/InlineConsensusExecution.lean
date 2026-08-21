/- GID: D5/S0/History/Consensus/InlineConsensusExecution
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Executions preserve retry uniqueness and consume finite protocol resources. -/
import D5.S0.History.Consensus.InlineConsensusOptimality
namespace D5.S0.History.Consensus.InlineConsensusOptimality
def NoStaleTerminationPermitAfterFix : Prop :=
  forall config start repaired,
    ProtocolStep config start (.boundedPass start.stage .fixPass) repaired ->
      repaired.terminationExit = none /\ repaired.terminationEpoch = none /\
        forall final, Not (ProtocolStep config repaired .finish final)
theorem no_stale_termination_permit_after_fix : NoStaleTerminationPermitAfterFix := by
  intro config start repaired step
  cases step with
  | fixAndReview =>
      refine ⟨rfl, rfl, ?_⟩
      intro final finish
      cases finish with
      | finish => simp_all
theorem termination_gate_requires_current_done_review {config : ProtocolConfig}
    {state final : ProtocolState}
    (step : ProtocolStep config state (.boundedPass state.stage .terminationGate) final) :
    state.reviewExit = some .done /\ state.reviewEpoch = some state.artifactEpoch := by
  cases step <;> simp_all
inductive DesignRouteTransition : DesignExit -> Type
  | implement {config start final}
      (step : ProtocolStep config start (.advance .metaJudge .implementationWorker) final) :
      DesignRouteTransition .implement
  | convergenceSucceeded {config start final}
      (step : ProtocolStep config start (.boundedPass .metaJudge .metaLayerConvergence) final)
      (implementable : final.designSituation = some .unanimousActionable) :
      DesignRouteTransition .metaLayerConvergence
  | convergenceExhausted {config start final}
      (step : ProtocolStep config start (.boundedPass .metaJudge .metaLayerConvergence) final)
      (exhausted : final.phase = .abstained) : DesignRouteTransition .metaLayerConvergence
  | stalled {config start final} (step : ProtocolStep config start (.abstain .metaJudge) final)
      (stopped : final.phase = .abstained) : DesignRouteTransition .abstainEscalate
  | fakeConsensus {config start final}
      (step : ProtocolStep config start (.abstain .metaJudge) final)
      (stopped : final.phase = .abstained) : DesignRouteTransition .rejectFakeConsensus
inductive ReviewRouteTransition : ReviewExit -> Type
  | repair {config start final}
      (step : ProtocolStep config start (.boundedPass .fixOrDone .fixPass) final) :
      ReviewRouteTransition .fix
  | terminationCandidate {config start final}
      (step : ProtocolStep config start (.boundedPass .fixOrDone .terminationGate) final) :
      ReviewRouteTransition .done
  | userDecision {config start final}
      (step : ProtocolStep config start (.abstain .fixOrDone) final) :
      ReviewRouteTransition .userDecisionOrBoundedPass
  | repeatedPass {config start final}
      (step : ProtocolStep config start (.boundedPass .fixOrDone .repeatedReview) final) :
      ReviewRouteTransition .userDecisionOrBoundedPass
inductive TerminationRouteTransition : TerminationExit -> Type
  | fakeConsensus {config start final}
      (step : ProtocolStep config start (.boundedPass .fixOrDone .terminationGate) final)
      (recorded : final.terminationExit = some .rejectFakeConsensus) :
      TerminationRouteTransition .rejectFakeConsensus
  | permit {config start final}
      (step : ProtocolStep config start (.boundedPass .fixOrDone .terminationGate) final)
      (recorded : final.terminationExit = some .permitClaim) :
      TerminationRouteTransition .permitClaim
  | continueAgainstGap {config start final}
      (step : ProtocolStep config start (.boundedPass .fixOrDone .terminationGate) final)
      (recorded : final.terminationExit = some .continueAgainstGap) :
      TerminationRouteTransition .continueAgainstGap
  | evidenceGap {config start final}
      (step : ProtocolStep config start (.boundedPass .fixOrDone .terminationGate) final)
      (recorded : final.terminationExit = some .escalateEvidenceGap) :
      TerminationRouteTransition .escalateEvidenceGap
def RouterTransitionsExhaustive : Prop :=
  (forall exit, Nonempty (DesignRouteTransition exit)) /\
    (forall exit, Nonempty (ReviewRouteTransition exit)) /\
    (forall exit, Nonempty (TerminationRouteTransition exit))
def termination_observation_information_content :
    TerminationObservation ≃ TerminationRoster ×
      (TerminationSeatResult .criterionEvidence ×
        TerminationSeatResult .residualGap × TerminationSeatResult .claimIntegrity) where
  toFun observation := (observation.roster,
    observation.result .criterionEvidence,
    observation.result .residualGap,
    observation.result .claimIntegrity)
  invFun data :=
    { roster := data.1
      result := fun seat => match seat with
        | .criterionEvidence => data.2.1
        | .residualGap => data.2.2.1
        | .claimIntegrity => data.2.2.2 }
  left_inv observation := by
    cases observation with
    | mk roster result =>
        have resultEta :
            (fun seat => match seat with
              | .criterionEvidence => result .criterionEvidence
              | .residualGap => result .residualGap
              | .claimIntegrity => result .claimIntegrity) = result := by
          funext seat
          cases seat <;> rfl
        change TerminationObservation.mk roster (fun seat => match seat with
          | .criterionEvidence => result .criterionEvidence
          | .residualGap => result .residualGap
          | .claimIntegrity => result .claimIntegrity) =
            TerminationObservation.mk roster result
        rw [resultEta]
  right_inv data := by
    rcases data with ⟨roster, criterion, residual, claim⟩
    rfl
def TerminationHazard (observation : TerminationObservation) : Prop :=
  Not (ExactRoster observation.roster) \/
    exists seat, Not ((observation.result seat).IsSatisfied)
abbrev Rule := TerminationObservation -> Bool
def Sound (rule : Rule) : Prop :=
  forall observation, rule observation = true -> Not (TerminationHazard observation)
def RuleLE (left right : Rule) : Prop :=
  forall observation, left observation = true -> right observation = true
def Greatest (rule : Rule) : Prop := IsGreatest {candidate | Sound candidate} rule
def StrictBelow (left right : Rule) : Prop :=
  RuleLE left right /\ exists observation, right observation = true /\ left observation = false
def terminationAdmits : Rule :=
  fun observation => decide (terminationRouter observation = .permitClaim)
def alwaysAbstain : Rule := fun _ => false
def majorityAdmit : Rule :=
  fun observation => exactRosterBool observation.roster &&
    (((observation.result .criterionEvidence).isSatisfiedBool &&
        (observation.result .residualGap).isSatisfiedBool) ||
      ((observation.result .criterionEvidence).isSatisfiedBool &&
        (observation.result .claimIntegrity).isSatisfiedBool) ||
      ((observation.result .residualGap).isSatisfiedBool &&
        (observation.result .claimIntegrity).isSatisfiedBool))
/-- Internal wiring only; external prose correspondence remains a digest-pinned snapshot claim. -/
theorem inline_consensus_model_internal_wiring :
    inlineConsensusModel.stageRelation = Stage.Successor /\
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
      inlineConsensusModel.transition = ProtocolStep := by
  simp [inlineConsensusModel]
def optimalTerminationRule : Rule := fun observation =>
  decide (inlineConsensusModel.terminationRoute observation = .permitClaim)
theorem nonpermitting_observation_cannot_admit (observation : TerminationObservation)
    (withheld : terminationRouter observation ≠ .permitClaim) :
    optimalTerminationRule observation = false := by
  simp [optimalTerminationRule, inlineConsensusModel, withheld]
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
        0 < attempts /\ attempts <= config.retryBudget stage role carrier
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
theorem exact_roster_bool_iff (roster : TerminationRoster) :
    exactRosterBool roster = true <-> ExactRoster roster := by
  simp only [exactRosterBool, ExactRoster, Bool.and_eq_true, bne_iff_ne]
  tauto
theorem seat_result_satisfied_bool_iff {seat : TerminationSeat}
    (result : TerminationSeatResult seat) :
    result.isSatisfiedBool = true <-> result.IsSatisfied := by
  cases result with
  | completed evidence roleMatches verdict =>
      cases verdict <;> simp [TerminationSeatResult.isSatisfiedBool,
        TerminationSeatResult.IsSatisfied]
  | invalid => simp [TerminationSeatResult.isSatisfiedBool, TerminationSeatResult.IsSatisfied]
  | missing => simp [TerminationSeatResult.isSatisfiedBool, TerminationSeatResult.IsSatisfied]
private theorem all_satisfied_bool_iff (observation : TerminationObservation) :
    allSatisfiedBool observation = true <-> allSatisfied observation := by
  simp only [allSatisfiedBool, Bool.and_eq_true]
  rw [seat_result_satisfied_bool_iff, seat_result_satisfied_bool_iff,
    seat_result_satisfied_bool_iff]
  constructor
  · rintro ⟨⟨criterion, residual⟩, claim⟩ seat
    cases seat <;> assumption
  · intro satisfied
    exact ⟨⟨satisfied .criterionEvidence, satisfied .residualGap⟩,
      satisfied .claimIntegrity⟩
private theorem termination_router_permit_iff (observation : TerminationObservation) :
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
      by_contra notSatisfied
      exact safe (Or.inr ⟨seat, notSatisfied⟩)
  · rintro ⟨roster, satisfied⟩ hazard
    rcases hazard with fake | danger
    · exact fake roster
    · obtain ⟨seat, notSatisfied⟩ := danger
      exact notSatisfied (satisfied seat)
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
private theorem rule_le_iff_le (left right : Rule) : RuleLE left right <-> left <= right := by
  simp [RuleLE, Pi.le_def, Bool.le_iff_imp]
private theorem termination_admits_sound_maximal_unique :
    Sound terminationAdmits /\
      (forall rule, Sound rule -> RuleLE rule terminationAdmits) /\
      (forall rule, Greatest rule -> rule = terminationAdmits) := by
  refine ⟨termination_admits_sound, ?_, ?_⟩
  · intro rule sound
    exact (rule_le_iff_le rule terminationAdmits).mpr (termination_admits_greatest.2 sound)
  · intro rule greatest
    exact IsGreatest.unique greatest termination_admits_greatest
theorem termination_router_sound_maximal_unique :
    Sound optimalTerminationRule /\
      (forall rule, Sound rule -> RuleLE rule optimalTerminationRule) /\
      (forall rule, Greatest rule -> rule = optimalTerminationRule) := by
  change Sound terminationAdmits /\
    (forall rule, Sound rule -> RuleLE rule terminationAdmits) /\
    (forall rule, Greatest rule -> rule = terminationAdmits)
  exact termination_admits_sound_maximal_unique
private theorem step_potential_lt {config : ProtocolConfig} {start final : ProtocolState}
    {event : Event} (step : ProtocolStep config start event final) :
    potential config final < potential config start := by
  cases step with
  | flightFailure role carrier attempts budget live isolated legal eligible untried selected
      available positive within =>
      have smaller := Finset.card_erase_lt_of_mem available
      simp only [potential] at smaller ⊢
      omega
  | advance target budget live isolated authorized successor =>
      have stageDecrease : stageRemaining target < stageRemaining start.stage := by
        cases source : start.stage <;>
          simp [Stage.Successor, Stage.next, source] at successor <;>
          subst target <;> simp [stageRemaining, Stage.rank]
      simp only [potential, AdvanceCondition.nextState_remainingFlights,
        AdvanceCondition.nextState_stage, AdvanceCondition.nextState_passesUsed,
        AdvanceCondition.nextState_phase]
      omega
  | designConvergence => simp [potential]; omega
  | designConvergenceExhausted => simp_all [potential, liveCredit]; omega
  | repeatedReview => simp [potential]; omega
  | fixAndReview => simp [potential]; omega
  | terminationGate => simp [potential]; omega
  | terminationGapEngineering => simp [potential]; omega
  | terminationGapCaller => simp [potential]; omega
  | terminationGapEscalate => simp_all [potential, liveCredit]; omega
  | terminationFakeConsensus => simp_all [potential, liveCredit]; omega
  | terminationEvidenceGap => simp_all [potential, liveCredit]; omega
  | finish => simp_all [potential, liveCredit]
  | abstain budget live reason => simp [potential, liveCredit, live]
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
      rcases List.mem_cons.mp member with head | tail
      · subst queried
        cases step <;> simp_all
      · exact ih queried tail
private theorem execution_keys_mem_start {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    forall key, key ∈ flightKeys events -> key ∈ start.remainingFlights := by
  induction execution with
  | nil =>
      intro key member
      simp [flightKeys] at member
  | cons step rest ih =>
      cases step with
      | flightFailure role carrier attempts budget live isolated legal eligible untried selected
          available positive within =>
          intro key member
          simp only [flightKeys, List.mem_cons] at member
          rcases member with rfl | member
          · exact available
          · exact Finset.mem_of_mem_erase (ih key member)
      | advance target budget live isolated authorized successor => simpa [flightKeys] using ih
      | designConvergence => simpa [flightKeys] using ih
      | designConvergenceExhausted => simpa [flightKeys] using ih
      | repeatedReview => simpa [flightKeys] using ih
      | fixAndReview => simpa [flightKeys] using ih
      | terminationGate => simpa [flightKeys] using ih
      | terminationGapEngineering => simpa [flightKeys] using ih
      | terminationGapCaller => simpa [flightKeys] using ih
      | terminationGapEscalate => simpa [flightKeys] using ih
      | terminationFakeConsensus => simpa [flightKeys] using ih
      | terminationEvidenceGap => simpa [flightKeys] using ih
      | finish => simpa [flightKeys] using ih
      | abstain budget live reason => simpa [flightKeys] using ih
private theorem execution_no_carrier_reopened {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    NoCarrierReopened events := by
  induction execution with
  | nil => simp [NoCarrierReopened, flightKeys]
  | cons step rest ih =>
      cases step with
      | flightFailure role carrier attempts budget live isolated legal eligible untried selected
          available positive within =>
          simp only [NoCarrierReopened, flightKeys, List.nodup_cons]
          constructor
          · intro reopened
            have remaining := execution_keys_mem_start rest _ reopened
            exact (Finset.mem_erase.mp remaining).1 rfl
          · exact ih
      | advance target budget live isolated authorized successor =>
          simpa [NoCarrierReopened, flightKeys] using ih
      | designConvergence => simpa [NoCarrierReopened, flightKeys] using ih
      | designConvergenceExhausted => simpa [NoCarrierReopened, flightKeys] using ih
      | repeatedReview => simpa [NoCarrierReopened, flightKeys] using ih
      | fixAndReview => simpa [NoCarrierReopened, flightKeys] using ih
      | terminationGate => simpa [NoCarrierReopened, flightKeys] using ih
      | terminationGapEngineering => simpa [NoCarrierReopened, flightKeys] using ih
      | terminationGapCaller => simpa [NoCarrierReopened, flightKeys] using ih
      | terminationGapEscalate => simpa [NoCarrierReopened, flightKeys] using ih
      | terminationFakeConsensus => simpa [NoCarrierReopened, flightKeys] using ih
      | terminationEvidenceGap => simpa [NoCarrierReopened, flightKeys] using ih
      | finish => simpa [NoCarrierReopened, flightKeys] using ih
      | abstain budget live reason => simpa [NoCarrierReopened, flightKeys] using ih
private theorem execution_pass_count_eq {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    start.passesUsed + sharedPassCount events = final.passesUsed := by
  induction execution with
  | nil => simp [sharedPassCount]
  | cons step rest ih =>
      cases step <;> simp [sharedPassCount] at ih ⊢ <;> omega
private theorem execution_passes_within_budget {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final)
    (startWithin : start.passesUsed <= config.sharedPassBudget) :
    final.passesUsed <= config.sharedPassBudget := by
  induction execution with
  | nil => exact startWithin
  | cons step rest ih =>
      apply ih
      cases step <;> simp_all
theorem every_maximal_run_is_bounded (config : ProtocolConfig)
    (run : MaximalRun inlineConsensusModel config) :
    WithinRetryBudgets config run.events /\
      NoCarrierReopened run.events /\
      sharedPassCount run.events <= config.sharedPassBudget /\
      run.events.length <= explicitRunBound config := by
  refine ⟨execution_within_retry_budgets run.execution,
    execution_no_carrier_reopened run.execution, ?_, ?_⟩
  · have countEq : sharedPassCount run.events = run.finalState.passesUsed := by
      simpa [initialState] using execution_pass_count_eq run.execution
    rw [countEq]
    exact execution_passes_within_budget run.execution (Nat.zero_le _)
  · have bound := execution_length_add_potential_le run.execution
    have initialPotential : potential config (initialState config) = explicitRunBound config := by
      simp [potential, initialState, explicitRunBound, stageRemaining, Stage.rank, liveCredit,
        Finset.card_univ]
      omega
    rw [initialPotential] at bound
    omega
#print axioms termination_router_sound_maximal_unique
#print axioms every_maximal_run_is_bounded
end D5.S0.History.Consensus.InlineConsensusOptimality
