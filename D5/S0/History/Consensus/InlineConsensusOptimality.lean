/- GID: D5/S0/History/Consensus/InlineConsensusOptimality
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Event-fresh permits and preassigned dispatch refine the maximal safe router. -/
/- Snapshot correspondence only; it is not a theorem premise.
   beta.32 SKILL.md SHA-256 ab688e34f2b183291958f78b2d9ff6905d7330f3844668c5103026790d8b4cbf
   CODEX_WORKER_SPEC.md SHA-256 700237b1a1389002215272874e8c9cd7b17a130f0d0eaf7bb20cf9b39f49829d -/
import D5.S0.History.Consensus.InlineConsensusProtocolCore

namespace D5.S0.History.Consensus.InlineConsensusOptimality

theorem stage_order_is_the_protocol_order :
    Stage.next .intake = some .chooseWorkerMode /\
      Stage.next .chooseWorkerMode = some .thinkingPanelWorkers /\
      Stage.next .thinkingPanelWorkers = some .metaJudge /\
      Stage.next .metaJudge = some .implementationWorker /\
      Stage.next .implementationWorker = some .reviewTripletWorkers /\
      Stage.next .reviewTripletWorkers = some .fixOrDone /\
      Stage.next .fixOrDone = none := by decide

theorem stage_successor_is_unique (source first second : Stage)
    (hFirst : source.Successor first) (hSecond : source.Successor second) : first = second := by
  exact Option.some.inj (hFirst.symm.trans hSecond)

theorem carrier_priority_is_the_protocol_priority :
    Carrier.priorityRank .codexCli = 0 /\ Carrier.priorityRank .nyxidOracle = 1 /\
      Carrier.priorityRank .isolatedTokenSubagent = 2 /\
      Carrier.priorityRank .abstain = 3 := by decide

theorem selectCarrier_mem (eligible : Eligibility) (tried : Finset Carrier)
    (available : (eligibleUntried eligible tried).Nonempty) :
    selectCarrier eligible tried ∈ eligibleUntried eligible tried := by
  simp only [selectCarrier, dif_pos available]
  exact Finset.min'_mem _ _

theorem selectCarrier_minimal (eligible : Eligibility) (tried : Finset Carrier)
    (carrier : Carrier) (available : carrier ∈ eligibleUntried eligible tried) :
    Carrier.priorityRank (selectCarrier eligible tried) <= Carrier.priorityRank carrier := by
  have nonempty : (eligibleUntried eligible tried).Nonempty := ⟨carrier, available⟩
  have ordered : selectCarrier eligible tried <= carrier := by
    simp only [selectCarrier, dif_pos nonempty]
    exact Finset.min'_le _ _ available
  exact ordered

theorem selectCarrier_is_unique_minimum (eligible : Eligibility) (tried : Finset Carrier)
    (available : (eligibleUntried eligible tried).Nonempty) :
    selectCarrier eligible tried ∈ eligibleUntried eligible tried /\
      forall other, other ∈ eligibleUntried eligible tried ->
        (forall carrier, carrier ∈ eligibleUntried eligible tried ->
          Carrier.priorityRank other <= Carrier.priorityRank carrier) ->
        other = selectCarrier eligible tried := by
  refine ⟨selectCarrier_mem eligible tried available, ?_⟩
  intro other otherAvailable otherMinimal
  apply le_antisymm
  · exact otherMinimal _ (selectCarrier_mem eligible tried available)
  · exact selectCarrier_minimal eligible tried other otherAvailable

theorem design_router_rejects_single_perspective :
    designRouter .singlePerspective = .rejectFakeConsensus := by decide

inductive BoundedPassKind
  | metaLayerConvergence | repeatedReview | fixPass | terminationGate
  deriving DecidableEq, Fintype, Repr

def BoundedPassKind.LegalAt : BoundedPassKind -> Stage -> Prop
  | .metaLayerConvergence, .metaJudge
  | .repeatedReview, .fixOrDone
  | .fixPass, .fixOrDone
  | .terminationGate, .fixOrDone => True
  | _, _ => False

inductive IsolationStatus
  | available | unavailable
  deriving DecidableEq, Fintype, Repr

structure ProtocolConfig where
  eligible : Stage -> SeatRole -> Eligibility
  retryBudget : Stage -> SeatRole -> Carrier -> Nat
  dispatchPlan : DispatchPlan
  goalArtifact : GoalArtifact
  sharedPassBudget : Nat
  ownerAuthorizedAboveDefault : Bool
  initialIsolation : IsolationStatus

def defaultSharedPassBudget : Nat := 5

def PassBudgetAuthorized (config : ProtocolConfig) : Prop :=
  config.sharedPassBudget <= defaultSharedPassBudget \/ config.ownerAuthorizedAboveDefault = true

structure FlightKey where
  stage : Stage
  role : SeatRole
  carrier : Carrier
  deriving DecidableEq, Fintype, Repr

def flightKey (stage : Stage) (role : SeatRole) (carrier : Carrier) : FlightKey :=
  { stage, role, carrier }

inductive RunPhase
  | live | terminal | abstained
  deriving DecidableEq, Fintype, Repr

structure ProtocolState where
  stage : Stage
  phase : RunPhase
  remainingFlights : Finset FlightKey
  attemptedFlights : Finset FlightKey
  exhaustedFlights : Finset FlightKey
  passesUsed : Nat
  isolation : IsolationStatus
  designSituation : Option DesignSituation
  reviewExit : Option ReviewExit
  terminationExit : Option TerminationExit
  artifactEpoch : Nat
  reviewEpoch : Option Nat
  eventEpoch : Nat
  terminationEpoch : Option Nat

def initialState (config : ProtocolConfig) : ProtocolState :=
  { stage := .intake
    phase := .live
    remainingFlights := Finset.univ
    attemptedFlights := {}
    exhaustedFlights := {}
    passesUsed := 0
    isolation := config.initialIsolation
    designSituation := none
    reviewExit := none
    terminationExit := none
    artifactEpoch := 0
    reviewEpoch := none
    eventEpoch := 0
    terminationEpoch := none }

def triedAt (state : ProtocolState) (stage : Stage) (role : SeatRole) : Finset Carrier :=
  Finset.univ.filter fun carrier => flightKey stage role carrier ∈ state.attemptedFlights

def InitiallyAssigned (config : ProtocolConfig) (state : ProtocolState)
    (role : SeatRole) (carrier : Carrier) : Prop :=
  config.dispatchPlan.carrierAt state.stage role = some carrier /\
    triedAt state state.stage role = {}

def FallbackAssigned (config : ProtocolConfig) (state : ProtocolState)
    (role : SeatRole) (carrier : Carrier) : Prop :=
  (exists failedCarrier,
    flightKey state.stage role failedCarrier ∈ state.exhaustedFlights) /\
    (triedAt state state.stage role).Nonempty /\
    selectCarrier (config.eligible state.stage role) (triedAt state state.stage role) = carrier

def CarrierAssigned (config : ProtocolConfig) (state : ProtocolState)
    (role : SeatRole) (carrier : Carrier) : Prop :=
  InitiallyAssigned config state role carrier \/ FallbackAssigned config state role carrier

structure AuthorizedReport (config : ProtocolConfig) (state : ProtocolState)
    (role : SeatRole) {Verdict : Type} (report : WorkerReport Verdict) : Prop where
  legal : CarrierLegalAt state.stage role report.carrier
  roleMatches : report.view.role = role
  eligible : config.eligible state.stage role report.carrier = true
  untried : report.carrier ∉ triedAt state state.stage role
  assigned : CarrierAssigned config state role report.carrier
  complete : Complete report.carrier report.completionObservation
  isolatedView : report.view.IsolatedComplete config.goalArtifact
  exposureMatches : report.view.exposure = priorExposure report.carrier

def ThinkingResults.DispatchAuthorized (config : ProtocolConfig) (state : ProtocolState)
    (results : ThinkingResults) : Prop :=
  forall seat, AuthorizedReport config state seat.role (results seat).toWorkerReport

def ReviewResults.DispatchAuthorized (config : ProtocolConfig) (state : ProtocolState)
    (results : ReviewResults) : Prop :=
  forall seat, AuthorizedReport config state seat.role (results seat)

def TerminationSeatResult.DispatchAuthorized (config : ProtocolConfig) (state : ProtocolState)
    {seat : TerminationSeat} : TerminationSeatResult seat -> Prop
  | .completed report _ => AuthorizedReport config state seat.role report
  | .invalid | .missing => True

def TerminationObservation.DispatchAuthorized
    (config : ProtocolConfig) (state : ProtocolState)
    (observation : TerminationObservation) : Prop :=
  forall seat, (observation.result seat).DispatchAuthorized config state

def ThinkingResults.attemptKeys (state : ProtocolState)
    (results : ThinkingResults) : Finset FlightKey :=
  Finset.univ.biUnion fun seat =>
    {flightKey state.stage seat.role (results seat).toWorkerReport.carrier}

def ReviewResults.attemptKeys (state : ProtocolState)
    (results : ReviewResults) : Finset FlightKey :=
  Finset.univ.biUnion fun seat => {flightKey state.stage seat.role (results seat).carrier}

def TerminationSeatResult.attemptKeys (state : ProtocolState) {seat : TerminationSeat} :
    TerminationSeatResult seat -> Finset FlightKey
  | .completed report _ => {flightKey state.stage seat.role report.carrier}
  | .invalid | .missing => {}

def TerminationObservation.attemptKeys (state : ProtocolState)
    (observation : TerminationObservation) : Finset FlightKey :=
  Finset.univ.biUnion fun seat => (observation.result seat).attemptKeys state

inductive DesignAction : DesignExit -> Type
  | advance : DesignAction .implement
  | converge : DesignAction .metaLayerConvergence
  | abstainEscalate : DesignAction .abstainEscalate
  | rejectFakeConsensus : DesignAction .rejectFakeConsensus

inductive ReviewAction : ReviewExit -> Type
  | repair : ReviewAction .fix
  | terminationCandidate : ReviewAction .done
  | requestUserDecision : ReviewAction .userDecisionOrBoundedPass
  | anotherBoundedPass : ReviewAction .userDecisionOrBoundedPass

inductive TerminationGapOwner
  | engineering | caller | maintainer | unresolved
  deriving DecidableEq, Fintype, Repr

inductive AdvanceCondition (config : ProtocolConfig) (state : ProtocolState) : Type
  | intake (atStage : state.stage = .intake)
  | workerMode (atStage : state.stage = .chooseWorkerMode)
  | thinking (atStage : state.stage = .thinkingPanelWorkers)
      (compatible : PlanCompatibility) (results : ThinkingResults)
      (authorized : results.DispatchAuthorized config state)
  | metaJudge (atStage : state.stage = .metaJudge)
      (situation : DesignSituation) (recorded : state.designSituation = some situation)
      (routed : designRouter situation = .implement)
  | implementation (atStage : state.stage = .implementationWorker)
      (result : WorkerReport Unit)
      (authorized : AuthorizedReport config state .implementation result)
  | review (atStage : state.stage = .reviewTripletWorkers)
      (results : ReviewResults) (authorized : results.DispatchAuthorized config state)

def AdvanceCondition.nextState {config : ProtocolConfig} {state : ProtocolState}
    (condition : AdvanceCondition config state) (target : Stage) : ProtocolState :=
  match condition with
  | .thinking _ compatible results _ =>
      { state with
        stage := target
        attemptedFlights := state.attemptedFlights ∪ results.attemptKeys state
        designSituation := some (thinkingSituation compatible results) }
  | .implementation _ result _ =>
      { state with
        stage := target
        attemptedFlights := insert (flightKey state.stage .implementation result.carrier)
          state.attemptedFlights
        artifactEpoch := state.artifactEpoch + 1
        reviewExit := none
        reviewEpoch := none }
  | .review _ results _ =>
      { state with
        stage := target
        attemptedFlights := state.attemptedFlights ∪ results.attemptKeys state
        reviewExit := some (reviewRouter (reviewObservation results))
        reviewEpoch := some state.artifactEpoch }
  | _ => { state with stage := target }

inductive AbstainCondition (config : ProtocolConfig) (state : ProtocolState) : Prop
  | carrierExhausted (role : SeatRole)
      (legalRole : exists carrier, CarrierLegalAt state.stage role carrier)
      (exhausted : selectCarrier (config.eligible state.stage role)
        (triedAt state state.stage role) = .abstain)
  | isolationUnavailable (unavailable : state.isolation = .unavailable)
  | designStall (atStage : state.stage = .metaJudge)
      (recorded : state.designSituation = some .boundedStall)
  | designFakeConsensus (atStage : state.stage = .metaJudge)
      (recorded : state.designSituation = some .singlePerspective)
  | reviewUserDecision (atStage : state.stage = .fixOrDone)
      (recorded : state.reviewExit = some .userDecisionOrBoundedPass)

inductive Event
  | flightFailure (stage : Stage) (role : SeatRole) (carrier : Carrier) (attempts : Nat)
  | advance (source target : Stage)
  | boundedPass (stage : Stage) (kind : BoundedPassKind)
  | finish
  | abstain (stage : Stage)
  deriving DecidableEq, Repr

def FinishPrecondition (state : ProtocolState) : Prop :=
  state.phase = .live /\ state.stage = .fixOrDone /\ state.isolation = .available /\
    state.reviewExit = some .done /\ state.reviewEpoch = some state.artifactEpoch /\
    state.terminationExit = some .permitClaim /\
    state.terminationEpoch = some state.eventEpoch

def terminationNextState (state : ProtocolState) (observation : TerminationObservation)
    (owner : TerminationGapOwner) : ProtocolState :=
  match terminationRouter observation with
  | .permitClaim =>
      { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
        terminationExit := some .permitClaim
        terminationEpoch := some (state.eventEpoch + 1) }
  | .continueAgainstGap =>
      if owner = .engineering then
        { state with
          passesUsed := state.passesUsed + 1
          attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
          reviewExit := some .fix
          reviewEpoch := none
          terminationExit := some .continueAgainstGap }
      else
        { state with
          passesUsed := state.passesUsed + 1
          attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
          phase := .abstained
          terminationExit := some .continueAgainstGap }
  | .rejectFakeConsensus =>
      { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
        phase := .abstained
        terminationExit := some .rejectFakeConsensus }
  | .escalateEvidenceGap =>
      { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
        phase := .abstained
        terminationExit := some .escalateEvidenceGap }

inductive ProtocolAction (config : ProtocolConfig) :
    ProtocolState -> Event -> ProtocolState -> Prop
  | flightFailure (state : ProtocolState) (role : SeatRole) (carrier : Carrier) (attempts : Nat)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (legal : CarrierLegalAt state.stage role carrier)
      (eligible : config.eligible state.stage role carrier = true)
      (untried : carrier ∉ triedAt state state.stage role)
      (assigned : CarrierAssigned config state role carrier)
      (available : flightKey state.stage role carrier ∈ state.remainingFlights)
      (positive : 0 < attempts)
      (budgetExhausted : attempts = config.retryBudget state.stage role carrier) :
      ProtocolAction config state (.flightFailure state.stage role carrier attempts)
        { state with
          remainingFlights := state.remainingFlights.erase (flightKey state.stage role carrier)
          attemptedFlights := insert (flightKey state.stage role carrier) state.attemptedFlights
          exhaustedFlights := insert (flightKey state.stage role carrier) state.exhaustedFlights }
  | advance (state : ProtocolState) (target : Stage)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (authorized : AdvanceCondition config state)
      (successor : state.stage.Successor target) :
      ProtocolAction config state (.advance state.stage target) (authorized.nextState target)
  | designConvergence (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atMeta : state.stage = .metaJudge)
      (recorded : state.designSituation = some .compatiblePlans)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolAction config state (.boundedPass state.stage .metaLayerConvergence)
        { state with
          passesUsed := state.passesUsed + 1
          designSituation := some .unanimousActionable }
  | designConvergenceExhausted (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atMeta : state.stage = .metaJudge)
      (recorded : state.designSituation = some .compatiblePlans)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolAction config state (.boundedPass state.stage .metaLayerConvergence)
        { state with passesUsed := state.passesUsed + 1, phase := .abstained }
  | repeatedReview (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (needsPass : state.reviewExit = some .userDecisionOrBoundedPass)
      (results : ReviewResults) (authorized : results.DispatchAuthorized config state)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolAction config state (.boundedPass state.stage .repeatedReview)
        { state with
          passesUsed := state.passesUsed + 1
          attemptedFlights := state.attemptedFlights ∪ results.attemptKeys state
          reviewExit := some (reviewRouter (reviewObservation results))
          reviewEpoch := some state.artifactEpoch }
  | fixAndReview (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone) (needsFix : state.reviewExit = some .fix)
      (implementation : WorkerReport Unit)
      (implementationAuthorized : AuthorizedReport config state .implementation implementation)
      (results : ReviewResults) (reviewAuthorized : results.DispatchAuthorized config state)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolAction config state (.boundedPass state.stage .fixPass)
        { state with
          passesUsed := state.passesUsed + 1
          attemptedFlights := insert
            (flightKey state.stage .implementation implementation.carrier)
            (state.attemptedFlights ∪ results.attemptKeys state)
          artifactEpoch := state.artifactEpoch + 1
          reviewExit := some (reviewRouter (reviewObservation results))
          reviewEpoch := some (state.artifactEpoch + 1) }
  | terminationGate (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (reviewDone : state.reviewExit = some .done)
      (reviewCurrent : state.reviewEpoch = some state.artifactEpoch)
      (noPermit : state.terminationExit ≠ some .permitClaim)
      (observation : TerminationObservation)
      (authorized : observation.DispatchAuthorized config state)
      (owner : TerminationGapOwner)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolAction config state (.boundedPass state.stage .terminationGate)
        (terminationNextState state observation owner)
  | finish (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (ready : FinishPrecondition state) :
      ProtocolAction config state .finish { state with phase := .terminal }
  | abstain (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (reason : AbstainCondition config state) :
      ProtocolAction config state (.abstain state.stage) { state with phase := .abstained }

def permitEpochAfterEvent (start raw : ProtocolState) : Option Nat :=
  if start.terminationExit = some .permitClaim then
    start.terminationEpoch
  else if raw.terminationExit = some .permitClaim then
    some (start.eventEpoch + 1)
  else
    raw.terminationEpoch

def recordEvent (start raw : ProtocolState) : ProtocolState :=
  { raw with
    eventEpoch := start.eventEpoch + 1
    terminationEpoch := permitEpochAfterEvent start raw }

def StateWellFormed (state : ProtocolState) : Prop :=
  forall epoch, state.terminationEpoch = some epoch -> epoch <= state.eventEpoch

def ProtocolStep (config : ProtocolConfig) (start : ProtocolState)
    (event : Event) (final : ProtocolState) : Prop :=
  StateWellFormed start /\
    exists raw, ProtocolAction config start event raw /\ final = recordEvent start raw

namespace ProtocolStep

theorem ofAction {config : ProtocolConfig} {start raw : ProtocolState} {event : Event}
    (wellFormed : StateWellFormed start)
    (action : ProtocolAction config start event raw) :
    ProtocolStep config start event (recordEvent start raw) :=
  ⟨wellFormed, raw, action, rfl⟩

theorem event_epoch_strict {config : ProtocolConfig} {start final : ProtocolState} {event : Event}
    (step : ProtocolStep config start event final) :
    final.eventEpoch = start.eventEpoch + 1 := by
  rcases step with ⟨wellFormed, raw, action, rfl⟩
  rfl

end ProtocolStep

structure InlineConsensusModel where
  stageRelation : Stage -> Stage -> Prop
  fallbackSelector : Eligibility -> Finset Carrier -> Carrier
  dispatchShape : DispatchPlan -> Prop
  completionPredicate : Carrier -> CompletionObservation -> Prop
  designRoute : DesignSituation -> DesignExit
  reviewRoute : ReviewObservation -> ReviewExit
  terminationRoute : TerminationObservation -> TerminationExit
  rosterContract : TerminationRoster -> Prop
  transition : ProtocolConfig -> ProtocolState -> Event -> ProtocolState -> Prop

def inlineConsensusModel : InlineConsensusModel :=
  { stageRelation := Stage.Successor
    fallbackSelector := selectCarrier
    dispatchShape := fun plan =>
      MultiSeatLayout plan.thinking /\ MultiSeatLayout plan.review /\
        MultiSeatLayout plan.termination
    completionPredicate := Complete
    designRoute := designRouter
    reviewRoute := reviewRouter
    terminationRoute := terminationRouter
    rosterContract := ExactRoster
    transition := ProtocolStep }

abbrev Rule := TerminationObservation -> Bool

def TerminationHazard (observation : TerminationObservation) : Prop :=
  Not (ExactRoster observation.roster) \/ exists seat,
    (observation.result seat).isSatisfiedBool = false

def Sound (rule : Rule) : Prop :=
  forall observation, rule observation = true -> Not (TerminationHazard observation)

def RuleLE (left right : Rule) : Prop :=
  forall observation, left observation = true -> right observation = true

def Greatest (rule : Rule) : Prop := IsGreatest {candidate | Sound candidate} rule

def terminationAdmits : Rule :=
  fun observation => decide (terminationRouter observation = .permitClaim)

def optimalTerminationRule : Rule :=
  fun observation => decide (inlineConsensusModel.terminationRoute observation = .permitClaim)

end D5.S0.History.Consensus.InlineConsensusOptimality
