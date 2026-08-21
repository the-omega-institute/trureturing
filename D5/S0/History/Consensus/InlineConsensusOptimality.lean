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

theorem selectCarrier_eq_abstain_iff (eligible : Eligibility) (tried : Finset Carrier) :
    selectCarrier eligible tried = .abstain <-> eligibleUntried eligible tried = {} := by
  constructor
  · intro selected
    by_contra nonempty
    have available : (eligibleUntried eligible tried).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr nonempty
    have member : (eligibleUntried eligible tried).min' available ∈
        eligibleUntried eligible tried := Finset.min'_mem _ _
    have workerCarrier : (eligibleUntried eligible tried).min' available ≠ .abstain := by
      intro abstain
      rw [abstain] at member
      simp [eligibleUntried] at member
    exact workerCarrier (by simpa [selectCarrier, available] using selected)
  · intro empty
    simp [selectCarrier, empty]

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
  workerModeEligibility : Eligibility
  eligible : Stage -> SeatRole -> Eligibility
  retryBudget : Stage -> SeatRole -> Carrier -> Nat
  dispatchPlan : DispatchPlan
  initialPlanCompatible : InitialPlanCompatible eligible dispatchPlan
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

def FallbackAssigned (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState)
    (role : SeatRole) (carrier : Carrier) : Prop :=
  (exists failedCarrier,
    flightKey state.stage role failedCarrier ∈ state.exhaustedFlights) /\
    (triedAt state state.stage role).Nonempty /\
    model.fallbackSelector (config.eligible state.stage role)
      (triedAt state state.stage role) = carrier

def CarrierAssigned (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState)
    (role : SeatRole) (carrier : Carrier) : Prop :=
  InitiallyAssigned config state role carrier \/ FallbackAssigned model config state role carrier

theorem initial_plan_ineligible_is_rejected
    {eligible : Stage -> SeatRole -> Eligibility} {plan : DispatchPlan}
    {stage : Stage} {role : SeatRole} {carrier : Carrier}
    (planned : plan.carrierAt stage role = some carrier)
    (ineligible : eligible stage role carrier = false) :
    Not (InitialPlanCompatible eligible plan) := by
  intro compatible
  have eligibleCarrier := (compatible stage role carrier planned).2
  simp_all

private theorem DispatchPlan.carrierAt_exists_of_legal (plan : DispatchPlan)
    (stage : Stage) (role : SeatRole) (legal : role.LegalAt stage) :
    exists carrier, plan.carrierAt stage role = some carrier := by
  cases stage <;> cases role <;>
    simp_all [SeatRole.LegalAt, SeatRole.IsThinking, SeatRole.IsReview,
      SeatRole.IsTermination, DispatchPlan.carrierAt]

theorem legal_worker_stage_initially_progresses_or_abstains
    (model : InlineConsensusModel) (config : ProtocolConfig) (state : ProtocolState)
    (role : SeatRole)
    (legal : role.LegalAt state.stage)
    (untried : triedAt state state.stage role = {}) :
    (exists carrier,
      InitiallyAssigned config state role carrier /\
        CarrierLegalAt state.stage role carrier /\
        config.eligible state.stage role carrier = true) \/
      model.fallbackSelector (config.eligible state.stage role)
        (triedAt state state.stage role) = .abstain := by
  left
  obtain ⟨carrier, planned⟩ :=
    config.dispatchPlan.carrierAt_exists_of_legal state.stage role legal
  have compatible := config.initialPlanCompatible state.stage role carrier planned
  exact ⟨carrier, ⟨planned, untried⟩, compatible⟩

structure AuthorizedReport (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState)
    (role : SeatRole) {Verdict : Type} (report : WorkerReport Verdict) : Prop where
  legal : CarrierLegalAt state.stage role report.carrier
  roleMatches : report.view.role = role
  eligible : config.eligible state.stage role report.carrier = true
  untried : report.carrier ∉ triedAt state state.stage role
  assigned : CarrierAssigned model config state role report.carrier
  complete : model.completionPredicate report.carrier report.completionObservation
  isolatedView : report.view.IsolatedComplete config.goalArtifact
  exposureMatches : report.view.exposure = priorExposure report.carrier

def ThinkingResults.DispatchAuthorized (model : InlineConsensusModel)
    (config : ProtocolConfig) (state : ProtocolState) (results : ThinkingResults) : Prop :=
  forall seat, AuthorizedReport model config state seat.role (results seat).toWorkerReport

def ReviewResults.DispatchAuthorized (model : InlineConsensusModel)
    (config : ProtocolConfig) (state : ProtocolState) (results : ReviewResults) : Prop :=
  forall seat, AuthorizedReport model config state seat.role (results seat)

def TerminationSeatResult.DispatchAuthorized (model : InlineConsensusModel)
    (config : ProtocolConfig) (state : ProtocolState) {seat : TerminationSeat} :
    TerminationSeatResult seat -> Prop
  | .completed report _ => AuthorizedReport model config state seat.role report
  | .invalid | .missing => True

def TerminationObservation.DispatchAuthorized
    (model : InlineConsensusModel) (config : ProtocolConfig) (state : ProtocolState)
    (observation : TerminationObservation) : Prop :=
  forall seat, (observation.result seat).DispatchAuthorized model config state

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

inductive AdvanceCondition (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState) : Type
  | intake (atStage : state.stage = .intake)
  | workerMode (atStage : state.stage = .chooseWorkerMode) (carrier : Carrier)
      (selected : model.fallbackSelector config.workerModeEligibility {} = carrier)
      (available : config.workerModeEligibility carrier = true)
      (worker : carrier != .abstain)
  | thinking (atStage : state.stage = .thinkingPanelWorkers)
      (compatible : PlanCompatibility) (results : ThinkingResults)
      (authorized : results.DispatchAuthorized model config state)
  | metaJudge (atStage : state.stage = .metaJudge)
      (situation : DesignSituation) (recorded : state.designSituation = some situation)
      (routed : model.designRoute situation = .implement)
  | implementation (atStage : state.stage = .implementationWorker)
      (result : WorkerReport Unit)
      (authorized : AuthorizedReport model config state .implementation result)
  | review (atStage : state.stage = .reviewTripletWorkers)
      (results : ReviewResults) (authorized : results.DispatchAuthorized model config state)

def AdvanceCondition.attemptKeys {model : InlineConsensusModel} {config : ProtocolConfig}
    {state : ProtocolState} : AdvanceCondition model config state -> Finset FlightKey
  | .thinking _ _ results _ => results.attemptKeys state
  | .implementation _ result _ => {flightKey state.stage .implementation result.carrier}
  | .review _ results _ => results.attemptKeys state
  | _ => {}

def AdvanceCondition.nextState {model : InlineConsensusModel} {config : ProtocolConfig}
    {state : ProtocolState} (condition : AdvanceCondition model config state)
    (target : Stage) : ProtocolState :=
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
        reviewExit := some (model.reviewRoute (reviewObservation results))
        reviewEpoch := some state.artifactEpoch }
  | _ => { state with stage := target }

inductive AbstainCondition (model : InlineConsensusModel) (config : ProtocolConfig)
    (state : ProtocolState) : Prop
  | carrierExhausted (role : SeatRole)
      (legalRole : exists carrier, CarrierLegalAt state.stage role carrier)
      (exhausted : model.fallbackSelector (config.eligible state.stage role)
        (triedAt state state.stage role) = .abstain)
  | workerModeUnavailable (atStage : state.stage = .chooseWorkerMode)
      (unavailable : model.fallbackSelector config.workerModeEligibility {} = .abstain)
  | isolationUnavailable (unavailable : state.isolation = .unavailable)
  | designStall (atStage : state.stage = .metaJudge)
      (recorded : state.designSituation = some .boundedStall)
  | designFakeConsensus (atStage : state.stage = .metaJudge)
      (recorded : state.designSituation = some .singlePerspective)
  | reviewUserDecision (atStage : state.stage = .fixOrDone)
      (recorded : state.reviewExit = some .userDecisionOrBoundedPass)

inductive Event
  | flightFailure (stage : Stage) (role : SeatRole) (carrier : Carrier) (attempts : Nat)
  | advance (source target : Stage) (attempted : Finset FlightKey)
  | boundedPass (stage : Stage) (kind : BoundedPassKind) (attempted : Finset FlightKey)
  | finish
  | abstain (stage : Stage)
  deriving DecidableEq

def FinishPrecondition (state : ProtocolState) : Prop :=
  state.phase = .live /\ state.stage = .fixOrDone /\ state.isolation = .available /\
    state.reviewExit = some .done /\ state.reviewEpoch = some state.artifactEpoch /\
    state.terminationExit = some .permitClaim /\
    state.terminationEpoch = some state.eventEpoch

def terminationNextState (model : InlineConsensusModel) (state : ProtocolState)
    (observation : TerminationObservation) (owner : TerminationGapOwner) : ProtocolState :=
  match model.terminationRoute observation with
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

inductive ProtocolAction (model : InlineConsensusModel) (config : ProtocolConfig) :
    ProtocolState -> Event -> ProtocolState -> Prop
  | flightFailure (state : ProtocolState) (role : SeatRole) (carrier : Carrier) (attempts : Nat)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (legal : CarrierLegalAt state.stage role carrier)
      (eligible : config.eligible state.stage role carrier = true)
      (untried : carrier ∉ triedAt state state.stage role)
      (assigned : CarrierAssigned model config state role carrier)
      (available : flightKey state.stage role carrier ∈ state.remainingFlights)
      (positive : 0 < attempts)
      (budgetExhausted : attempts = config.retryBudget state.stage role carrier) :
      ProtocolAction model config state (.flightFailure state.stage role carrier attempts)
        { state with
          remainingFlights := state.remainingFlights.erase (flightKey state.stage role carrier)
          attemptedFlights := insert (flightKey state.stage role carrier) state.attemptedFlights
          exhaustedFlights := insert (flightKey state.stage role carrier) state.exhaustedFlights }
  | advance (state : ProtocolState) (target : Stage)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (authorized : AdvanceCondition model config state)
      (attemptsFresh : Disjoint authorized.attemptKeys state.attemptedFlights)
      (successor : model.stageRelation state.stage target) :
      ProtocolAction model config state
        (.advance state.stage target authorized.attemptKeys) (authorized.nextState target)
  | designConvergence (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atMeta : state.stage = .metaJudge)
      (recorded : state.designSituation = some .compatiblePlans)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolAction model config state (.boundedPass state.stage .metaLayerConvergence {})
        { state with
          passesUsed := state.passesUsed + 1
          designSituation := some .unanimousActionable }
  | designConvergenceExhausted (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atMeta : state.stage = .metaJudge)
      (recorded : state.designSituation = some .compatiblePlans)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolAction model config state (.boundedPass state.stage .metaLayerConvergence {})
        { state with passesUsed := state.passesUsed + 1, phase := .abstained }
  | repeatedReview (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (needsPass : state.reviewExit = some .userDecisionOrBoundedPass)
      (results : ReviewResults) (authorized : results.DispatchAuthorized model config state)
      (attemptsFresh : Disjoint (results.attemptKeys state) state.attemptedFlights)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolAction model config state
        (.boundedPass state.stage .repeatedReview (results.attemptKeys state))
        { state with
          passesUsed := state.passesUsed + 1
          attemptedFlights := state.attemptedFlights ∪ results.attemptKeys state
          reviewExit := some (model.reviewRoute (reviewObservation results))
          reviewEpoch := some state.artifactEpoch }
  | fixAndReview (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone) (needsFix : state.reviewExit = some .fix)
      (implementation : WorkerReport Unit)
      (implementationAuthorized :
        AuthorizedReport model config state .implementation implementation)
      (results : ReviewResults) (reviewAuthorized : results.DispatchAuthorized model config state)
      (attemptsFresh : Disjoint
        (insert (flightKey state.stage .implementation implementation.carrier)
          (results.attemptKeys state)) state.attemptedFlights)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolAction model config state
        (.boundedPass state.stage .fixPass
          (insert (flightKey state.stage .implementation implementation.carrier)
            (results.attemptKeys state)))
        { state with
          passesUsed := state.passesUsed + 1
          attemptedFlights := insert
            (flightKey state.stage .implementation implementation.carrier)
            (state.attemptedFlights ∪ results.attemptKeys state)
          artifactEpoch := state.artifactEpoch + 1
          reviewExit := some (model.reviewRoute (reviewObservation results))
          reviewEpoch := some (state.artifactEpoch + 1) }
  | terminationGate (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (reviewDone : state.reviewExit = some .done)
      (reviewCurrent : state.reviewEpoch = some state.artifactEpoch)
      (noPermit : state.terminationExit ≠ some .permitClaim)
      (observation : TerminationObservation)
      (authorized : observation.DispatchAuthorized model config state)
      (attemptsFresh : Disjoint (observation.attemptKeys state) state.attemptedFlights)
      (owner : TerminationGapOwner)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolAction model config state
        (.boundedPass state.stage .terminationGate (observation.attemptKeys state))
        (terminationNextState model state observation owner)
  | finish (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (ready : FinishPrecondition state) :
      ProtocolAction model config state .finish { state with phase := .terminal }
  | abstain (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (reason : AbstainCondition model config state) :
      ProtocolAction model config state (.abstain state.stage) { state with phase := .abstained }

def carriedPermit (start raw : ProtocolState) : Bool :=
  start.terminationExit == some .permitClaim && raw.terminationExit == some .permitClaim

def terminationExitAfterEvent (start raw : ProtocolState) : Option TerminationExit :=
  if carriedPermit start raw then none else raw.terminationExit

def permitEpochAfterEvent (start raw : ProtocolState) : Option Nat :=
  if carriedPermit start raw then none
  else if raw.terminationExit = some .permitClaim then
    some (start.eventEpoch + 1)
  else
    none

def recordEvent (start raw : ProtocolState) : ProtocolState :=
  { raw with
    eventEpoch := start.eventEpoch + 1
    terminationExit := terminationExitAfterEvent start raw
    terminationEpoch := permitEpochAfterEvent start raw }

def StateWellFormed (state : ProtocolState) : Prop :=
  forall epoch, state.terminationEpoch = some epoch -> epoch <= state.eventEpoch

def ProtocolStep (model : InlineConsensusModel) (config : ProtocolConfig) (start : ProtocolState)
    (event : Event) (final : ProtocolState) : Prop :=
  model.dispatchShape config.dispatchPlan /\ StateWellFormed start /\
    exists raw, ProtocolAction model config start event raw /\ final = recordEvent start raw

def InlineConsensusModel.transition (model : InlineConsensusModel) :
    ProtocolConfig -> ProtocolState -> Event -> ProtocolState -> Prop :=
  ProtocolStep model

namespace ProtocolStep

theorem ofAction {model : InlineConsensusModel} {config : ProtocolConfig}
    {start raw : ProtocolState} {event : Event}
    (dispatchShape : model.dispatchShape config.dispatchPlan)
    (wellFormed : StateWellFormed start)
    (action : ProtocolAction model config start event raw) :
    ProtocolStep model config start event (recordEvent start raw) :=
  ⟨dispatchShape, wellFormed, raw, action, rfl⟩

theorem event_epoch_strict {model : InlineConsensusModel} {config : ProtocolConfig}
    {start final : ProtocolState} {event : Event}
    (step : ProtocolStep model config start event final) :
    final.eventEpoch = start.eventEpoch + 1 := by
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  rfl

end ProtocolStep

abbrev Rule := TerminationObservation -> Bool

def TerminationHazard (model : InlineConsensusModel)
    (observation : TerminationObservation) : Prop :=
  Not (model.rosterContract observation.roster) \/ exists seat,
    (observation.result seat).isSatisfiedBool = false

def Sound (model : InlineConsensusModel) (rule : Rule) : Prop :=
  forall observation, rule observation = true -> Not (TerminationHazard model observation)

def RuleLE (left right : Rule) : Prop :=
  forall observation, left observation = true -> right observation = true

def Greatest (model : InlineConsensusModel) (rule : Rule) : Prop :=
  IsGreatest {candidate | Sound model candidate} rule

def StrictBelow (left right : Rule) : Prop :=
  RuleLE left right /\ exists observation, right observation = true /\ left observation = false

def terminationAdmits (model : InlineConsensusModel) : Rule :=
  fun observation => decide (model.terminationRoute observation = .permitClaim)

def optimalTerminationRule : Rule :=
  terminationAdmits inlineConsensusModel

def alwaysAbstain : Rule := fun _ => false

def majorityAdmit : Rule := fun observation =>
  exactRosterBool observation.roster &&
    (((observation.result .criterionEvidence).isSatisfiedBool &&
        (observation.result .residualGap).isSatisfiedBool) ||
      ((observation.result .criterionEvidence).isSatisfiedBool &&
        (observation.result .claimIntegrity).isSatisfiedBool) ||
      ((observation.result .residualGap).isSatisfiedBool &&
        (observation.result .claimIntegrity).isSatisfiedBool))

end D5.S0.History.Consensus.InlineConsensusOptimality
