/- GID: D5/S0/History/Consensus/InlineConsensusOptimality
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite protocol routers are maximal safe rules; runs consume bounded resources. -/
/- Snapshot correspondence only; it is not a theorem premise.
   beta.32 SKILL.md SHA-256 ab688e34f2b183291958f78b2d9ff6905d7330f3844668c5103026790d8b4cbf
   CODEX_WORKER_SPEC.md SHA-256 700237b1a1389002215272874e8c9cd7b17a130f0d0eaf7bb20cf9b39f49829d
   A later plugin version may falsify it without falsifying these theorems.
   No statement asserts a fact about any current or future plugin version. -/
import Mathlib
namespace D5.S0.History.Consensus.InlineConsensusOptimality
inductive Stage
  | intake | chooseWorkerMode | thinkingPanelWorkers | metaJudge
  | implementationWorker | reviewTripletWorkers | fixOrDone
  deriving DecidableEq, Fintype, Repr
def Stage.rank : Stage -> Nat
  | .intake => 0 | .chooseWorkerMode => 1 | .thinkingPanelWorkers => 2
  | .metaJudge => 3 | .implementationWorker => 4
  | .reviewTripletWorkers => 5 | .fixOrDone => 6
def Stage.next : Stage -> Option Stage
  | .intake => some .chooseWorkerMode | .chooseWorkerMode => some .thinkingPanelWorkers
  | .thinkingPanelWorkers => some .metaJudge | .metaJudge => some .implementationWorker
  | .implementationWorker => some .reviewTripletWorkers
  | .reviewTripletWorkers => some .fixOrDone
  | .fixOrDone => none
theorem stage_order_is_the_protocol_order :
    Stage.next .intake = some .chooseWorkerMode /\
      Stage.next .chooseWorkerMode = some .thinkingPanelWorkers /\
      Stage.next .thinkingPanelWorkers = some .metaJudge /\
      Stage.next .metaJudge = some .implementationWorker /\
      Stage.next .implementationWorker = some .reviewTripletWorkers /\
      Stage.next .reviewTripletWorkers = some .fixOrDone /\
      Stage.next .fixOrDone = none := by decide
def Stage.Successor (source target : Stage) : Prop := source.next = some target
theorem stage_successor_is_unique (source first second : Stage) (hFirst : source.Successor first)
    (hSecond : source.Successor second) : first = second := by
  exact Option.some.inj (hFirst.symm.trans hSecond)
inductive Carrier
  | codexCli | nyxidOracle | isolatedTokenSubagent | abstain
  deriving DecidableEq, Fintype, Repr
def Carrier.priorityRank : Carrier -> Nat
  | .codexCli => 0
  | .nyxidOracle => 1
  | .isolatedTokenSubagent => 2
  | .abstain => 3
theorem carrier_priority_is_the_protocol_priority :
    Carrier.priorityRank .codexCli = 0 /\ Carrier.priorityRank .nyxidOracle = 1 /\
      Carrier.priorityRank .isolatedTokenSubagent = 2 /\ Carrier.priorityRank .abstain = 3 := by
  decide
abbrev Eligibility := Carrier -> Bool
def selectCarrier (eligible : Eligibility) (tried : Finset Carrier) : Carrier :=
  if eligible .codexCli && .codexCli ∉ tried then .codexCli
  else if eligible .nyxidOracle && .nyxidOracle ∉ tried then .nyxidOracle
  else if eligible .isolatedTokenSubagent && .isolatedTokenSubagent ∉ tried then
    .isolatedTokenSubagent
  else .abstain
structure CompletionObservation where
  carrierExitedZero : Bool
  resultArtifactExists : Bool
  envelopeValid : Bool
  verdictAllowed : Bool
  sentinelExists : Bool
  deriving DecidableEq, Fintype, Repr
def Complete (observation : CompletionObservation) : Prop :=
  observation.carrierExitedZero = true /\
    observation.resultArtifactExists = true /\
    observation.envelopeValid = true /\
    observation.verdictAllowed = true /\
    observation.sentinelExists = true
inductive CompletionConjunct | carrierExit | resultArtifact | envelope | verdict | sentinel
  deriving DecidableEq, Fintype, Repr
inductive ForbiddenCompletionProxy
  | processSnapshot | logText | stdoutMarker | emptyGitStatus
  deriving DecidableEq, Fintype, Repr
def evidenceFromProxyOnly (_ : ForbiddenCompletionProxy) : CompletionObservation :=
  { carrierExitedZero := false
    resultArtifactExists := false
    envelopeValid := false
    verdictAllowed := false
    sentinelExists := false }
inductive GoalArtifactSnapshot | complete
  deriving DecidableEq, Fintype, Repr
inductive SeatRole
  | teleology | parsimony | fidelity | naturalOwnership | proportionalContainment | worth
  | implementation
  | architectureReview | qualityReview | testsReview
  | criterionEvidence | residualGap | claimIntegrity
  deriving DecidableEq, Fintype, Repr
inductive PriorExposure
  | repoPriorExposed | externalPriorExposed | callerPriorExposed | noCarrier
  deriving DecidableEq, Fintype, Repr
def priorExposure : Carrier -> PriorExposure
  | .codexCli => .repoPriorExposed
  | .nyxidOracle => .externalPriorExposed
  | .isolatedTokenSubagent => .callerPriorExposed
  | .abstain => .noCarrier
theorem prior_exposure_is_per_carrier :
    priorExposure .codexCli = .repoPriorExposed /\
      priorExposure .nyxidOracle = .externalPriorExposed /\
      priorExposure .isolatedTokenSubagent = .callerPriorExposed /\
      priorExposure .abstain = .noCarrier := by decide
structure SeatView where
  goalArtifact : GoalArtifactSnapshot
  role : SeatRole
  exposure : PriorExposure
  deriving DecidableEq, Fintype, Repr
def seat_view_information_content : SeatView ≃ GoalArtifactSnapshot × SeatRole × PriorExposure where
  toFun view := (view.goalArtifact, view.role, view.exposure)
  invFun data := { goalArtifact := data.1, role := data.2.1, exposure := data.2.2 }
  left_inv view := by cases view; rfl
  right_inv data := by rcases data with ⟨goal, role, exposure⟩; rfl
structure CompletedSeatResult where
  view : SeatView
  carrier : Carrier
  workerCarrier : carrier ≠ .abstain
  completionObservation : CompletionObservation
  complete : Complete completionObservation
  exposureMatches : view.exposure = priorExposure carrier
def correlatedConclusion (_ : Carrier) (latent : Bool) : Bool := latent
inductive DesignSituation
  | unanimousActionable | compatiblePlans | boundedStall | singlePerspective
  deriving DecidableEq, Fintype, Repr
inductive DesignExit
  | implement | metaLayerConvergence | abstainEscalate | rejectFakeConsensus
  deriving DecidableEq, Fintype, Repr
def designRouter : DesignSituation -> DesignExit
  | .unanimousActionable => .implement
  | .compatiblePlans => .metaLayerConvergence
  | .boundedStall => .abstainEscalate
  | .singlePerspective => .rejectFakeConsensus
theorem design_router_rejects_single_perspective :
    designRouter .singlePerspective = .rejectFakeConsensus := by decide
inductive ReviewVerdict
  | approve | comment | reject
  deriving DecidableEq, Fintype, Repr
abbrev ReviewObservation := Fin 3 -> ReviewVerdict
inductive ReviewExit
  | fix | done | userDecisionOrBoundedPass
  deriving DecidableEq, Fintype, Repr
def reviewHasBool (observation : ReviewObservation) (verdict : ReviewVerdict) : Bool :=
  observation 0 == verdict || observation 1 == verdict || observation 2 == verdict
def reviewRouter (observation : ReviewObservation) : ReviewExit :=
  if reviewHasBool observation .reject then .fix
  else if reviewHasBool observation .approve then .done
  else .userDecisionOrBoundedPass
inductive TerminationSeat
  | criterionEvidence | residualGap | claimIntegrity
  deriving DecidableEq, Fintype, Repr
def TerminationSeat.role : TerminationSeat -> SeatRole
  | .criterionEvidence => .criterionEvidence
  | .residualGap => .residualGap
  | .claimIntegrity => .claimIntegrity
inductive TerminationVerdict | satisfied | unsatisfied | abstain
  deriving DecidableEq, Fintype, Repr
inductive TerminationSeatResult (seat : TerminationSeat)
  | completed (evidence : CompletedSeatResult)
      (roleMatches : evidence.view.role = seat.role) (verdict : TerminationVerdict)
  | invalid | missing
abbrev TerminationRoster := Fin 3 -> Option TerminationSeat
structure TerminationObservation where
  roster : TerminationRoster
  result : (seat : TerminationSeat) -> TerminationSeatResult seat
def ExactRoster (roster : TerminationRoster) : Prop :=
  (roster 0).isSome = true /\ (roster 1).isSome = true /\ (roster 2).isSome = true /\
    roster 0 ≠ roster 1 /\ roster 0 ≠ roster 2 /\ roster 1 ≠ roster 2
def exactRosterBool (roster : TerminationRoster) : Bool :=
  (roster 0).isSome && (roster 1).isSome && (roster 2).isSome &&
    roster 0 != roster 1 && roster 0 != roster 2 && roster 1 != roster 2
def TerminationSeatResult.IsSatisfied {seat : TerminationSeat} :
    TerminationSeatResult seat -> Prop
  | .completed _ _ verdict => verdict = .satisfied
  | .invalid | .missing => False
def TerminationSeatResult.isSatisfiedBool {seat : TerminationSeat} :
    TerminationSeatResult seat -> Bool
  | .completed _ _ verdict => verdict == .satisfied
  | .invalid | .missing => false
def allSatisfied (observation : TerminationObservation) : Prop :=
  forall seat, (observation.result seat).IsSatisfied
def allSatisfiedBool (observation : TerminationObservation) : Bool :=
  (observation.result .criterionEvidence).isSatisfiedBool &&
    (observation.result .residualGap).isSatisfiedBool &&
    (observation.result .claimIntegrity).isSatisfiedBool
def anyUnsatisfiedBool (observation : TerminationObservation) : Bool :=
  match observation.result .criterionEvidence,
      observation.result .residualGap, observation.result .claimIntegrity with
  | .completed _ _ .unsatisfied, _, _ | _, .completed _ _ .unsatisfied, _
  | _, _, .completed _ _ .unsatisfied => true
  | _, _, _ => false
inductive TerminationExit
  | rejectFakeConsensus | permitClaim | continueAgainstGap | escalateEvidenceGap
  deriving DecidableEq, Fintype, Repr
def terminationRouter (observation : TerminationObservation) : TerminationExit :=
  if exactRosterBool observation.roster then
    if allSatisfiedBool observation then .permitClaim
    else if anyUnsatisfiedBool observation then .continueAgainstGap
    else .escalateEvidenceGap
  else .rejectFakeConsensus
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
inductive BoundedPassKind
  | metaLayerConvergence | repeatedReview | fixPass | terminationGate
  deriving DecidableEq, Fintype, Repr
def BoundedPassKind.LegalAt : BoundedPassKind -> Stage -> Prop
  | .metaLayerConvergence, .metaJudge | .repeatedReview, .reviewTripletWorkers
  | .fixPass, .fixOrDone | .terminationGate, .fixOrDone => True
  | _, _ => False
structure ProtocolConfig where
  eligible : Stage -> SeatRole -> Eligibility
  retryBudget : Stage -> SeatRole -> Carrier -> Nat
  sharedPassBudget : Nat
  ownerAuthorizedAboveDefault : Bool
def PassBudgetAuthorized (config : ProtocolConfig) : Prop :=
  config.sharedPassBudget <= 5 \/ config.ownerAuthorizedAboveDefault = true
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
inductive IsolationStatus | available | unavailable
  deriving DecidableEq, Fintype, Repr
structure ProtocolState where
  stage : Stage
  phase : RunPhase
  remainingFlights : Finset FlightKey
  passesUsed : Nat
  isolation : IsolationStatus
def initialState (_ : ProtocolConfig) : ProtocolState :=
  { stage := .intake
    phase := .live
    remainingFlights := Finset.univ
    passesUsed := 0
    isolation := .available }
def triedAt (state : ProtocolState) (stage : Stage) (role : SeatRole) : Finset Carrier :=
  Finset.univ.filter fun carrier =>
    flightKey stage role carrier ∉ state.remainingFlights
inductive AdvanceCondition (config : ProtocolConfig) (state : ProtocolState) : Prop
  | intake (atStage : state.stage = .intake)
  | workerMode (atStage : state.stage = .chooseWorkerMode) (role : SeatRole) (carrier : Carrier)
      (selected : selectCarrier (config.eligible state.stage role)
        (triedAt state state.stage role) = carrier) (workerCarrier : carrier ≠ .abstain)
  | thinking (atStage : state.stage = .thinkingPanelWorkers)
      (completedSeats : Fin 6 -> CompletedSeatResult)
  | metaJudge (atStage : state.stage = .metaJudge) (situation : DesignSituation)
      (routed : designRouter situation = .implement)
  | implementation (atStage : state.stage = .implementationWorker)
      (result : CompletedSeatResult) (roleMatches : result.view.role = .implementation)
  | review (atStage : state.stage = .reviewTripletWorkers)
      (completedSeats : Fin 3 -> CompletedSeatResult)
      (observation : ReviewObservation) (exit : ReviewExit) (routed : reviewRouter observation = exit)
inductive StageAbstainEvidence : Stage -> Prop
  | designStall (situation : DesignSituation) (routed : designRouter situation = .abstainEscalate) :
      StageAbstainEvidence .metaJudge
  | terminationEvidenceGap (observation : TerminationObservation)
      (routed : terminationRouter observation = .escalateEvidenceGap) :
      StageAbstainEvidence .fixOrDone
inductive AbstainCondition (config : ProtocolConfig) (state : ProtocolState) : Prop
  | carrierExhausted (role : SeatRole)
      (exhausted : selectCarrier (config.eligible state.stage role)
        (triedAt state state.stage role) = .abstain)
  | isolationUnavailable (unavailable : state.isolation = .unavailable)
  | stageOutcome (evidence : StageAbstainEvidence state.stage)
inductive Event
  | flightFailure (stage : Stage) (role : SeatRole) (carrier : Carrier) (attempts : Nat)
  | advance (source target : Stage)
  | boundedPass (stage : Stage) (kind : BoundedPassKind)
  | finish
  | abstain (stage : Stage)
  deriving DecidableEq, Repr
inductive ProtocolStep (config : ProtocolConfig) : ProtocolState -> Event -> ProtocolState -> Prop
  | flightFailure (state : ProtocolState) (role : SeatRole) (carrier : Carrier) (attempts : Nat)
      (live : state.phase = .live)
      (selected : selectCarrier (config.eligible state.stage role)
        (triedAt state state.stage role) = carrier)
      (workerCarrier : carrier ≠ .abstain)
      (available : flightKey state.stage role carrier ∈
        state.remainingFlights)
      (positive : 0 < attempts)
      (withinBudget : attempts <= config.retryBudget state.stage role carrier) :
      ProtocolStep config state (.flightFailure state.stage role carrier attempts)
        { state with remainingFlights :=
            Finset.erase state.remainingFlights (flightKey state.stage role carrier) }
  | advance (state : ProtocolState) (target : Stage) (live : state.phase = .live)
      (isolated : state.isolation = .available) (authorized : AdvanceCondition config state)
      (successor : state.stage.Successor target) :
      ProtocolStep config state (.advance state.stage target) { state with stage := target }
  | boundedPass (state : ProtocolState) (kind : BoundedPassKind)
      (live : state.phase = .live) (legal : kind.LegalAt state.stage)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage kind)
        { state with passesUsed := state.passesUsed + 1 }
  | finish (state : ProtocolState)
      (live : state.phase = .live) (atEnd : state.stage = .fixOrDone)
      (observation : TerminationObservation) (permitted : terminationRouter observation = .permitClaim) :
      ProtocolStep config state .finish { state with phase := .terminal }
  | abstain (state : ProtocolState) (live : state.phase = .live)
      (reason : AbstainCondition config state) :
      ProtocolStep config state (.abstain state.stage) { state with phase := .abstained }
structure InlineConsensusModel where
  stageRelation : Stage -> Stage -> Prop
  carrierSelector : Eligibility -> Finset Carrier -> Carrier
  completionPredicate : CompletionObservation -> Prop
  seatView : Type
  priorDisclosure : Carrier -> PriorExposure
  designRoute : DesignSituation -> DesignExit
  reviewRoute : ReviewObservation -> ReviewExit
  terminationRoute : TerminationObservation -> TerminationExit
  rosterContract : TerminationRoster -> Prop
  passLegalAt : BoundedPassKind -> Stage -> Prop
  transition : ProtocolConfig -> ProtocolState -> Event -> ProtocolState -> Prop
  sharedPassBudget : Nat
def inlineConsensusModel : InlineConsensusModel :=
  { stageRelation := Stage.Successor, carrierSelector := selectCarrier
    completionPredicate := Complete, seatView := SeatView, priorDisclosure := priorExposure
    designRoute := designRouter, reviewRoute := reviewRouter, terminationRoute := terminationRouter
    rosterContract := ExactRoster, passLegalAt := BoundedPassKind.LegalAt
    transition := ProtocolStep, sharedPassBudget := 5 }
theorem inline_consensus_model_covers_load_bearing_clauses :
    inlineConsensusModel.stageRelation = Stage.Successor /\
      inlineConsensusModel.carrierSelector = selectCarrier /\
      inlineConsensusModel.completionPredicate = Complete /\ inlineConsensusModel.seatView = SeatView /\
      inlineConsensusModel.priorDisclosure = priorExposure /\ inlineConsensusModel.designRoute = designRouter /\
      inlineConsensusModel.reviewRoute = reviewRouter /\
      inlineConsensusModel.terminationRoute = terminationRouter /\
      inlineConsensusModel.rosterContract = ExactRoster /\
      inlineConsensusModel.passLegalAt = BoundedPassKind.LegalAt /\
      inlineConsensusModel.transition = ProtocolStep /\ inlineConsensusModel.sharedPassBudget = 5 := by
  simp [inlineConsensusModel]
def optimalTerminationRule : Rule := fun observation =>
  decide (inlineConsensusModel.terminationRoute observation = .permitClaim)
inductive Execution (model : InlineConsensusModel) (config : ProtocolConfig) :
    ProtocolState -> List Event -> ProtocolState -> Prop
  | nil (state : ProtocolState) : Execution model config state [] state
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
private theorem exact_roster_bool_iff (roster : TerminationRoster) :
    exactRosterBool roster = true <-> ExactRoster roster := by
  simp only [exactRosterBool, ExactRoster, Bool.and_eq_true, bne_iff_ne]
  tauto
private theorem seat_result_satisfied_bool_iff {seat : TerminationSeat}
    (result : TerminationSeatResult seat) :
    result.isSatisfiedBool = true <-> result.IsSatisfied := by
  cases result with
  | completed evidence roleMatches verdict => cases verdict <;> simp [TerminationSeatResult.isSatisfiedBool,
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
private theorem termination_admits_iff (observation : TerminationObservation) :
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
  | flightFailure role carrier attempts live selected worker available positive within =>
      have smaller := Finset.card_erase_lt_of_mem available
      simp only [potential] at smaller ⊢
      omega
  | advance target live isolated authorized successor =>
      cases source : start.stage <;>
        simp [Stage.Successor, Stage.next, source] at successor <;>
        subst target <;> simp [potential, stageRemaining, Stage.rank, source]
  | boundedPass kind live legal within =>
      simp [potential]
      omega
  | finish live atEnd observation permitted => simp [potential, liveCredit, live]
  | abstain live reason => simp [potential, liveCredit, live]
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
      | flightFailure role carrier attempts live selected worker available positive within =>
          intro key member
          simp only [flightKeys, List.mem_cons] at member
          rcases member with rfl | member
          · exact available
          · exact Finset.mem_of_mem_erase (ih key member)
      | advance target live isolated authorized successor => simpa [flightKeys] using ih
      | boundedPass kind live legal within => simpa [flightKeys] using ih
      | finish live atEnd observation permitted => simpa [flightKeys] using ih
      | abstain live reason => simpa [flightKeys] using ih
private theorem execution_no_carrier_reopened {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) : NoCarrierReopened events := by
  induction execution with
  | nil => simp [NoCarrierReopened, flightKeys]
  | cons step rest ih =>
      cases step with
      | flightFailure role carrier attempts live selected worker available positive within =>
          simp only [NoCarrierReopened, flightKeys, List.nodup_cons]
          constructor
          · intro reopened
            have remaining := execution_keys_mem_start rest _ reopened
            exact (Finset.mem_erase.mp remaining).1 rfl
          · exact ih
      | advance target live isolated authorized successor =>
          simpa [NoCarrierReopened, flightKeys] using ih
      | boundedPass kind live legal within =>
          simpa [NoCarrierReopened, flightKeys] using ih
      | finish live atEnd observation permitted => simpa [NoCarrierReopened, flightKeys] using ih
      | abstain live reason => simpa [NoCarrierReopened, flightKeys] using ih
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
def fixtureConfig : ProtocolConfig :=
  { eligible := fun _ _ => allEligible
    retryBudget := fun _ _ _ => 2
    sharedPassBudget := 5
    ownerAuthorizedAboveDefault := false }
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
    remainingFlights := ((Finset.univ.erase
      (flightKey .thinkingPanelWorkers .teleology .codexCli)).erase
      (flightKey .thinkingPanelWorkers .teleology .nyxidOracle)).erase
      (flightKey .thinkingPanelWorkers .teleology .isolatedTokenSubagent) }
def thinkingAbstainFinal : ProtocolState :=
  { thinkingExhaustedStart with phase := .abstained }
def thinkingAbstainExecution :
    Execution inlineConsensusModel fixtureConfig thinkingExhaustedStart
      thinkingAbstainEvents thinkingAbstainFinal := by
  refine Execution.cons ?_ (Execution.nil _)
  apply ProtocolStep.abstain thinkingExhaustedStart rfl
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
  { eligible := fun _ _ _ => false, retryBudget := fun _ _ _ => 1, sharedPassBudget := 5
    ownerAuthorizedAboveDefault := false }
def immediateAbstainFinal : ProtocolState := { initialState exhaustedConfig with phase := .abstained }
def immediateAbstainRun : MaximalRun inlineConsensusModel exhaustedConfig where
  events := [.abstain .intake]
  finalState := immediateAbstainFinal
  execution := by
    refine Execution.cons ?_ (Execution.nil _)
    apply ProtocolStep.abstain (initialState exhaustedConfig) rfl
    apply AbstainCondition.carrierExhausted .implementation
    decide
  maximal := by
    intro event state step
    cases step <;> simp [immediateAbstainFinal, initialState] at *
def maximal_run_fixture_is_nonempty : MaximalRun inlineConsensusModel exhaustedConfig :=
  immediateAbstainRun
#print axioms termination_router_sound_maximal_unique
#print axioms every_maximal_run_is_bounded
end D5.S0.History.Consensus.InlineConsensusOptimality
