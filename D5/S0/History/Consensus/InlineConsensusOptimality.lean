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
inductive CompletionObservation
  | codex
      (carrierExitedZero resultArtifactExists envelopeValid verdictAllowed sentinelExists : Bool)
  | nyxid (terminalStatusCompleted envelopeValid verdictAllowed : Bool)
  | subagent (envelopeValid verdictAllowed : Bool)
  deriving DecidableEq, Fintype, Repr
def Complete : Carrier -> CompletionObservation -> Prop
  | .codexCli, .codex exited artifact envelope verdict sentinel =>
      exited = true /\ artifact = true /\ envelope = true /\ verdict = true /\ sentinel = true
  | .nyxidOracle, .nyxid terminal envelope verdict =>
      terminal = true /\ envelope = true /\ verdict = true
  | .isolatedTokenSubagent, .subagent envelope verdict => envelope = true /\ verdict = true
  | _, _ => False
inductive CompletionConjunct | carrierExit | resultArtifact | envelope | verdict | sentinel
  deriving DecidableEq, Fintype, Repr
inductive ForbiddenCompletionProxy
  | processSnapshot | logText | stdoutMarker | emptyGitStatus
  deriving DecidableEq, Fintype, Repr
def evidenceFromProxyOnly (carrier : Carrier)
    (_ : ForbiddenCompletionProxy) : CompletionObservation :=
  match carrier with
  | .codexCli | .abstain => .codex false false false false false
  | .nyxidOracle => .nyxid false false false
  | .isolatedTokenSubagent => .subagent false false
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
def seat_view_information_content :
    SeatView ≃ GoalArtifactSnapshot × SeatRole × PriorExposure where
  toFun view := (view.goalArtifact, view.role, view.exposure)
  invFun data := { goalArtifact := data.1, role := data.2.1, exposure := data.2.2 }
  left_inv view := by cases view; rfl
  right_inv data := by rcases data with ⟨goal, role, exposure⟩; rfl
structure CompletedSeatResult where
  view : SeatView
  carrier : Carrier
  workerCarrier : carrier ≠ .abstain
  completionObservation : CompletionObservation
  complete : Complete carrier completionObservation
  exposureMatches : view.exposure = priorExposure carrier
def correlatedConclusion (_ : Carrier) (latent : Bool) : Bool := latent
inductive ThinkingSeat
  | teleology | parsimony | fidelity | naturalOwnership | proportionalContainment | worth
  deriving DecidableEq, Fintype, Repr
def ThinkingSeat.role : ThinkingSeat -> SeatRole
  | .teleology => .teleology
  | .parsimony => .parsimony
  | .fidelity => .fidelity
  | .naturalOwnership => .naturalOwnership
  | .proportionalContainment => .proportionalContainment
  | .worth => .worth
inductive ThinkingVerdict
  | propose | revise | reject | abstain
  deriving DecidableEq, Fintype, Repr
inductive PlanIdentity
  | planA | planB | planC
  deriving DecidableEq, Fintype, Repr
abbrev PlanCompatibility := PlanIdentity -> PlanIdentity -> Bool
inductive ThinkingSeatResult (seat : ThinkingSeat)
  | completed (evidence : CompletedSeatResult)
      (roleMatches : evidence.view.role = seat.role) (verdict : ThinkingVerdict)
      (plan : Option PlanIdentity) (presentedAsConsensus : Bool)
abbrev ThinkingResults := (seat : ThinkingSeat) -> ThinkingSeatResult seat
def ThinkingSeatResult.verdict {seat : ThinkingSeat} : ThinkingSeatResult seat -> ThinkingVerdict
  | .completed _ _ verdict _ _ => verdict
def ThinkingSeatResult.plan {seat : ThinkingSeat} : ThinkingSeatResult seat -> Option PlanIdentity
  | .completed _ _ _ plan _ => plan
def ThinkingSeatResult.presentedAsConsensus {seat : ThinkingSeat} :
    ThinkingSeatResult seat -> Bool
  | .completed _ _ _ _ presented => presented
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
def allThinkingVerdictsAre (results : ThinkingResults) (verdict : ThinkingVerdict) : Bool :=
  (results .teleology).verdict == verdict &&
    (results .parsimony).verdict == verdict &&
    (results .fidelity).verdict == verdict &&
    (results .naturalOwnership).verdict == verdict &&
    (results .proportionalContainment).verdict == verdict &&
    (results .worth).verdict == verdict
def anyThinkingVerdictIs (results : ThinkingResults) (verdict : ThinkingVerdict) : Bool :=
  (results .teleology).verdict == verdict ||
    (results .parsimony).verdict == verdict ||
    (results .fidelity).verdict == verdict ||
    (results .naturalOwnership).verdict == verdict ||
    (results .proportionalContainment).verdict == verdict ||
    (results .worth).verdict == verdict
def allThinkingPlansAre (results : ThinkingResults) (plan : PlanIdentity) : Bool :=
  (results .teleology).plan == some plan && (results .parsimony).plan == some plan &&
    (results .fidelity).plan == some plan && (results .naturalOwnership).plan == some plan &&
    (results .proportionalContainment).plan == some plan && (results .worth).plan == some plan
def thinkingPlans (results : ThinkingResults) : List PlanIdentity :=
  [(results .teleology).plan, (results .parsimony).plan, (results .fidelity).plan,
    (results .naturalOwnership).plan, (results .proportionalContainment).plan,
    (results .worth).plan].filterMap id
def plansPairwiseCompatible (compatible : PlanCompatibility) (plans : List PlanIdentity) : Bool :=
  plans.all fun first => plans.all fun second => compatible first second
def allThinkingPlansAgree (results : ThinkingResults) : Bool :=
  match (results .teleology).plan with
  | some plan => allThinkingPlansAre results plan
  | none => false
def anyThinkingResultPresentedAsConsensus (results : ThinkingResults) : Bool :=
  (results .teleology).presentedAsConsensus || (results .parsimony).presentedAsConsensus ||
    (results .fidelity).presentedAsConsensus ||
    (results .naturalOwnership).presentedAsConsensus ||
    (results .proportionalContainment).presentedAsConsensus ||
    (results .worth).presentedAsConsensus
def thinkingSituation (compatible : PlanCompatibility)
    (results : ThinkingResults) : DesignSituation :=
  if anyThinkingResultPresentedAsConsensus results then .singlePerspective
  else if allThinkingVerdictsAre results .propose && allThinkingPlansAgree results then
    .unanimousActionable
  else if !(anyThinkingVerdictIs results .abstain || anyThinkingVerdictIs results .reject) &&
      (thinkingPlans results).length == 6 &&
      plansPairwiseCompatible compatible (thinkingPlans results) &&
      !allThinkingPlansAgree results then .compatiblePlans
  else .boundedStall
inductive ReviewVerdict
  | approve | comment | reject
  deriving DecidableEq, Fintype, Repr
inductive ReviewSeat
  | architecture | quality | tests
  deriving DecidableEq, Fintype, Repr
def ReviewSeat.role : ReviewSeat -> SeatRole
  | .architecture => .architectureReview
  | .quality => .qualityReview
  | .tests => .testsReview
inductive ReviewSeatResult (seat : ReviewSeat)
  | completed (evidence : CompletedSeatResult)
      (roleMatches : evidence.view.role = seat.role) (verdict : ReviewVerdict)
abbrev ReviewResults := (seat : ReviewSeat) -> ReviewSeatResult seat
def ReviewSeatResult.verdict {seat : ReviewSeat} : ReviewSeatResult seat -> ReviewVerdict
  | .completed _ _ verdict => verdict
abbrev ReviewObservation := Fin 3 -> ReviewVerdict
def reviewObservation (results : ReviewResults) : ReviewObservation
  | 0 => (results .architecture).verdict
  | 1 => (results .quality).verdict
  | _ => (results .tests).verdict
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
inductive IsolationStatus | available | unavailable
  deriving DecidableEq, Fintype, Repr
structure ProtocolConfig where
  eligible : Stage -> SeatRole -> Eligibility
  retryBudget : Stage -> SeatRole -> Carrier -> Nat
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
  passesUsed : Nat
  isolation : IsolationStatus
  designSituation : Option DesignSituation
  reviewExit : Option ReviewExit
  terminationExit : Option TerminationExit
def initialState (config : ProtocolConfig) : ProtocolState :=
  { stage := .intake
    phase := .live
    remainingFlights := Finset.univ
    passesUsed := 0
    isolation := config.initialIsolation
    designSituation := none
    reviewExit := none
    terminationExit := none }
def triedAt (state : ProtocolState) (stage : Stage) (role : SeatRole) : Finset Carrier :=
  Finset.univ.filter fun carrier =>
    flightKey stage role carrier ∉ state.remainingFlights
inductive AdvanceCondition (config : ProtocolConfig) (state : ProtocolState) : Type
  | intake (atStage : state.stage = .intake)
  | workerMode (atStage : state.stage = .chooseWorkerMode) (role : SeatRole) (carrier : Carrier)
      (selected : selectCarrier (config.eligible state.stage role)
        (triedAt state state.stage role) = carrier) (workerCarrier : carrier ≠ .abstain)
  | thinking (atStage : state.stage = .thinkingPanelWorkers)
      (compatible : PlanCompatibility) (completedSeats : ThinkingResults)
  | metaJudge (atStage : state.stage = .metaJudge) (situation : DesignSituation)
      (recorded : state.designSituation = some situation)
      (routed : designRouter situation = .implement)
  | implementation (atStage : state.stage = .implementationWorker)
      (result : CompletedSeatResult) (roleMatches : result.view.role = .implementation)
  | review (atStage : state.stage = .reviewTripletWorkers)
      (completedSeats : ReviewResults)
def AdvanceCondition.nextState {config : ProtocolConfig} {state : ProtocolState}
    (condition : AdvanceCondition config state) (target : Stage) : ProtocolState :=
  match condition with
  | .thinking _ compatible completedSeats =>
      { state with
        stage := target
        designSituation := some (thinkingSituation compatible completedSeats) }
  | .review _ completedSeats =>
      { state with
        stage := target
        reviewExit := some (reviewRouter (reviewObservation completedSeats)) }
  | _ => { state with stage := target }
@[simp] theorem AdvanceCondition.nextState_stage {config : ProtocolConfig} {state : ProtocolState}
    (condition : AdvanceCondition config state) (target : Stage) :
    (condition.nextState target).stage = target := by
  cases condition <;> rfl
@[simp] theorem AdvanceCondition.nextState_phase {config : ProtocolConfig} {state : ProtocolState}
    (condition : AdvanceCondition config state) (target : Stage) :
    (condition.nextState target).phase = state.phase := by
  cases condition <;> rfl
@[simp] theorem AdvanceCondition.nextState_remainingFlights
    {config : ProtocolConfig} {state : ProtocolState}
    (condition : AdvanceCondition config state) (target : Stage) :
    (condition.nextState target).remainingFlights = state.remainingFlights := by
  cases condition <;> rfl
@[simp] theorem AdvanceCondition.nextState_passesUsed
    {config : ProtocolConfig} {state : ProtocolState}
    (condition : AdvanceCondition config state) (target : Stage) :
    (condition.nextState target).passesUsed = state.passesUsed := by
  cases condition <;> rfl
inductive StageAbstainEvidence : ProtocolState -> Prop
  | designStall (state : ProtocolState) (atStage : state.stage = .metaJudge)
      (situation : DesignSituation) (recorded : state.designSituation = some situation)
      (routed : designRouter situation = .abstainEscalate) :
      StageAbstainEvidence state
  | terminationEvidenceGap (state : ProtocolState) (atStage : state.stage = .fixOrDone)
      (recorded : state.terminationExit = some .escalateEvidenceGap) :
      StageAbstainEvidence state
inductive AbstainCondition (config : ProtocolConfig) (state : ProtocolState) : Prop
  | carrierExhausted (role : SeatRole)
      (exhausted : selectCarrier (config.eligible state.stage role)
        (triedAt state state.stage role) = .abstain)
  | isolationUnavailable (unavailable : state.isolation = .unavailable)
  | stageOutcome (evidence : StageAbstainEvidence state)
inductive Event
  | flightFailure (stage : Stage) (role : SeatRole) (carrier : Carrier) (attempts : Nat)
  | advance (source target : Stage)
  | boundedPass (stage : Stage) (kind : BoundedPassKind)
  | finish
  | abstain (stage : Stage)
  deriving DecidableEq, Repr
inductive ProtocolStep (config : ProtocolConfig) : ProtocolState -> Event -> ProtocolState -> Prop
  | flightFailure (state : ProtocolState) (role : SeatRole) (carrier : Carrier) (attempts : Nat)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
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
  | advance (state : ProtocolState) (target : Stage)
      (budgetAuthorized : PassBudgetAuthorized config) (live : state.phase = .live)
      (isolated : state.isolation = .available) (authorized : AdvanceCondition config state)
      (successor : state.stage.Successor target) :
      ProtocolStep config state (.advance state.stage target) (authorized.nextState target)
  | boundedPass (state : ProtocolState) (kind : BoundedPassKind)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (legal : kind.LegalAt state.stage) (notFix : kind ≠ .fixPass)
      (notTermination : kind ≠ .terminationGate)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage kind)
        { state with passesUsed := state.passesUsed + 1 }
  | fixAndReview (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (needsFix : state.reviewExit = some .fix)
      (implementation : CompletedSeatResult)
      (roleMatches : implementation.view.role = .implementation)
      (completedSeats : ReviewResults)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .fixPass) { state with
        passesUsed := state.passesUsed + 1
        reviewExit := some (reviewRouter (reviewObservation completedSeats)) }
  | terminationGate (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone) (observation : TerminationObservation)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .terminationGate) { state with
        passesUsed := state.passesUsed + 1
        terminationExit := some (terminationRouter observation) }
  | finish (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (atEnd : state.stage = .fixOrDone)
      (isolated : state.isolation = .available) (reviewDone : state.reviewExit = some .done)
      (permitted : state.terminationExit = some .permitClaim) :
      ProtocolStep config state .finish { state with phase := .terminal }
  | abstain (state : ProtocolState) (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live)
      (reason : AbstainCondition config state) :
      ProtocolStep config state (.abstain state.stage) { state with phase := .abstained }
structure InlineConsensusModel where
  stageRelation : Stage -> Stage -> Prop
  carrierSelector : Eligibility -> Finset Carrier -> Carrier
  completionPredicate : Carrier -> CompletionObservation -> Prop
  seatView : Type
  thinkingResults : Type
  thinkingSituationFrom : PlanCompatibility -> ThinkingResults -> DesignSituation
  reviewResults : Type
  priorDisclosure : Carrier -> PriorExposure
  designRoute : DesignSituation -> DesignExit
  reviewRoute : ReviewObservation -> ReviewExit
  terminationRoute : TerminationObservation -> TerminationExit
  rosterContract : TerminationRoster -> Prop
  passLegalAt : BoundedPassKind -> Stage -> Prop
  transition : ProtocolConfig -> ProtocolState -> Event -> ProtocolState -> Prop
def inlineConsensusModel : InlineConsensusModel :=
  { stageRelation := Stage.Successor, carrierSelector := selectCarrier
    completionPredicate := Complete, seatView := SeatView
    thinkingResults := ThinkingResults, thinkingSituationFrom := thinkingSituation
    reviewResults := ReviewResults
    priorDisclosure := priorExposure
    designRoute := designRouter, reviewRoute := reviewRouter, terminationRoute := terminationRouter
    rosterContract := ExactRoster, passLegalAt := BoundedPassKind.LegalAt
    transition := ProtocolStep }
/-- This theorem checks only the model record's internal wiring. Correspondence between these
objects and the external sshx prose is a digest-pinned snapshot claim, not a Lean theorem. -/
theorem inline_consensus_model_internal_wiring :
    inlineConsensusModel.stageRelation = Stage.Successor /\
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
      inlineConsensusModel.transition = ProtocolStep := by
  simp [inlineConsensusModel]
def optimalTerminationRule : Rule := fun observation =>
  decide (inlineConsensusModel.terminationRoute observation = .permitClaim)
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
  | flightFailure role carrier attempts budget live isolated selected worker available positive
      within =>
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
  | boundedPass kind budget live isolated legal notFix notTermination within =>
      simp [potential]
      omega
  | fixAndReview budget live isolated atEnd needsFix implementation roleMatches completedSeats
      within =>
      simp [potential]
      omega
  | terminationGate budget live isolated atEnd observation within =>
      simp [potential]
      omega
  | finish budget live atEnd isolated reviewDone permitted =>
      simp [potential, liveCredit, live]
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
      | flightFailure role carrier attempts budget live isolated selected worker available positive
          within =>
          intro key member
          simp only [flightKeys, List.mem_cons] at member
          rcases member with rfl | member
          · exact available
          · exact Finset.mem_of_mem_erase (ih key member)
      | advance target budget live isolated authorized successor => simpa [flightKeys] using ih
      | boundedPass kind budget live isolated legal notFix notTermination within =>
          simpa [flightKeys] using ih
      | fixAndReview budget live isolated atEnd needsFix implementation roleMatches completedSeats
          within =>
          simpa [flightKeys] using ih
      | terminationGate budget live isolated atEnd observation within => simpa [flightKeys] using ih
      | finish budget live atEnd isolated reviewDone permitted =>
          simpa [flightKeys] using ih
      | abstain budget live reason => simpa [flightKeys] using ih
private theorem execution_no_carrier_reopened {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution inlineConsensusModel config start events final) :
    NoCarrierReopened events := by
  induction execution with
  | nil => simp [NoCarrierReopened, flightKeys]
  | cons step rest ih =>
      cases step with
      | flightFailure role carrier attempts budget live isolated selected worker available positive
          within =>
          simp only [NoCarrierReopened, flightKeys, List.nodup_cons]
          constructor
          · intro reopened
            have remaining := execution_keys_mem_start rest _ reopened
            exact (Finset.mem_erase.mp remaining).1 rfl
          · exact ih
      | advance target budget live isolated authorized successor =>
          simpa [NoCarrierReopened, flightKeys] using ih
      | boundedPass kind budget live isolated legal notFix notTermination within =>
          simpa [NoCarrierReopened, flightKeys] using ih
      | fixAndReview budget live isolated atEnd needsFix implementation roleMatches completedSeats
          within =>
          simpa [NoCarrierReopened, flightKeys] using ih
      | terminationGate budget live isolated atEnd observation within =>
          simpa [NoCarrierReopened, flightKeys] using ih
      | finish budget live atEnd isolated reviewDone permitted =>
          simpa [NoCarrierReopened, flightKeys] using ih
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
