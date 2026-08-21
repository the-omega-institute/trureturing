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
  deriving Fintype, Repr
def Carrier.priorityRank : Carrier -> Nat
  | .codexCli => 0
  | .nyxidOracle => 1
  | .isolatedTokenSubagent => 2
  | .abstain => 3
private theorem Carrier.priorityRank_injective : Function.Injective Carrier.priorityRank := by
  intro first second
  cases first <;> cases second <;> simp_all [Carrier.priorityRank]
instance : LinearOrder Carrier :=
  LinearOrder.lift' Carrier.priorityRank Carrier.priorityRank_injective
theorem carrier_priority_is_the_protocol_priority :
    Carrier.priorityRank .codexCli = 0 /\ Carrier.priorityRank .nyxidOracle = 1 /\
      Carrier.priorityRank .isolatedTokenSubagent = 2 /\ Carrier.priorityRank .abstain = 3 := by
  decide
abbrev Eligibility := Carrier -> Bool
def eligibleUntried (eligible : Eligibility) (tried : Finset Carrier) : Finset Carrier :=
  Finset.univ.filter fun carrier =>
    carrier ≠ .abstain /\ eligible carrier = true /\ carrier ∉ tried
def selectCarrier (eligible : Eligibility) (tried : Finset Carrier) : Carrier :=
  if available : (eligibleUntried eligible tried).Nonempty then
    (eligibleUntried eligible tried).min' available
  else .abstain
theorem selectCarrier_mem (eligible : Eligibility) (tried : Finset Carrier)
    (available : (eligibleUntried eligible tried).Nonempty) :
    selectCarrier eligible tried ∈ eligibleUntried eligible tried := by
  simp only [selectCarrier, dif_pos available]
  exact Finset.min'_mem _ _
theorem selectCarrier_minimal (eligible : Eligibility) (tried : Finset Carrier)
    (carrier : Carrier) (available : carrier ∈ eligibleUntried eligible tried) :
    Carrier.priorityRank (selectCarrier eligible tried) <= Carrier.priorityRank carrier := by
  have nonempty : (eligibleUntried eligible tried).Nonempty := ⟨carrier, available⟩
  have ordered : selectCarrier eligible tried ≤ carrier := by
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
  apply Carrier.priorityRank_injective
  apply le_antisymm
  · exact otherMinimal _ (selectCarrier_mem eligible tried available)
  · exact selectCarrier_minimal eligible tried other otherAvailable
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
def SeatRole.IsThinking (role : SeatRole) : Prop :=
  role = .teleology \/ role = .parsimony \/ role = .fidelity \/
    role = .naturalOwnership \/ role = .proportionalContainment \/ role = .worth
def SeatRole.IsReview (role : SeatRole) : Prop :=
  role = .architectureReview \/ role = .qualityReview \/ role = .testsReview
def SeatRole.IsTermination (role : SeatRole) : Prop :=
  role = .criterionEvidence \/ role = .residualGap \/ role = .claimIntegrity
def SeatRole.LegalAt (role : SeatRole) : Stage -> Prop
  | .chooseWorkerMode | .thinkingPanelWorkers => role.IsThinking
  | .implementationWorker => role = .implementation
  | .reviewTripletWorkers => role.IsReview
  | .fixOrDone => role = .implementation \/ role.IsReview \/ role.IsTermination
  | .intake | .metaJudge => False
def CarrierLegalAt (stage : Stage) (role : SeatRole) (carrier : Carrier) : Prop :=
  role.LegalAt stage /\ carrier ≠ .abstain
theorem CarrierLegalAt.workerCarrier {stage : Stage} {role : SeatRole} {carrier : Carrier}
    (legal : CarrierLegalAt stage role carrier) : carrier ≠ .abstain := legal.2
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
theorem seat_view_contains_complete_goal (view : SeatView) :
    view.goalArtifact = .complete := by
  cases view.goalArtifact
  rfl
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
def ThinkingSeatResult.evidence {seat : ThinkingSeat} :
    ThinkingSeatResult seat -> CompletedSeatResult
  | .completed evidence _ _ _ _ => evidence
inductive DesignSituation
  | unanimousActionable | compatiblePlans | boundedStall | singlePerspective
  deriving DecidableEq, Fintype, Repr
inductive DesignExit
  | implement | metaLayerConvergence | abstainEscalate | rejectFakeConsensus
  deriving DecidableEq, Fintype, Repr
inductive ConvergenceResult
  | implementable (plan : PlanIdentity) | exhausted
  deriving DecidableEq, Fintype, Repr
inductive DesignAction : DesignExit -> Type
  | advance : DesignAction .implement
  | converge (result : ConvergenceResult) : DesignAction .metaLayerConvergence
  | abstainEscalate : DesignAction .abstainEscalate
  | rejectFakeConsensus : DesignAction .rejectFakeConsensus
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
def ReviewSeatResult.evidence {seat : ReviewSeat} : ReviewSeatResult seat -> CompletedSeatResult
  | .completed evidence _ _ => evidence
abbrev ReviewObservation := Fin 3 -> ReviewVerdict
def reviewObservation (results : ReviewResults) : ReviewObservation
  | 0 => (results .architecture).verdict
  | 1 => (results .quality).verdict
  | _ => (results .tests).verdict
inductive ReviewExit
  | fix | done | userDecisionOrBoundedPass
  deriving DecidableEq, Fintype, Repr
inductive ReviewAction : ReviewExit -> Type
  | repair : ReviewAction .fix
  | terminationCandidate : ReviewAction .done
  | requestUserDecision : ReviewAction .userDecisionOrBoundedPass
  | anotherBoundedPass : ReviewAction .userDecisionOrBoundedPass
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
inductive TerminationGapOwner
  | engineering | caller | maintainer | unresolved
  deriving DecidableEq, Fintype, Repr
inductive TerminationAction : TerminationExit -> Type
  | rejectFakeConsensus : TerminationAction .rejectFakeConsensus
  | permitClaim : TerminationAction .permitClaim
  | continueAgainstGap (owner : TerminationGapOwner) : TerminationAction .continueAgainstGap
  | escalateEvidenceGap : TerminationAction .escalateEvidenceGap
def terminationRouter (observation : TerminationObservation) : TerminationExit :=
  if exactRosterBool observation.roster then
    if allSatisfiedBool observation then .permitClaim
    else if anyUnsatisfiedBool observation then .continueAgainstGap
    else .escalateEvidenceGap
  else .rejectFakeConsensus
inductive BoundedPassKind
  | metaLayerConvergence | repeatedReview | fixPass | terminationGate
  deriving DecidableEq, Fintype, Repr
def BoundedPassKind.LegalAt : BoundedPassKind -> Stage -> Prop
  | .metaLayerConvergence, .metaJudge | .repeatedReview, .fixOrDone
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
  attemptedFlights : Finset FlightKey := {}
  artifactEpoch : Nat := 0
  reviewEpoch : Option Nat := none
  terminationEpoch : Option Nat := none
def initialState (config : ProtocolConfig) : ProtocolState :=
  { stage := .intake
    phase := .live
    remainingFlights := Finset.univ
    passesUsed := 0
    isolation := config.initialIsolation
    designSituation := none
    reviewExit := none
    terminationExit := none
    attemptedFlights := {}
    artifactEpoch := 0
    reviewEpoch := none
    terminationEpoch := none }
def triedAt (state : ProtocolState) (stage : Stage) (role : SeatRole) : Finset Carrier :=
  Finset.univ.filter fun carrier =>
    flightKey stage role carrier ∈ state.attemptedFlights
structure SelectedWorkerEvidence (config : ProtocolConfig) (state : ProtocolState)
    (role : SeatRole) (result : CompletedSeatResult) : Prop where
  legal : CarrierLegalAt state.stage role result.carrier
  roleMatches : result.view.role = role
  eligible : config.eligible state.stage role result.carrier = true
  untried : result.carrier ∉ triedAt state state.stage role
  selected : selectCarrier (config.eligible state.stage role)
    (triedAt state state.stage role) = result.carrier
  complete : Complete result.carrier result.completionObservation
def ThinkingResults.DispatchAuthorized (config : ProtocolConfig) (state : ProtocolState)
    (results : ThinkingResults) : Prop :=
  forall seat, SelectedWorkerEvidence config state seat.role (results seat).evidence
def ReviewResults.DispatchAuthorized (config : ProtocolConfig) (state : ProtocolState)
    (results : ReviewResults) : Prop :=
  forall seat, SelectedWorkerEvidence config state seat.role (results seat).evidence
def TerminationSeatResult.DispatchAuthorized (config : ProtocolConfig) (state : ProtocolState)
    {seat : TerminationSeat} : TerminationSeatResult seat -> Prop
  | .completed evidence _ _ => SelectedWorkerEvidence config state seat.role evidence
  | .invalid | .missing => True
def TerminationObservation.DispatchAuthorized (config : ProtocolConfig) (state : ProtocolState)
    (observation : TerminationObservation) : Prop :=
  forall seat, (observation.result seat).DispatchAuthorized config state
def ThinkingResults.attemptKeys (state : ProtocolState)
    (results : ThinkingResults) : Finset FlightKey :=
  Finset.univ.biUnion fun seat => {flightKey state.stage seat.role (results seat).evidence.carrier}
def ReviewResults.attemptKeys (state : ProtocolState)
    (results : ReviewResults) : Finset FlightKey :=
  Finset.univ.biUnion fun seat => {flightKey state.stage seat.role (results seat).evidence.carrier}
def TerminationSeatResult.attemptKeys (state : ProtocolState) {seat : TerminationSeat} :
    TerminationSeatResult seat -> Finset FlightKey
  | .completed evidence _ _ => {flightKey state.stage seat.role evidence.carrier}
  | .invalid | .missing => {}
def TerminationObservation.attemptKeys (state : ProtocolState)
    (observation : TerminationObservation) : Finset FlightKey :=
  Finset.univ.biUnion fun seat => (observation.result seat).attemptKeys state
inductive AdvanceCondition (config : ProtocolConfig) (state : ProtocolState) : Type
  | intake (atStage : state.stage = .intake)
  | workerMode (atStage : state.stage = .chooseWorkerMode) (role : SeatRole) (carrier : Carrier)
      (legal : CarrierLegalAt state.stage role carrier)
      (eligible : config.eligible state.stage role carrier = true)
      (untried : carrier ∉ triedAt state state.stage role)
      (selected : selectCarrier (config.eligible state.stage role)
        (triedAt state state.stage role) = carrier)
  | thinking (atStage : state.stage = .thinkingPanelWorkers)
      (compatible : PlanCompatibility) (completedSeats : ThinkingResults)
      (authorized : completedSeats.DispatchAuthorized config state)
  | metaJudge (atStage : state.stage = .metaJudge) (situation : DesignSituation)
      (recorded : state.designSituation = some situation)
      (routed : designRouter situation = .implement)
      (action : DesignAction .implement)
  | implementation (atStage : state.stage = .implementationWorker)
      (result : CompletedSeatResult)
      (authorized : SelectedWorkerEvidence config state .implementation result)
  | review (atStage : state.stage = .reviewTripletWorkers)
      (completedSeats : ReviewResults) (authorized : completedSeats.DispatchAuthorized config state)
def AdvanceCondition.nextState {config : ProtocolConfig} {state : ProtocolState}
    (condition : AdvanceCondition config state) (target : Stage) : ProtocolState :=
  match condition with
  | .thinking _ compatible completedSeats _ =>
      { state with
        stage := target
        attemptedFlights := state.attemptedFlights ∪ completedSeats.attemptKeys state
        designSituation := some (thinkingSituation compatible completedSeats) }
  | .implementation _ result _ =>
      { state with
        stage := target
        attemptedFlights := insert (flightKey state.stage .implementation result.carrier)
          state.attemptedFlights
        artifactEpoch := state.artifactEpoch + 1
        reviewExit := none
        reviewEpoch := none
        terminationExit := none
        terminationEpoch := none }
  | .review _ completedSeats _ =>
      { state with
        stage := target
        attemptedFlights := state.attemptedFlights ∪ completedSeats.attemptKeys state
        reviewExit := some (reviewRouter (reviewObservation completedSeats))
        reviewEpoch := some state.artifactEpoch
        terminationExit := none
        terminationEpoch := none }
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
      (routed : designRouter situation = .abstainEscalate)
      (action : DesignAction .abstainEscalate) :
      StageAbstainEvidence state
  | designFakeConsensus (state : ProtocolState) (atStage : state.stage = .metaJudge)
      (situation : DesignSituation) (recorded : state.designSituation = some situation)
      (routed : designRouter situation = .rejectFakeConsensus)
      (action : DesignAction .rejectFakeConsensus) :
      StageAbstainEvidence state
  | reviewUserDecision (state : ProtocolState) (atStage : state.stage = .fixOrDone)
      (recorded : state.reviewExit = some .userDecisionOrBoundedPass)
      (action : ReviewAction .userDecisionOrBoundedPass) :
      StageAbstainEvidence state
inductive AbstainCondition (config : ProtocolConfig) (state : ProtocolState) : Prop
  | carrierExhausted (role : SeatRole)
      (legalRole : exists carrier, CarrierLegalAt state.stage role carrier)
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
      (legal : CarrierLegalAt state.stage role carrier)
      (eligible : config.eligible state.stage role carrier = true)
      (untried : carrier ∉ triedAt state state.stage role)
      (selected : selectCarrier (config.eligible state.stage role)
        (triedAt state state.stage role) = carrier)
      (available : flightKey state.stage role carrier ∈
        state.remainingFlights)
      (positive : 0 < attempts)
      (withinBudget : attempts <= config.retryBudget state.stage role carrier) :
      ProtocolStep config state (.flightFailure state.stage role carrier attempts)
        { state with
          remainingFlights := Finset.erase state.remainingFlights
            (flightKey state.stage role carrier)
          attemptedFlights := insert (flightKey state.stage role carrier) state.attemptedFlights }
  | advance (state : ProtocolState) (target : Stage)
      (budgetAuthorized : PassBudgetAuthorized config) (live : state.phase = .live)
      (isolated : state.isolation = .available) (authorized : AdvanceCondition config state)
      (successor : state.stage.Successor target) :
      ProtocolStep config state (.advance state.stage target) (authorized.nextState target)
  | designConvergence (state : ProtocolState) (plan : PlanIdentity)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atMeta : state.stage = .metaJudge)
      (recorded : state.designSituation = some .compatiblePlans)
      (routed : designRouter .compatiblePlans = .metaLayerConvergence)
      (action : DesignAction .metaLayerConvergence)
      (actionShape : action = DesignAction.converge (.implementable plan))
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .metaLayerConvergence) { state with
        passesUsed := state.passesUsed + 1
        designSituation := some .unanimousActionable }
  | designConvergenceExhausted (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atMeta : state.stage = .metaJudge)
      (recorded : state.designSituation = some .compatiblePlans)
      (routed : designRouter .compatiblePlans = .metaLayerConvergence)
      (action : DesignAction .metaLayerConvergence)
      (actionShape : action = DesignAction.converge .exhausted)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .metaLayerConvergence) { state with
        passesUsed := state.passesUsed + 1
        phase := .abstained }
  | repeatedReview (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (needsPass : state.reviewExit = some .userDecisionOrBoundedPass)
      (action : ReviewAction .userDecisionOrBoundedPass)
      (actionShape : action = ReviewAction.anotherBoundedPass)
      (completedSeats : ReviewResults)
      (authorized : completedSeats.DispatchAuthorized config state)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .repeatedReview) { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := state.attemptedFlights ∪ completedSeats.attemptKeys state
        reviewExit := some (reviewRouter (reviewObservation completedSeats))
        reviewEpoch := some state.artifactEpoch
        terminationExit := none
        terminationEpoch := none }
  | fixAndReview (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (needsFix : state.reviewExit = some .fix)
      (action : ReviewAction .fix) (actionShape : action = ReviewAction.repair)
      (implementation : CompletedSeatResult)
      (implementationAuthorized :
        SelectedWorkerEvidence config state .implementation implementation)
      (completedSeats : ReviewResults)
      (reviewAuthorized : completedSeats.DispatchAuthorized config state)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .fixPass) { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := insert (flightKey state.stage .implementation implementation.carrier)
          (state.attemptedFlights ∪ completedSeats.attemptKeys state)
        artifactEpoch := state.artifactEpoch + 1
        reviewExit := some (reviewRouter (reviewObservation completedSeats))
        reviewEpoch := some (state.artifactEpoch + 1)
        terminationExit := none
        terminationEpoch := none }
  | terminationGate (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (reviewDone : state.reviewExit = some .done)
      (reviewCurrent : state.reviewEpoch = some state.artifactEpoch)
      (reviewAction : ReviewAction .done)
      (reviewActionShape : reviewAction = ReviewAction.terminationCandidate)
      (observation : TerminationObservation)
      (authorized : observation.DispatchAuthorized config state)
      (routed : terminationRouter observation = .permitClaim)
      (action : TerminationAction .permitClaim)
      (actionShape : action = TerminationAction.permitClaim)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .terminationGate) { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
        terminationExit := some .permitClaim
        terminationEpoch := some state.artifactEpoch }
  | terminationGapEngineering (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (reviewDone : state.reviewExit = some .done)
      (reviewCurrent : state.reviewEpoch = some state.artifactEpoch)
      (observation : TerminationObservation)
      (authorized : observation.DispatchAuthorized config state)
      (routed : terminationRouter observation = .continueAgainstGap)
      (action : TerminationAction .continueAgainstGap)
      (actionShape : action = TerminationAction.continueAgainstGap .engineering)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .terminationGate) { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
        reviewExit := some .fix
        reviewEpoch := none
        terminationExit := some .continueAgainstGap
        terminationEpoch := none }
  | terminationGapCaller (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (reviewDone : state.reviewExit = some .done)
      (reviewCurrent : state.reviewEpoch = some state.artifactEpoch)
      (observation : TerminationObservation)
      (authorized : observation.DispatchAuthorized config state)
      (routed : terminationRouter observation = .continueAgainstGap)
      (action : TerminationAction .continueAgainstGap)
      (actionShape : action = TerminationAction.continueAgainstGap .caller)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .terminationGate) { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
        terminationExit := some .continueAgainstGap
        terminationEpoch := none }
  | terminationGapEscalate (state : ProtocolState) (owner : TerminationGapOwner)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (reviewDone : state.reviewExit = some .done)
      (reviewCurrent : state.reviewEpoch = some state.artifactEpoch)
      (observation : TerminationObservation)
      (authorized : observation.DispatchAuthorized config state)
      (routed : terminationRouter observation = .continueAgainstGap)
      (action : TerminationAction .continueAgainstGap)
      (actionShape : action = TerminationAction.continueAgainstGap owner)
      (escalating : owner = .maintainer \/ owner = .unresolved)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .terminationGate) { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
        phase := .abstained
        terminationExit := some .continueAgainstGap
        terminationEpoch := none }
  | terminationFakeConsensus (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (reviewDone : state.reviewExit = some .done)
      (reviewCurrent : state.reviewEpoch = some state.artifactEpoch)
      (observation : TerminationObservation)
      (authorized : observation.DispatchAuthorized config state)
      (routed : terminationRouter observation = .rejectFakeConsensus)
      (action : TerminationAction .rejectFakeConsensus)
      (actionShape : action = TerminationAction.rejectFakeConsensus)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .terminationGate) { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
        phase := .abstained
        terminationExit := some .rejectFakeConsensus
        terminationEpoch := none }
  | terminationEvidenceGap (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (isolated : state.isolation = .available)
      (atEnd : state.stage = .fixOrDone)
      (reviewDone : state.reviewExit = some .done)
      (reviewCurrent : state.reviewEpoch = some state.artifactEpoch)
      (observation : TerminationObservation)
      (authorized : observation.DispatchAuthorized config state)
      (routed : terminationRouter observation = .escalateEvidenceGap)
      (action : TerminationAction .escalateEvidenceGap)
      (actionShape : action = TerminationAction.escalateEvidenceGap)
      (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage .terminationGate) { state with
        passesUsed := state.passesUsed + 1
        attemptedFlights := state.attemptedFlights ∪ observation.attemptKeys state
        phase := .abstained
        terminationExit := some .escalateEvidenceGap
        terminationEpoch := none }
  | finish (state : ProtocolState)
      (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live) (atEnd : state.stage = .fixOrDone)
      (isolated : state.isolation = .available) (reviewDone : state.reviewExit = some .done)
      (reviewCurrent : state.reviewEpoch = some state.artifactEpoch)
      (permitted : state.terminationExit = some .permitClaim)
      (permitCurrent : state.terminationEpoch = some state.artifactEpoch) :
      ProtocolStep config state .finish { state with phase := .terminal }
  | abstain (state : ProtocolState) (budgetAuthorized : PassBudgetAuthorized config)
      (live : state.phase = .live)
      (reason : AbstainCondition config state) :
      ProtocolStep config state (.abstain state.stage) { state with phase := .abstained }
structure InlineConsensusModel where
  stageRelation : Stage -> Stage -> Prop
  carrierSelector : Eligibility -> Finset Carrier -> Carrier
  carrierLegalAt : Stage -> SeatRole -> Carrier -> Prop
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
    carrierLegalAt := CarrierLegalAt
    completionPredicate := Complete, seatView := SeatView
    thinkingResults := ThinkingResults, thinkingSituationFrom := thinkingSituation
    reviewResults := ReviewResults
    priorDisclosure := priorExposure
    designRoute := designRouter, reviewRoute := reviewRouter, terminationRoute := terminationRouter
    rosterContract := ExactRoster, passLegalAt := BoundedPassKind.LegalAt
    transition := ProtocolStep }
end D5.S0.History.Consensus.InlineConsensusOptimality
