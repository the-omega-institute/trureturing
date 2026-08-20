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
inductive ClauseId | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9 | S10
  deriving DecidableEq, Fintype, Repr
inductive ModelObject
  | sevenStages | uniqueSuccessor
  | carrierAlphabet | carrierPriority | fallbackSelection
  | immutableRetryBudget
  | completionConjunction | forbiddenCompletionProxies
  | abstainTerminal
  | isolatedSeatView
  | priorExposure | correlatedHeterogeneity
  | designTable | reviewTable | terminationTable
  | terminationRoster
  | sharedPassCounter
  deriving DecidableEq, Fintype, Repr
def clauseTrace : ModelObject -> ClauseId
  | .sevenStages | .uniqueSuccessor => .S1
  | .carrierAlphabet | .carrierPriority | .fallbackSelection => .S2
  | .immutableRetryBudget => .S3
  | .completionConjunction | .forbiddenCompletionProxies => .S4
  | .abstainTerminal => .S5
  | .isolatedSeatView => .S6
  | .priorExposure | .correlatedHeterogeneity => .S7
  | .designTable | .reviewTable | .terminationTable => .S8
  | .terminationRoster => .S9
  | .sharedPassCounter => .S10
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
def Stage.Successor (source target : Stage) : Prop := source.next = some target
example (source first second : Stage) (hFirst : source.Successor first)
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
abbrev Eligibility := Carrier -> Bool
def EligibleUntried (eligible : Eligibility) (tried : Finset Carrier) (carrier : Carrier) : Prop :=
  eligible carrier = true /\ carrier ≠ .abstain /\ carrier ∉ tried
def MinimumRankUntried
    (eligible : Eligibility) (tried : Finset Carrier) (carrier : Carrier) : Prop :=
  EligibleUntried eligible tried carrier /\
    forall other, EligibleUntried eligible tried other ->
      carrier.priorityRank <= other.priorityRank
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
inductive CompletionConjunct
  | carrierExit | resultArtifact | envelope | verdict | sentinel
  deriving DecidableEq, Fintype, Repr
def CompleteExcept (omitted : CompletionConjunct) (observation : CompletionObservation) : Prop :=
  match omitted with
  | .carrierExit =>
      observation.resultArtifactExists = true /\ observation.envelopeValid = true /\
        observation.verdictAllowed = true /\ observation.sentinelExists = true
  | .resultArtifact =>
      observation.carrierExitedZero = true /\ observation.envelopeValid = true /\
        observation.verdictAllowed = true /\ observation.sentinelExists = true
  | .envelope =>
      observation.carrierExitedZero = true /\ observation.resultArtifactExists = true /\
        observation.verdictAllowed = true /\ observation.sentinelExists = true
  | .verdict =>
      observation.carrierExitedZero = true /\ observation.resultArtifactExists = true /\
        observation.envelopeValid = true /\ observation.sentinelExists = true
  | .sentinel =>
      observation.carrierExitedZero = true /\ observation.resultArtifactExists = true /\
        observation.envelopeValid = true /\ observation.verdictAllowed = true
inductive ForbiddenCompletionProxy
  | processSnapshot | logText | stdoutMarker | emptyGitStatus
  deriving DecidableEq, Fintype, Repr
structure ProxyOnlyObservation where observed : ForbiddenCompletionProxy
  deriving DecidableEq, Fintype, Repr
def evidenceFromProxyOnly (_ : ProxyOnlyObservation) : CompletionObservation :=
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
structure SeatView where
  goalArtifact : GoalArtifactSnapshot
  role : SeatRole
  exposure : PriorExposure
  deriving DecidableEq, Fintype, Repr
structure SeatEvidence where
  view : SeatView
  conclusionBit : Bool
  deriving DecidableEq, Fintype, Repr
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
inductive ReviewVerdict
  | approve | comment | reject
  deriving DecidableEq, Fintype, Repr
abbrev ReviewObservation := Fin 3 -> ReviewVerdict
inductive ReviewExit
  | fix | done | userDecisionOrBoundedPass
  deriving DecidableEq, Fintype, Repr
def ReviewHas (observation : ReviewObservation) (verdict : ReviewVerdict) : Prop :=
  exists seat, observation seat = verdict
def reviewHasBool (observation : ReviewObservation) (verdict : ReviewVerdict) : Bool :=
  observation 0 == verdict || observation 1 == verdict || observation 2 == verdict
def reviewRouter (observation : ReviewObservation) : ReviewExit :=
  if reviewHasBool observation .reject then .fix
  else if reviewHasBool observation .approve then .done
  else .userDecisionOrBoundedPass
def ReviewHazard (observation : ReviewObservation) : Prop :=
  ReviewHas observation .reject \/ forall seat, observation seat = .comment
abbrev ReviewRule := ReviewObservation -> Bool
def ReviewSound (rule : ReviewRule) : Prop :=
  forall observation, rule observation = true -> Not (ReviewHazard observation)
def ReviewRuleLE (left right : ReviewRule) : Prop :=
  forall observation, left observation = true -> right observation = true
def reviewAdmits : ReviewRule := fun observation => decide (reviewRouter observation = .done)
inductive TerminationSeat
  | criterionEvidence | residualGap | claimIntegrity
  deriving DecidableEq, Fintype, Repr
inductive TerminationResult
  | satisfied | unsatisfied | abstain | invalid | missing
  deriving DecidableEq, Fintype, Repr
abbrev TerminationRoster := Fin 3 -> Option TerminationSeat
structure TerminationObservation where
  roster : TerminationRoster
  result : TerminationSeat -> TerminationResult
  deriving DecidableEq, Fintype
def ExactRoster (roster : TerminationRoster) : Prop :=
  (roster 0).isSome = true /\ (roster 1).isSome = true /\ (roster 2).isSome = true /\
    roster 0 ≠ roster 1 /\ roster 0 ≠ roster 2 /\ roster 1 ≠ roster 2
def exactRosterBool (roster : TerminationRoster) : Bool :=
  (roster 0).isSome && (roster 1).isSome && (roster 2).isSome &&
    roster 0 != roster 1 && roster 0 != roster 2 && roster 1 != roster 2
def allSatisfied (observation : TerminationObservation) : Prop :=
  forall seat, observation.result seat = .satisfied
def allSatisfiedBool (observation : TerminationObservation) : Bool :=
  observation.result .criterionEvidence == .satisfied &&
    observation.result .residualGap == .satisfied &&
    observation.result .claimIntegrity == .satisfied
def anyUnsatisfiedBool (observation : TerminationObservation) : Bool :=
  observation.result .criterionEvidence == .unsatisfied ||
    observation.result .residualGap == .unsatisfied ||
    observation.result .claimIntegrity == .unsatisfied
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
    exists seat, observation.result seat ≠ .satisfied
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
    ((observation.result .criterionEvidence == .satisfied &&
        observation.result .residualGap == .satisfied) ||
      (observation.result .criterionEvidence == .satisfied &&
        observation.result .claimIntegrity == .satisfied) ||
      (observation.result .residualGap == .satisfied &&
        observation.result .claimIntegrity == .satisfied))
inductive BoundedPassKind
  | metaLayerConvergence | repeatedReview | fixPass | terminationGate
  deriving DecidableEq, Fintype, Repr
structure ProtocolConfig where
  eligible : Stage -> SeatRole -> Eligibility
  retryBudget : Stage -> SeatRole -> Carrier -> Nat
  sharedPassBudget : Nat
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
def initialState (_ : ProtocolConfig) : ProtocolState :=
  { stage := .intake
    phase := .live
    remainingFlights := Finset.univ
    passesUsed := 0 }
def triedAt (state : ProtocolState) (stage : Stage) (role : SeatRole) : Finset Carrier :=
  Finset.univ.filter fun carrier =>
    flightKey stage role carrier ∉ state.remainingFlights
inductive Event
  | flightFailure (stage : Stage) (role : SeatRole) (carrier : Carrier) (attempts : Nat)
  | advance (source target : Stage)
  | boundedPass (stage : Stage) (kind : BoundedPassKind)
  | finish
  | abstain (stage : Stage)
  deriving DecidableEq, Repr
def Event.stage? : Event -> Option Stage
  | .flightFailure stage _ _ _ => some stage
  | .advance _ target => some target
  | .boundedPass stage _ => some stage
  | .finish => some .fixOrDone
  | .abstain stage => some stage
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
  | advance (state : ProtocolState) (target : Stage)
      (live : state.phase = .live) (successor : state.stage.Successor target) :
      ProtocolStep config state (.advance state.stage target) { state with stage := target }
  | boundedPass (state : ProtocolState) (kind : BoundedPassKind)
      (live : state.phase = .live) (withinBudget : state.passesUsed < config.sharedPassBudget) :
      ProtocolStep config state (.boundedPass state.stage kind)
        { state with passesUsed := state.passesUsed + 1 }
  | finish (state : ProtocolState)
      (live : state.phase = .live) (atEnd : state.stage = .fixOrDone) :
      ProtocolStep config state .finish { state with phase := .terminal }
  | abstain (state : ProtocolState) (live : state.phase = .live) :
      ProtocolStep config state (.abstain state.stage) { state with phase := .abstained }
inductive Execution (config : ProtocolConfig) :
    ProtocolState -> List Event -> ProtocolState -> Prop
  | nil (state : ProtocolState) : Execution config state [] state
  | cons {start middle final : ProtocolState} {event : Event} {events : List Event}
      (step : ProtocolStep config start event middle)
      (rest : Execution config middle events final) :
      Execution config start (event :: events) final
def stageRemaining (stage : Stage) : Nat := 6 - stage.rank
def liveCredit : RunPhase -> Nat
  | .live => 1
  | .terminal | .abstained => 0
def potential (config : ProtocolConfig) (state : ProtocolState) : Nat :=
  state.remainingFlights.card + stageRemaining state.stage +
    (config.sharedPassBudget - state.passesUsed) + liveCredit state.phase
def explicitRunBound (config : ProtocolConfig) : Nat :=
  Fintype.card FlightKey + 7 + config.sharedPassBudget
def RespectsStageSuccessors (events : List Event) : Prop :=
  forall event, event ∈ events -> match event with
    | .advance source target => source.Successor target
    | _ => True
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
def ReachesTerminalOrAbstain (state : ProtocolState) : Prop :=
  state.phase = .terminal \/ state.phase = .abstained
structure MaximalRun (config : ProtocolConfig) where
  events : List Event
  finalState : ProtocolState
  execution : Execution config (initialState config) events finalState
  maximal : forall event state, Not (ProtocolStep config finalState event state)
private theorem exact_roster_bool_iff (roster : TerminationRoster) :
    exactRosterBool roster = true <-> ExactRoster roster := by
  simp only [exactRosterBool, ExactRoster, Bool.and_eq_true, bne_iff_ne]
  tauto
private theorem all_satisfied_bool_iff (observation : TerminationObservation) :
    allSatisfiedBool observation = true <-> allSatisfied observation := by
  constructor
  · intro satisfied seat
    simp only [allSatisfiedBool, Bool.and_eq_true, beq_iff_eq] at satisfied
    cases seat <;> simp_all
  · intro satisfied
    simp only [allSatisfiedBool, Bool.and_eq_true, beq_iff_eq]
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
theorem termination_router_sound_maximal_unique :
    Sound terminationAdmits /\
      (forall rule, Sound rule -> RuleLE rule terminationAdmits) /\
      (forall rule, Greatest rule -> rule = terminationAdmits) := by
  refine ⟨termination_admits_sound, ?_, ?_⟩
  · intro rule sound
    exact (rule_le_iff_le rule terminationAdmits).mpr (termination_admits_greatest.2 sound)
  · intro rule greatest
    exact IsGreatest.unique greatest termination_admits_greatest
private theorem step_potential_lt {config : ProtocolConfig} {start final : ProtocolState}
    {event : Event} (step : ProtocolStep config start event final) :
    potential config final < potential config start := by
  cases step with
  | flightFailure role carrier attempts live selected worker available positive within =>
      have smaller := Finset.card_erase_lt_of_mem available
      simp only [potential] at smaller ⊢
      omega
  | advance target live successor =>
      cases source : start.stage <;>
        simp [Stage.Successor, Stage.next, source] at successor <;>
        subst target <;> simp [potential, stageRemaining, Stage.rank, source]
  | boundedPass kind live within =>
      simp [potential]
      omega
  | finish live atEnd => simp [potential, liveCredit, live]
  | abstain live => simp [potential, liveCredit, live]
private theorem execution_length_add_potential_le {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution config start events final) :
    events.length + potential config final <= potential config start := by
  induction execution with
  | nil => simp
  | cons step rest ih =>
      simp only [List.length_cons]
      have decreases := step_potential_lt step
      omega
private theorem execution_respects_stage {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution config start events final) : RespectsStageSuccessors events := by
  induction execution with
  | nil => simp [RespectsStageSuccessors]
  | cons step rest ih =>
      intro queried member
      rcases List.mem_cons.mp member with head | tail
      · subst queried
        cases step <;> simp_all
      · exact ih queried tail
private theorem execution_within_retry_budgets {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution config start events final) : WithinRetryBudgets config events := by
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
    (execution : Execution config start events final) :
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
      | advance target live successor => simpa [flightKeys] using ih
      | boundedPass kind live within => simpa [flightKeys] using ih
      | finish live atEnd => simpa [flightKeys] using ih
      | abstain live => simpa [flightKeys] using ih
private theorem execution_no_carrier_reopened {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution config start events final) : NoCarrierReopened events := by
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
      | advance target live successor => simpa [NoCarrierReopened, flightKeys] using ih
      | boundedPass kind live within =>
          simpa [NoCarrierReopened, flightKeys] using ih
      | finish live atEnd => simpa [NoCarrierReopened, flightKeys] using ih
      | abstain live => simpa [NoCarrierReopened, flightKeys] using ih
private theorem execution_pass_count_eq {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution config start events final) :
    start.passesUsed + sharedPassCount events = final.passesUsed := by
  induction execution with
  | nil => simp [sharedPassCount]
  | cons step rest ih =>
      cases step <;> simp [sharedPassCount] at ih ⊢ <;> omega
private theorem execution_passes_within_budget {config : ProtocolConfig}
    {start final : ProtocolState} {events : List Event}
    (execution : Execution config start events final)
    (startWithin : start.passesUsed <= config.sharedPassBudget) :
    final.passesUsed <= config.sharedPassBudget := by
  induction execution with
  | nil => exact startWithin
  | cons step rest ih =>
      apply ih
      cases step <;> simp_all
private theorem maximal_reaches_terminal_or_abstain {config : ProtocolConfig}
    {state : ProtocolState}
    (maximal : forall event final, Not (ProtocolStep config state event final)) :
    ReachesTerminalOrAbstain state := by
  cases phase : state.phase with
  | live =>
      exfalso
      exact maximal (.abstain state.stage) { state with phase := .abstained }
        (ProtocolStep.abstain state phase)
  | terminal => exact Or.inl phase
  | abstained => exact Or.inr phase
theorem every_reachable_run_is_bounded (config : ProtocolConfig) (run : MaximalRun config) :
    RespectsStageSuccessors run.events /\
      WithinRetryBudgets config run.events /\
      NoCarrierReopened run.events /\
      sharedPassCount run.events <= config.sharedPassBudget /\
      run.events.length <= explicitRunBound config /\
      ReachesTerminalOrAbstain run.finalState := by
  refine ⟨execution_respects_stage run.execution,
    execution_within_retry_budgets run.execution,
    execution_no_carrier_reopened run.execution, ?_, ?_,
    maximal_reaches_terminal_or_abstain run.maximal⟩
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
example : selectCarrier allEligible {} = .codexCli := by decide
example : MinimumRankUntried allEligible {} .codexCli := by
  constructor
  · simp [EligibleUntried, allEligible]
  · intro other eligible
    cases other <;> simp [EligibleUntried, allEligible, Carrier.priorityRank] at eligible ⊢
example : selectCarrier allEligible {.codexCli} = .nyxidOracle := by decide
example : MinimumRankUntried allEligible {.codexCli} .nyxidOracle := by
  constructor
  · simp [EligibleUntried, allEligible]
  · intro other eligible
    cases other <;> simp [EligibleUntried, allEligible, Carrier.priorityRank] at eligible ⊢
example : selectCarrier (fun _ => false) {} = .abstain := by decide
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
    CompleteExcept field (missingCompletionConjunct field) /\
      Not (Complete (missingCompletionConjunct field)) := by
  cases field <;> simp [CompleteExcept, missingCompletionConjunct, Complete]
example : CompleteExcept .carrierExit (missingCompletionConjunct .carrierExit) /\
    Not (Complete (missingCompletionConjunct .carrierExit)) := missing_completion_is_incomplete _
example : CompleteExcept .resultArtifact (missingCompletionConjunct .resultArtifact) /\
    Not (Complete (missingCompletionConjunct .resultArtifact)) := missing_completion_is_incomplete _
example : CompleteExcept .envelope (missingCompletionConjunct .envelope) /\
    Not (Complete (missingCompletionConjunct .envelope)) := missing_completion_is_incomplete _
example : CompleteExcept .verdict (missingCompletionConjunct .verdict) /\
    Not (Complete (missingCompletionConjunct .verdict)) := missing_completion_is_incomplete _
example : CompleteExcept .sentinel (missingCompletionConjunct .sentinel) /\
    Not (Complete (missingCompletionConjunct .sentinel)) := missing_completion_is_incomplete _
example (proxy : ForbiddenCompletionProxy) :
    Not (Complete (evidenceFromProxyOnly { observed := proxy })) := by
  cases proxy <;> simp [evidenceFromProxyOnly, Complete]
example :
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
def allSatisfiedResults : TerminationSeat -> TerminationResult := fun _ => .satisfied
def oneResult (seat : TerminationSeat) (result : TerminationResult) :
    TerminationSeat -> TerminationResult :=
  fun candidate => if candidate = seat then result else .satisfied
def permittedObservation : TerminationObservation :=
  { roster := exactRoster, result := allSatisfiedResults }
def fakeRosterObservation : TerminationObservation :=
  { roster := fakeRoster, result := allSatisfiedResults }
def unsatisfiedObservation : TerminationObservation :=
  { roster := exactRoster, result := oneResult .residualGap .unsatisfied }
def abstainObservation : TerminationObservation :=
  { roster := exactRoster, result := oneResult .residualGap .abstain }
def invalidObservation : TerminationObservation :=
  { roster := exactRoster, result := oneResult .residualGap .invalid }
def missingObservation : TerminationObservation :=
  { roster := exactRoster, result := oneResult .residualGap .missing }
example : terminationRouter permittedObservation = .permitClaim := by decide
example : terminationAdmits permittedObservation = true := by decide
example : terminationAdmits fakeRosterObservation = false := by decide
example : terminationAdmits unsatisfiedObservation = false := by decide
example : terminationAdmits abstainObservation = false := by decide
example : terminationAdmits invalidObservation = false := by decide
example : terminationAdmits missingObservation = false := by decide
example : Sound alwaysAbstain := by
  intro observation admitted
  simp [alwaysAbstain] at admitted
example : StrictBelow alwaysAbstain terminationAdmits := by
  constructor
  · intro observation admitted
    simp [alwaysAbstain] at admitted
  · exact ⟨permittedObservation, by decide, rfl⟩
example : StrictBelow terminationAdmits majorityAdmit := by
  constructor
  · intro observation admitted
    simp only [terminationAdmits, decide_eq_true_eq] at admitted
    simp only [majorityAdmit, Bool.and_eq_true]
    simp only [terminationRouter] at admitted
    split at admitted <;> rename_i roster
    · split at admitted <;> rename_i satisfied
      · constructor
        · exact roster
        · simp only [allSatisfiedBool, Bool.and_eq_true] at satisfied
          have criterion := beq_iff_eq.mp satisfied.1.1
          have residual := beq_iff_eq.mp satisfied.1.2
          have claim := beq_iff_eq.mp satisfied.2
          simp [criterion, residual, claim]
      · split at admitted <;> contradiction
    · contradiction
  · exact ⟨unsatisfiedObservation, by decide, by decide⟩
example : Not (Sound majorityAdmit) := by
  intro sound
  have admitted : majorityAdmit unsatisfiedObservation = true := by decide
  have safe := sound unsatisfiedObservation admitted
  apply safe
  right
  exact ⟨.residualGap, by decide⟩
private theorem review_has_bool_iff (observation : ReviewObservation) (verdict : ReviewVerdict) :
    reviewHasBool observation verdict = true <-> ReviewHas observation verdict := by
  constructor
  · intro present
    simp only [reviewHasBool, Bool.or_eq_true, beq_iff_eq] at present
    rcases present with (present | present) | present
    · exact ⟨0, present⟩
    · exact ⟨1, present⟩
    · exact ⟨2, present⟩
  · rintro ⟨seat, present⟩
    fin_cases seat <;> subst verdict <;> simp [reviewHasBool]
private theorem review_admits_iff (observation : ReviewObservation) :
    reviewAdmits observation = true <->
      Not (ReviewHas observation .reject) /\ ReviewHas observation .approve := by
  simp only [reviewAdmits, decide_eq_true_eq]
  rw [show reviewRouter observation = .done <->
      Not (ReviewHas observation .reject) /\ ReviewHas observation .approve by
    unfold reviewRouter
    rw [← review_has_bool_iff, ← review_has_bool_iff]
    cases reject : reviewHasBool observation .reject <;>
      cases approve : reviewHasBool observation .approve <;>
      simp]
example :
    ReviewSound reviewAdmits /\
      forall rule, ReviewSound rule -> ReviewRuleLE rule reviewAdmits := by
  constructor
  · intro observation admitted hazard
    have safeShape := (review_admits_iff observation).mp admitted
    rcases hazard with rejected | allComment
    · exact safeShape.1 rejected
    · obtain ⟨seat, approved⟩ := safeShape.2
      simpa [approved] using allComment seat
  · intro rule sound observation admitted
    apply (review_admits_iff observation).mpr
    have safe := sound observation admitted
    constructor
    · intro rejected
      exact safe (Or.inl rejected)
    · by_contra noApprove
      apply safe
      right
      intro seat
      have noReject : Not (observation seat = .reject) := by
        intro rejected
        exact safe (Or.inl ⟨seat, rejected⟩)
      have noSeatApprove : Not (observation seat = .approve) := by
        intro approved
        exact noApprove ⟨seat, approved⟩
      cases verdict : observation seat <;> simp_all
def fixtureConfig : ProtocolConfig :=
  { eligible := fun _ _ => allEligible
    retryBudget := fun _ _ _ => 2
    sharedPassBudget := 5 }
def fallbackStart : ProtocolState :=
  { stage := .thinkingPanelWorkers
    phase := .live
    remainingFlights := Finset.univ
    passesUsed := 0 }
def afterCodexFailure : ProtocolState :=
  { fallbackStart with
    remainingFlights := Finset.erase fallbackStart.remainingFlights
      (flightKey .thinkingPanelWorkers .teleology .codexCli) }
def afterNyxidFailure : ProtocolState :=
  { afterCodexFailure with
    remainingFlights := Finset.erase afterCodexFailure.remainingFlights
      (flightKey .thinkingPanelWorkers .teleology .nyxidOracle) }
def codexFailureStep : ProtocolStep fixtureConfig fallbackStart
    (.flightFailure .thinkingPanelWorkers .teleology .codexCli 2) afterCodexFailure := by
  apply ProtocolStep.flightFailure
  all_goals decide
def nyxidFallbackStep : ProtocolStep fixtureConfig afterCodexFailure
    (.flightFailure .thinkingPanelWorkers .teleology .nyxidOracle 1) afterNyxidFailure := by
  apply ProtocolStep.flightFailure
  all_goals decide
def fallbackFailureEvents : List Event :=
  [.flightFailure .thinkingPanelWorkers .teleology .codexCli 2,
    .flightFailure .thinkingPanelWorkers .teleology .nyxidOracle 1]
def fallbackFailureExecution :
    Execution fixtureConfig fallbackStart fallbackFailureEvents afterNyxidFailure := by
  exact Execution.cons codexFailureStep (Execution.cons nyxidFallbackStep (Execution.nil _))
example : Execution fixtureConfig fallbackStart fallbackFailureEvents afterNyxidFailure :=
  fallbackFailureExecution
example : fallbackFailureEvents.length <= explicitRunBound fixtureConfig := by
  simp only [fallbackFailureEvents, List.length_cons, List.length_nil, explicitRunBound,
    fixtureConfig]; omega
def thinkingAbstainEvents : List Event := [.abstain .thinkingPanelWorkers]
def thinkingAbstainFinal : ProtocolState :=
  { fallbackStart with phase := .abstained }
def thinkingAbstainExecution :
    Execution fixtureConfig fallbackStart thinkingAbstainEvents thinkingAbstainFinal := by
  exact Execution.cons (ProtocolStep.abstain fallbackStart rfl) (Execution.nil _)
def IsPostThinkingDependent : Stage -> Prop
  | .metaJudge | .implementationWorker | .reviewTripletWorkers | .fixOrDone => True
  | _ => False
example : Execution fixtureConfig fallbackStart thinkingAbstainEvents thinkingAbstainFinal /\
    forall event, event ∈ thinkingAbstainEvents ->
      forall stage, Event.stage? event = some stage -> Not (IsPostThinkingDependent stage) := by
  refine ⟨thinkingAbstainExecution, ?_⟩
  intro event member stage eventStage
  simp [thinkingAbstainEvents] at member
  subst event
  simp [Event.stage?] at eventStage
  subst stage
  simp [IsPostThinkingDependent]
example (config : ProtocolConfig) (state : ProtocolState) (abstained : state.phase = .abstained) :
    forall event final, Not (ProtocolStep config state event final) := by
  intro event final step
  cases step <;> simp_all
def immediateAbstainFinal (config : ProtocolConfig) : ProtocolState :=
  { initialState config with phase := .abstained }
def immediateAbstainRun (config : ProtocolConfig) : MaximalRun config where
  events := [.abstain .intake]
  finalState := immediateAbstainFinal config
  execution := by
    apply Execution.cons (ProtocolStep.abstain (initialState config) rfl)
    exact Execution.nil _
  maximal := by
    intro event state step
    cases step <;> simp [immediateAbstainFinal, initialState] at *
example : MaximalRun fixtureConfig := immediateAbstainRun fixtureConfig
#print axioms termination_router_sound_maximal_unique
#print axioms every_reachable_run_is_bounded
end D5.S0.History.Consensus.InlineConsensusOptimality
