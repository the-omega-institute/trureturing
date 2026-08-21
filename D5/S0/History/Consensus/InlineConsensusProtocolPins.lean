/- GID: D5/S0/History/Consensus/InlineConsensusProtocolPins
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusProtocolPins
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One total theorem admits every load-bearing inline-consensus clause. -/
import D5.S0.History.Consensus.InlineConsensusProtocolFixtures

namespace D5.S0.History.Consensus.InlineConsensusProtocolFixtures

open InlineConsensusOptimality

def WorkerModeAdvanceConsumesSelection (model : InlineConsensusModel) : Prop :=
  forall config state final target attempted,
    state.stage = .chooseWorkerMode -> target = .thinkingPanelWorkers ->
    model.transition config state (.advance state.stage target attempted) final ->
      exists carrier,
        model.fallbackSelector config.workerModeEligibility {} = carrier /\
          config.workerModeEligibility carrier = true /\ carrier != .abstain

/- Repair-round executable echo.  Each conjunct names one of K-1--K-5 and is
   proved again through `ModelsClause` below; keeping the conjunction here makes
   the requested mutation targets visible before the implementation. -/
def RepairAcceptanceContract (model : InlineConsensusModel) : Prop :=
  RouterTransitionsExhaustive model /\
    Not (UniformIndependent
      (correlatedConclusion .codexCli) (correlatedConclusion .nyxidOracle)) /\
    ConstantConclusionsAreIndependent /\
    RecoverablePermitInvalidation model /\
    AllWorkerAttemptsRecorded model /\
    WorkerModeAdvanceConsumesSelection model /\
    ChooseWorkerModeRouting model

def protocolThinkingDispatch : ThinkingSeat -> Carrier
  | .teleology => .isolatedTokenSubagent
  | .parsimony => .nyxidOracle
  | .fidelity | .naturalOwnership | .proportionalContainment | .worth => .codexCli

def protocolReviewDispatch : ReviewSeat -> Carrier
  | .architecture => .isolatedTokenSubagent
  | .quality => .nyxidOracle
  | .tests => .codexCli

def protocolTerminationDispatch : TerminationSeat -> Carrier
  | .criterionEvidence => .isolatedTokenSubagent
  | .residualGap => .nyxidOracle
  | .claimIntegrity => .codexCli

def protocolDispatchPlan : DispatchPlan :=
  { thinking := protocolThinkingDispatch
    implementation := .codexCli
    review := protocolReviewDispatch
    termination := protocolTerminationDispatch
    thinkingLayout := by decide
    reviewLayout := by decide
    terminationLayout := by decide }

def allCodexThinkingDispatch : ThinkingSeat -> Carrier := fun _ => .codexCli

def protocolEligibility : Stage -> SeatRole -> Eligibility :=
  fun _ _ carrier => carrier != .abstain

def mismatchedImplementationEligibility : Stage -> SeatRole -> Eligibility :=
  fun stage role carrier =>
    if stage == .implementationWorker && role == .implementation then
      carrier == .nyxidOracle
    else
      protocolEligibility stage role carrier

def protocolGoalArtifact : GoalArtifact :=
  { rawUserInput := some .digestA
    normalizedGoal := some .digestA
    constraints := some .digestA
    successCriteria := some .digestA
    iterationQuestion := some .digestA
    harness := some .digestA
    revisions := some .digestA }

def protocolAlternateGoalArtifact : GoalArtifact :=
  { protocolGoalArtifact with rawUserInput := some .digestB }

theorem protocol_initial_plan_is_compatible :
    InitialPlanCompatible protocolEligibility protocolDispatchPlan := by
  intro stage role carrier planned
  cases stage <;> cases role <;> cases carrier <;>
    simp_all [DispatchPlan.carrierAt, protocolDispatchPlan, protocolThinkingDispatch,
      protocolReviewDispatch, protocolTerminationDispatch, protocolEligibility,
      CarrierLegalAt, SeatRole.LegalAt, SeatRole.IsThinking, SeatRole.IsReview,
      SeatRole.IsTermination]

def protocolConfigWithWorkerMode (workerModeEligibility : Eligibility) : ProtocolConfig :=
  { workerModeEligibility
    eligible := protocolEligibility
    retryBudget := fun _ _ _ => 1
    dispatchPlan := protocolDispatchPlan
    initialPlanCompatible := protocol_initial_plan_is_compatible
    goalArtifact := protocolGoalArtifact
    sharedPassBudget := defaultSharedPassBudget
    ownerAuthorizedAboveDefault := false
    initialIsolation := .available }

def chooseWorkerModeState (workerModeEligibility : Eligibility) : ProtocolState :=
  { initialState (protocolConfigWithWorkerMode workerModeEligibility) with
    stage := .chooseWorkerMode }

theorem worker_mode_advance_consumes_selector_and_availability
    (model : InlineConsensusModel) :
    WorkerModeAdvanceConsumesSelection model := by
  intro config state final target attempted atChoose toThinking step
  rcases step with ⟨shape, wellFormed, raw, action, rfl⟩
  cases action with
  | advance target budgetAuthorized live isolated authorized attemptsFresh successor =>
      cases authorized <;> simp_all

theorem unavailable_primary_falls_back_before_launch :
    nyxidOnlyAvailable .codexCli = false /\
      nyxidOnlyAvailable .nyxidOracle = true /\
      inlineConsensusModel.fallbackSelector nyxidOnlyAvailable {} = .nyxidOracle := by
  decide

theorem unavailable_worker_mode_abstains_without_thinking_flight :
    exists final,
      inlineConsensusModel.transition (protocolConfigWithWorkerMode noWorkerAvailable)
          (chooseWorkerModeState noWorkerAvailable) (.abstain .chooseWorkerMode) final /\
        final.phase = .abstained /\ final.attemptedFlights = {} /\
        workerAttemptHistory [.abstain .chooseWorkerMode] = [] := by
  apply inline_choose_worker_mode_routes_before_launch.2.2
  · rfl
  · change MultiSeatLayout protocolThinkingDispatch /\
      MultiSeatLayout protocolReviewDispatch /\
      MultiSeatLayout protocolTerminationDispatch /\
      protocolDispatchPlan.implementation != .abstain
    exact ⟨by decide, by decide, by decide, by decide⟩
  · simp [StateWellFormed, chooseWorkerModeState, initialState,
      protocolConfigWithWorkerMode]
  · exact Or.inl (by simp [protocolConfigWithWorkerMode])
  · rfl
  · rfl
  · rfl

def ConcreteChooseWorkerModeRouting (model : InlineConsensusModel) : Prop :=
  nyxidOnlyAvailable .codexCli = false /\ nyxidOnlyAvailable .nyxidOracle = true /\
    model.fallbackSelector nyxidOnlyAvailable {} = .nyxidOracle /\
    exists final,
      model.transition (protocolConfigWithWorkerMode noWorkerAvailable)
          (chooseWorkerModeState noWorkerAvailable) (.abstain .chooseWorkerMode) final /\
        final.phase = .abstained /\ final.attemptedFlights = {} /\
        workerAttemptHistory [.abstain .chooseWorkerMode] = []

theorem concrete_choose_worker_mode_routing_is_pinned :
    ConcreteChooseWorkerModeRouting inlineConsensusModel :=
  ⟨unavailable_primary_falls_back_before_launch.1,
    unavailable_primary_falls_back_before_launch.2.1,
    unavailable_primary_falls_back_before_launch.2.2,
    unavailable_worker_mode_abstains_without_thinking_flight⟩

def permitBeforeInterveningFailure : ProtocolState :=
  { initialState (protocolConfigWithWorkerMode nyxidOnlyAvailable) with
    stage := .fixOrDone
    reviewExit := some .done
    terminationExit := some .permitClaim
    reviewEpoch := some 0
    terminationEpoch := some 0 }

def permitInvalidationRaw : ProtocolState :=
  { permitBeforeInterveningFailure with
    remainingFlights := permitBeforeInterveningFailure.remainingFlights.erase
      (flightKey .fixOrDone .implementation .codexCli)
    attemptedFlights := insert (flightKey .fixOrDone .implementation .codexCli)
      permitBeforeInterveningFailure.attemptedFlights
    exhaustedFlights := insert (flightKey .fixOrDone .implementation .codexCli)
      permitBeforeInterveningFailure.exhaustedFlights }

def permitInvalidatedState : ProtocolState :=
  recordEvent permitBeforeInterveningFailure permitInvalidationRaw

theorem intervening_failure_clears_current_permit :
    ProtocolStep inlineConsensusModel (protocolConfigWithWorkerMode nyxidOnlyAvailable)
      permitBeforeInterveningFailure
      (.flightFailure .fixOrDone .implementation .codexCli 1) permitInvalidatedState := by
  change ProtocolStep inlineConsensusModel _ _ _
    (recordEvent permitBeforeInterveningFailure permitInvalidationRaw)
  apply ProtocolStep.ofAction
  · change MultiSeatLayout protocolThinkingDispatch /\
      MultiSeatLayout protocolReviewDispatch /\
      MultiSeatLayout protocolTerminationDispatch /\
      protocolDispatchPlan.implementation != .abstain
    exact ⟨by decide, by decide, by decide, by decide⟩
  · simp [StateWellFormed, permitBeforeInterveningFailure, initialState,
      protocolConfigWithWorkerMode]
  · exact .flightFailure permitBeforeInterveningFailure .implementation .codexCli 1
      (Or.inl (by simp [protocolConfigWithWorkerMode])) rfl rfl
      (by simp [permitBeforeInterveningFailure, CarrierLegalAt, SeatRole.LegalAt]) rfl
      (by simp [triedAt, permitBeforeInterveningFailure, initialState])
      (Or.inl ⟨rfl, by simp [triedAt, permitBeforeInterveningFailure, initialState]⟩)
      (by simp [permitBeforeInterveningFailure, initialState]) (by omega) rfl

def successfulCompletionObservation : Carrier -> CompletionObservation
  | .codexCli => .codex true true true true true
  | .nyxidOracle => .nyxid true true true
  | .isolatedTokenSubagent => .subagent true true
  | .abstain => .subagent false false

def freshTerminationResult (seat : TerminationSeat) : TerminationSeatResult seat :=
  .completed
    { view :=
        { goalArtifact := ⟨protocolGoalArtifact, Finset.univ⟩
          role := seat.role
          exposure := priorExposure (protocolTerminationDispatch seat)
          sameRoundPeerOutputs := {} }
      carrier := protocolTerminationDispatch seat
      completionObservation := successfulCompletionObservation
        (protocolTerminationDispatch seat)
      verdict := .satisfied }
    rfl

def freshTerminationRoster : TerminationRoster
  | 0 => some .criterionEvidence
  | 1 => some .residualGap
  | _ => some .claimIntegrity

def freshTerminationObservation : TerminationObservation :=
  { roster := freshTerminationRoster
    result := freshTerminationResult }

theorem fresh_termination_reports_are_authorized :
    freshTerminationObservation.DispatchAuthorized inlineConsensusModel
      (protocolConfigWithWorkerMode nyxidOnlyAvailable) permitInvalidatedState := by
  intro seat
  cases seat <;>
    refine {
      legal := by
        simp [TerminationSeat.role, protocolTerminationDispatch, CarrierLegalAt,
          SeatRole.LegalAt, SeatRole.IsTermination, permitInvalidatedState,
          permitInvalidationRaw, permitBeforeInterveningFailure, recordEvent]
      roleMatches := rfl
      eligible := by
        simp [protocolConfigWithWorkerMode, protocolEligibility, protocolTerminationDispatch]
      untried := by
        simp [TerminationSeat.role, protocolTerminationDispatch, flightKey, triedAt,
          permitInvalidatedState, permitInvalidationRaw, permitBeforeInterveningFailure,
          initialState, recordEvent]
      assigned := by
        left
        constructor
        · rfl
        · simp [TerminationSeat.role, flightKey, triedAt,
            permitInvalidatedState, permitInvalidationRaw, permitBeforeInterveningFailure,
            initialState, recordEvent]
      complete := by
        simp [protocolTerminationDispatch, successfulCompletionObservation,
          inlineConsensusModel, Complete]
      isolatedView := by
        simp [protocolConfigWithWorkerMode, SeatView.IsolatedComplete,
          GoalArtifactSnapshot.ContainsComplete, GoalArtifact.Complete, protocolGoalArtifact]
      exposureMatches := by
        simp [protocolTerminationDispatch] }

def ConcretePermitRecovery (model : InlineConsensusModel) : Prop :=
    exists reevaluated,
      permitInvalidatedState.terminationExit = none /\
      Not (FinishPrecondition permitInvalidatedState) /\
      model.transition (protocolConfigWithWorkerMode nyxidOnlyAvailable)
        permitInvalidatedState
        (.boundedPass permitInvalidatedState.stage .terminationGate
          (freshTerminationObservation.attemptKeys permitInvalidatedState)) reevaluated

theorem stale_permit_cannot_finish_and_fresh_evaluation_is_reachable :
    ConcretePermitRecovery inlineConsensusModel := by
  have invalidating := intervening_failure_clears_current_permit
  have noFinish : Not (FinishPrecondition permitInvalidatedState) :=
    every_protocol_event_invalidates_carried_permit rfl invalidating
  have recovery := carried_permit_invalidation_is_recoverable inlineConsensusModel
    (protocolConfigWithWorkerMode nyxidOnlyAvailable) permitBeforeInterveningFailure
    permitInvalidatedState (.flightFailure .fixOrDone .implementation .codexCli 1)
    freshTerminationObservation .engineering rfl invalidating (Or.inl (by decide))
    (by simp [StateWellFormed, permitInvalidatedState, permitInvalidationRaw,
      permitBeforeInterveningFailure, recordEvent, terminationExitAfterEvent, carriedPermit,
      permitEpochAfterEvent]) rfl rfl rfl rfl rfl fresh_termination_reports_are_authorized
    (by decide) (by decide)
  obtain ⟨reevaluated, step⟩ := recovery
  exact ⟨reevaluated, by decide, noFinish, step⟩

theorem mismatched_initial_plan_is_rejected :
    mismatchedImplementationEligibility .implementationWorker .implementation .codexCli =
        false /\
      mismatchedImplementationEligibility .implementationWorker .implementation
        .nyxidOracle = true /\
      Not (InitialPlanCompatible mismatchedImplementationEligibility protocolDispatchPlan) := by
  refine ⟨by decide, by decide, ?_⟩
  exact initial_plan_ineligible_is_rejected
    (eligible := mismatchedImplementationEligibility) (plan := protocolDispatchPlan)
    (stage := .implementationWorker) (role := .implementation) (carrier := .codexCli)
    rfl rfl

theorem two_distinct_complete_goal_artifacts_exist :
    exists first second : GoalArtifact,
      first.Complete /\ second.Complete /\ first ≠ second := by
  refine ⟨protocolGoalArtifact, protocolAlternateGoalArtifact, ?_, ?_, ?_⟩
  · simp [GoalArtifact.Complete, protocolGoalArtifact]
  · simp [GoalArtifact.Complete, protocolAlternateGoalArtifact, protocolGoalArtifact]
  · intro same
    have rawInput := congrArg GoalArtifact.rawUserInput same
    simp [protocolAlternateGoalArtifact, protocolGoalArtifact] at rawInput

theorem complete_goal_snapshot_is_accepted :
    GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
      (⟨protocolGoalArtifact, Finset.univ⟩ : GoalArtifactSnapshot) := by
  exact ⟨by simp [GoalArtifact.Complete, protocolGoalArtifact], rfl, rfl⟩

theorem full_snapshot_with_wrong_artifact_is_rejected :
    Not (GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
      (⟨protocolAlternateGoalArtifact, Finset.univ⟩ : GoalArtifactSnapshot)) := by
  intro contains
  have rawInput := congrArg GoalArtifact.rawUserInput contains.2.1
  simp [protocolAlternateGoalArtifact, protocolGoalArtifact] at rawInput

theorem empty_visible_fields_are_rejected :
    Not (GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
      (⟨protocolGoalArtifact, {}⟩ : GoalArtifactSnapshot)) := by
  intro contains
  have fields : ({} : Finset GoalArtifactField) = Finset.univ := contains.2.2
  have visible : GoalArtifactField.rawUserInput ∈ ({} : Finset GoalArtifactField) := by
    rw [fields]
    simp
  simp at visible

def SuccessfulFixConsumesImplementationCarrier (model : InlineConsensusModel) : Prop :=
  forall config state attempted raw,
    ProtocolAction model config state (.boundedPass state.stage .fixPass attempted) raw ->
      exists carrier,
        flightKey state.stage .implementation carrier ∈ raw.attemptedFlights

def ImplementationAdvancePreservesPermitPayload (model : InlineConsensusModel) : Prop :=
  forall config state target (atStage : state.stage = .implementationWorker)
      (result : WorkerReport Unit)
      (authorized : AuthorizedReport model config state .implementation result),
    let condition : AdvanceCondition model config state := .implementation atStage result authorized
    (condition.nextState target).terminationExit = state.terminationExit /\
      (condition.nextState target).terminationEpoch = state.terminationEpoch

inductive ClauseId
  | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10
  deriving DecidableEq, Fintype, Repr

def ModelsClause (model : InlineConsensusModel) : ClauseId -> Prop
  | .s1 =>
      model.stageRelation .intake .chooseWorkerMode /\
      model.stageRelation .chooseWorkerMode .thinkingPanelWorkers /\
      model.stageRelation .thinkingPanelWorkers .metaJudge /\
      model.stageRelation .metaJudge .implementationWorker /\
      model.stageRelation .implementationWorker .reviewTripletWorkers /\
      model.stageRelation .reviewTripletWorkers .fixOrDone /\
      (forall target, Not (model.stageRelation .fixOrDone target)) /\
      (forall (source first second : Stage), model.stageRelation source first ->
        model.stageRelation source second -> first = second)
  | .s2 =>
      (Carrier.priorityRank .codexCli = 0 /\ Carrier.priorityRank .nyxidOracle = 1 /\
        Carrier.priorityRank .isolatedTokenSubagent = 2 /\
        Carrier.priorityRank .abstain = 3) /\
      (forall eligible tried, (eligibleUntried eligible tried).Nonempty ->
        model.fallbackSelector eligible tried ∈ eligibleUntried eligible tried) /\
      (forall eligible tried carrier, carrier ∈ eligibleUntried eligible tried ->
        Carrier.priorityRank (model.fallbackSelector eligible tried) <=
          Carrier.priorityRank carrier) /\
      (forall eligible tried, (eligibleUntried eligible tried).Nonempty ->
        model.fallbackSelector eligible tried ∈ eligibleUntried eligible tried /\
          forall other, other ∈ eligibleUntried eligible tried ->
            (forall carrier, carrier ∈ eligibleUntried eligible tried ->
              Carrier.priorityRank other <= Carrier.priorityRank carrier) ->
            other = model.fallbackSelector eligible tried) /\
      (forall eligible tried,
        model.fallbackSelector eligible tried = .abstain <->
          eligibleUntried eligible tried = {}) /\
      model.dispatchShape protocolDispatchPlan /\
      MultiSeatLayout protocolThinkingDispatch /\
      MultiSeatLayout protocolReviewDispatch /\
      MultiSeatLayout protocolTerminationDispatch /\
      Not (MultiSeatLayout allCodexThinkingDispatch) /\
      protocolDispatchPlan.implementation = .codexCli /\
      InitialPlanCompatible protocolEligibility protocolDispatchPlan /\
      (forall (eligible : Stage -> SeatRole -> Eligibility) (plan : DispatchPlan)
          (stage : Stage) (role : SeatRole) (carrier : Carrier),
        plan.carrierAt stage role = some carrier ->
        eligible stage role carrier = false ->
        Not (InitialPlanCompatible eligible plan)) /\
      (mismatchedImplementationEligibility .implementationWorker .implementation .codexCli =
          false /\
        mismatchedImplementationEligibility .implementationWorker .implementation
          .nyxidOracle = true /\
        Not (InitialPlanCompatible mismatchedImplementationEligibility protocolDispatchPlan)) /\
      (forall config state role carrier, FallbackAssigned model config state role carrier ->
        (triedAt state state.stage role).Nonempty /\
        model.fallbackSelector (config.eligible state.stage role)
          (triedAt state state.stage role) = carrier) /\
      (forall config state role carrier, FallbackAssigned model config state role carrier ->
        exists failedCarrier,
          flightKey state.stage role failedCarrier ∈ state.exhaustedFlights) /\
      SuccessfulFixConsumesImplementationCarrier model /\
      AllWorkerAttemptsRecorded model /\
      WorkerModeAdvanceConsumesSelection model /\
      ChooseWorkerModeRouting model /\
      ConcreteChooseWorkerModeRouting model /\
      (forall config state role, role.LegalAt state.stage ->
        triedAt state state.stage role = {} ->
          (exists carrier,
            InitiallyAssigned config state role carrier /\
              CarrierLegalAt state.stage role carrier /\
              config.eligible state.stage role carrier = true) \/
          model.fallbackSelector (config.eligible state.stage role)
            (triedAt state state.stage role) = .abstain)
  | .s3 =>
      (forall config state final role carrier attempts,
        ProtocolStep model config state
          (.flightFailure state.stage role carrier attempts) final ->
          0 < attempts /\ attempts = config.retryBudget state.stage role carrier) /\
      (forall config start events final,
        Execution model config start events final ->
          WithinRetryBudgets config events)
  | .s4 =>
      (forall exited artifact envelope verdict sentinel,
        model.completionPredicate .codexCli
            (.codex exited artifact envelope verdict sentinel) <->
          exited = true /\ artifact = true /\ envelope = true /\ verdict = true /\
            sentinel = true) /\
      (forall terminal envelope verdict,
        model.completionPredicate .nyxidOracle (.nyxid terminal envelope verdict) <->
          terminal = true /\ envelope = true /\ verdict = true) /\
      (forall envelope verdict,
        model.completionPredicate .isolatedTokenSubagent (.subagent envelope verdict) <->
          envelope = true /\ verdict = true) /\
      (forall proxy carrier, carrier ≠ .abstain ->
        Not (model.completionPredicate carrier (evidenceFromProxyOnly carrier proxy)))
  | .s5 =>
      (forall config state final stage,
        ProtocolStep model config state (.abstain stage) final ->
          final.phase = .abstained) /\
      (forall config state final event, state.phase = .abstained ->
        Not (ProtocolStep model config state event final))
  | .s6 =>
      (forall config state role (Verdict : Type) (report : WorkerReport Verdict),
        AuthorizedReport model config state role report ->
          report.view.IsolatedComplete config.goalArtifact) /\
      (forall config state final event, state.isolation = .unavailable ->
        ProtocolStep model config state event final -> exists stage, event = .abstain stage) /\
      (exists first second : GoalArtifact,
        first.Complete /\ second.Complete /\ first ≠ second) /\
      GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
        (⟨protocolGoalArtifact, Finset.univ⟩ : GoalArtifactSnapshot) /\
      Not (GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
        (⟨protocolAlternateGoalArtifact, Finset.univ⟩ : GoalArtifactSnapshot)) /\
      Not (GoalArtifactSnapshot.ContainsComplete protocolGoalArtifact
        (⟨protocolGoalArtifact, {}⟩ : GoalArtifactSnapshot))
  | .s7 =>
      (priorExposure .codexCli = .repoPriorExposed /\
        priorExposure .nyxidOracle = .externalPriorExposed /\
        priorExposure .isolatedTokenSubagent = .callerPriorExposed /\
        priorExposure .abstain = .noCarrier) /\
      priorExposure .codexCli ≠ priorExposure .nyxidOracle /\
      (forall latent, correlatedConclusion .codexCli latent =
        correlatedConclusion .nyxidOracle latent) /\
      Not (UniformIndependent
        (correlatedConclusion .codexCli) (correlatedConclusion .nyxidOracle)) /\
      ConstantConclusionsAreIndependent
  | .s8 =>
      RouterTransitionsExhaustive model /\
      model.designRoute .unanimousActionable = .implement /\
      model.designRoute .compatiblePlans = .metaLayerConvergence /\
      model.designRoute .boundedStall = .abstainEscalate /\
      model.designRoute .singlePerspective = .rejectFakeConsensus /\
      (forall observation, (exists index, observation index = .reject) ->
        model.reviewRoute observation = .fix) /\
      (forall observation, (forall index, observation index != .reject) ->
        (exists index, observation index = .approve) ->
          model.reviewRoute observation = .done) /\
      (forall observation, (forall index, observation index = .comment) ->
        model.reviewRoute observation = .userDecisionOrBoundedPass) /\
      (forall roster, exactRosterBool roster = true <-> model.rosterContract roster) /\
      (forall observation, model.terminationRoute observation = .permitClaim <->
        model.rosterContract observation.roster /\ allSatisfied observation) /\
      (forall observation, Not (model.rosterContract observation.roster) ->
        model.terminationRoute observation = .rejectFakeConsensus) /\
      (forall observation, model.rosterContract observation.roster ->
        (exists seat, (observation.result seat).isUnsatisfiedBool = true) ->
        model.terminationRoute observation = .continueAgainstGap) /\
      (forall observation, model.rosterContract observation.roster ->
        Not (allSatisfied observation) ->
        (forall seat, (observation.result seat).isUnsatisfiedBool = false) ->
        model.terminationRoute observation = .escalateEvidenceGap)
  | .s9 =>
      Fintype.card TerminationSeat = 3 /\
      (forall observation, terminationAdmits model observation = true <->
        model.rosterContract observation.roster /\ allSatisfied observation) /\
      Sound model (terminationAdmits model) /\
      (forall rule, Sound model rule -> RuleLE rule (terminationAdmits model)) /\
      (forall rule, Greatest model rule -> rule = terminationAdmits model) /\
      Sound model alwaysAbstain /\
      StrictBelow alwaysAbstain (terminationAdmits model) /\
      StrictBelow (terminationAdmits model) majorityAdmit /\
      Not (Sound model majorityAdmit) /\
      (forall observation, model.terminationRoute observation ≠ .permitClaim ->
        terminationAdmits model observation = false) /\
      (forall config start final event, ProtocolStep model config start event final ->
        final.eventEpoch = start.eventEpoch + 1) /\
      (forall config state attempted final,
        ProtocolStep model config state
          (.boundedPass state.stage .terminationGate attempted) final ->
          state.reviewExit = some .done /\
          state.reviewEpoch = some state.artifactEpoch) /\
      (forall config start final event,
        start.terminationExit = some .permitClaim ->
        ProtocolStep model config start event final -> Not (FinishPrecondition final)) /\
      (forall config start attempted repaired,
        ProtocolStep model config start (.boundedPass start.stage .fixPass attempted) repaired ->
          Not (FinishPrecondition repaired)) /\
      RecoverablePermitInvalidation model /\
      ConcretePermitRecovery model /\
      ImplementationAdvancePreservesPermitPayload model
  | .s10 =>
      defaultSharedPassBudget = 5 /\
      (forall config, PassBudgetAuthorized config <->
        config.sharedPassBudget <= defaultSharedPassBudget \/
          config.ownerAuthorizedAboveDefault = true) /\
      (forall config start events final,
        Execution model config start events final ->
          PassBudgetAuthorized config) /\
      BoundedPassKind.LegalAt .metaLayerConvergence .metaJudge /\
      BoundedPassKind.LegalAt .repeatedReview .fixOrDone /\
      BoundedPassKind.LegalAt .fixPass .fixOrDone /\
      BoundedPassKind.LegalAt .terminationGate .fixOrDone /\
      forall config (run : MaximalRun model config),
        sharedPassCount run.events <= config.sharedPassBudget /\
        run.events.length <= explicitRunBound config

def RequiredFixtureSuite (model : InlineConsensusModel) : Prop :=
  forall clause, ModelsClause model clause

theorem required_fixture_suite_is_pinned :
    RequiredFixtureSuite inlineConsensusModel := by
  have legal_preassigned_layout :
      MultiSeatLayout protocolThinkingDispatch /\
      MultiSeatLayout protocolReviewDispatch /\
      MultiSeatLayout protocolTerminationDispatch := by decide
  have illegal_all_codex_layout_is_rejected :
      Not (MultiSeatLayout allCodexThinkingDispatch) := by decide
  have successful_fix_consumes_implementation_carrier :
      SuccessfulFixConsumesImplementationCarrier inlineConsensusModel := by
    intro config state attempted raw action
    cases action with
    | fixAndReview budget live isolated atEnd needsFix implementation implementationAuthorized
        results reviewAuthorized attemptsFresh withinBudget =>
        exact ⟨implementation.carrier, by simp⟩
  have design_and_review_router_exits_have_executable_transitions :
      RouterTransitionsExhaustive inlineConsensusModel := router_transitions_are_exhaustive
  have implementation_branch_preserves_permit_payload :
      ImplementationAdvancePreservesPermitPayload inlineConsensusModel := by
    intro config state target atStage result authorized
    exact ⟨rfl, rfl⟩
  intro clause
  cases clause with
  | s1 =>
      change Stage.Successor .intake .chooseWorkerMode /\
        Stage.Successor .chooseWorkerMode .thinkingPanelWorkers /\
        Stage.Successor .thinkingPanelWorkers .metaJudge /\
        Stage.Successor .metaJudge .implementationWorker /\
        Stage.Successor .implementationWorker .reviewTripletWorkers /\
        Stage.Successor .reviewTripletWorkers .fixOrDone /\
        (forall target, Not (Stage.Successor .fixOrDone target)) /\
        (forall source first second, Stage.Successor source first ->
          Stage.Successor source second -> first = second)
      rcases stage_order_is_the_protocol_order with ⟨h1, h2, h3, h4, h5, h6, h7⟩
      refine ⟨h1, h2, h3, h4, h5, h6, ?_, stage_successor_is_unique⟩
      intro target successor
      rw [Stage.Successor, h7] at successor
      simp at successor
  | s2 =>
      exact ⟨carrier_priority_is_the_protocol_priority,
        selectCarrier_mem, selectCarrier_minimal, selectCarrier_is_unique_minimum,
        selectCarrier_eq_abstain_iff,
        ⟨legal_preassigned_layout.1, legal_preassigned_layout.2.1,
          legal_preassigned_layout.2.2, by decide⟩,
        legal_preassigned_layout.1, legal_preassigned_layout.2.1,
        legal_preassigned_layout.2.2, illegal_all_codex_layout_is_rejected,
        rfl, protocol_initial_plan_is_compatible,
        (fun _ _ _ _ _ planned ineligible =>
          initial_plan_ineligible_is_rejected planned ineligible),
        mismatched_initial_plan_is_rejected,
        (fun _ _ _ _ fallback => fallback_selection_requires_a_tried_origin fallback),
        (fun _ _ _ _ fallback => fallback_selection_requires_exhausted_origin fallback),
        successful_fix_consumes_implementation_carrier,
        all_worker_attempts_are_recorded inlineConsensusModel,
        worker_mode_advance_consumes_selector_and_availability inlineConsensusModel,
        inline_choose_worker_mode_routes_before_launch,
        concrete_choose_worker_mode_routing_is_pinned,
        legal_worker_stage_initially_progresses_or_abstains inlineConsensusModel⟩
  | s3 =>
      exact ⟨fun _ _ _ _ _ _ step =>
        flight_failure_occurs_only_after_precommitted_budget_exhaustion step,
        fun _ _ _ _ execution =>
          every_execution_uses_prelaunch_retry_commitment execution⟩
  | s4 =>
      refine ⟨by simp [inlineConsensusModel, Complete],
        by simp [inlineConsensusModel, Complete],
        by simp [inlineConsensusModel, Complete], ?_⟩
      intro proxy carrier workerCarrier
      cases proxy <;> cases carrier <;>
        simp_all [inlineConsensusModel, Complete, evidenceFromProxyOnly]
  | s5 =>
      exact ⟨(fun _ _ _ _ step => abstain_event_enters_absorbing_state step),
        fun _ _ _ _ abstained => abstained_state_has_no_successor abstained⟩
  | s6 =>
      refine ⟨?_, ?_, two_distinct_complete_goal_artifacts_exist,
        complete_goal_snapshot_is_accepted,
        full_snapshot_with_wrong_artifact_is_rejected,
        empty_visible_fields_are_rejected⟩
      · intro config state role Verdict report authorized
        exact authorized.isolatedView
      · intro config state final event unavailable step
        exact unavailable_isolation_allows_only_abstain unavailable step
  | s7 =>
      exact ⟨by decide, by decide, by decide,
        heterogeneous_correlated_conclusions_are_not_independent,
        constant_conclusions_are_independent⟩
  | s8 =>
      exact ⟨design_and_review_router_exits_have_executable_transitions,
        by decide, by decide, by decide, design_router_rejects_single_perspective,
        review_router_reject_precedence, review_router_approve_without_reject,
        review_router_all_comment, exact_roster_bool_iff, termination_router_permit_iff,
        termination_fake_roster_precedence, termination_unsatisfied_precedence,
        termination_evidence_gap_precedence⟩
  | s9 =>
      rcases termination_router_sound_maximal_unique with
        ⟨sound, greatest, unique, abstainSound, abstainStrict, majorityStrict,
          majorityUnsound⟩
      exact ⟨by decide, termination_admits_iff, sound, greatest, unique,
        abstainSound, abstainStrict,
        majorityStrict, majorityUnsound, nonpermitting_observation_cannot_admit,
        (fun _ _ _ _ step => every_protocol_event_increments_epoch step),
        (fun _ _ _ _ step => termination_gate_requires_current_done_review step),
        (fun _ _ _ _ carried step =>
          every_protocol_event_invalidates_carried_permit carried step),
        (fun _ _ _ _ step => no_stale_termination_permit_after_fix
          inlineConsensusModel _ _ _ _ step),
        carried_permit_invalidation_is_recoverable inlineConsensusModel,
        stale_permit_cannot_finish_and_fresh_evaluation_is_reachable,
        implementation_branch_preserves_permit_payload⟩
  | s10 =>
      refine ⟨rfl, (fun _ => Iff.rfl),
        (fun _ _ _ _ execution => every_execution_uses_authorized_shared_budget execution),
        trivial, trivial, trivial, trivial, ?_⟩
      intro config run
      exact ⟨(every_maximal_run_is_bounded config run).2.2.1,
        (every_maximal_run_is_bounded config run).2.2.2⟩

theorem inline_consensus_model_models_every_clause :
    forall clause, ModelsClause inlineConsensusModel clause :=
  required_fixture_suite_is_pinned

theorem repair_acceptance_contract_is_pinned :
    RepairAcceptanceContract inlineConsensusModel :=
  ⟨router_transitions_are_exhaustive,
    heterogeneous_correlated_conclusions_are_not_independent,
    constant_conclusions_are_independent,
    carried_permit_invalidation_is_recoverable inlineConsensusModel,
    all_worker_attempts_are_recorded inlineConsensusModel,
    worker_mode_advance_consumes_selector_and_availability inlineConsensusModel,
    inline_choose_worker_mode_routes_before_launch⟩

end D5.S0.History.Consensus.InlineConsensusProtocolFixtures
