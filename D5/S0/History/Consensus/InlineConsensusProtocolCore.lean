/- GID: D5/S0/History/Consensus/InlineConsensusProtocolCore
   generality: G
   mirror-B: D5/B/S0/History/Consensus/InlineConsensusProtocolCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite protocol observations, dispatch plans, and fail-closed routers. -/
import Mathlib

namespace D5.S0.History.Consensus.InlineConsensusOptimality

inductive Stage
  | intake | chooseWorkerMode | thinkingPanelWorkers | metaJudge
  | implementationWorker | reviewTripletWorkers | fixOrDone
  deriving DecidableEq, Fintype, Repr

def Stage.rank : Stage -> Nat
  | .intake => 0
  | .chooseWorkerMode => 1
  | .thinkingPanelWorkers => 2
  | .metaJudge => 3
  | .implementationWorker => 4
  | .reviewTripletWorkers => 5
  | .fixOrDone => 6

def Stage.next : Stage -> Option Stage
  | .intake => some .chooseWorkerMode
  | .chooseWorkerMode => some .thinkingPanelWorkers
  | .thinkingPanelWorkers => some .metaJudge
  | .metaJudge => some .implementationWorker
  | .implementationWorker => some .reviewTripletWorkers
  | .reviewTripletWorkers => some .fixOrDone
  | .fixOrDone => none

def Stage.Successor (source target : Stage) : Prop := source.next = some target

inductive Carrier
  | codexCli | nyxidOracle | isolatedTokenSubagent | abstain
  deriving DecidableEq, Fintype, Repr

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

abbrev Eligibility := Carrier -> Bool

def eligibleUntried (eligible : Eligibility) (tried : Finset Carrier) : Finset Carrier :=
  Finset.univ.filter fun carrier =>
    carrier != .abstain && eligible carrier && !(decide (carrier ∈ tried))

def selectCarrier (eligible : Eligibility) (tried : Finset Carrier) : Carrier :=
  if available : (eligibleUntried eligible tried).Nonempty then
    (eligibleUntried eligible tried).min' available
  else
    .abstain

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
  | .isolatedTokenSubagent, .subagent envelope verdict =>
      envelope = true /\ verdict = true
  | _, _ => False

inductive CompletionConjunct
  | carrierExit | resultArtifact | envelope | verdict | sentinel
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

inductive GoalArtifactField
  | rawUserInput | normalizedGoal | constraints | successCriteria | iterationQuestion
  | harness | revisions
  deriving DecidableEq, Fintype, Repr

inductive GoalArtifactDigest
  | digestA | digestB
  deriving DecidableEq, Fintype, Repr

structure GoalArtifact where
  rawUserInput : Option GoalArtifactDigest
  normalizedGoal : Option GoalArtifactDigest
  constraints : Option GoalArtifactDigest
  successCriteria : Option GoalArtifactDigest
  iterationQuestion : Option GoalArtifactDigest
  harness : Option GoalArtifactDigest
  revisions : Option GoalArtifactDigest
  deriving DecidableEq, Repr

structure GoalArtifactSnapshot where
  artifact : GoalArtifact
  visibleFields : Finset GoalArtifactField
  deriving DecidableEq

def GoalArtifact.Complete (artifact : GoalArtifact) : Prop :=
  artifact.rawUserInput.isSome = true /\ artifact.normalizedGoal.isSome = true /\
    artifact.constraints.isSome = true /\ artifact.successCriteria.isSome = true /\
    artifact.iterationQuestion.isSome = true /\ artifact.harness.isSome = true /\
    artifact.revisions.isSome = true

def GoalArtifactSnapshot.ContainsComplete
    (shared : GoalArtifact) (snapshot : GoalArtifactSnapshot) : Prop :=
  shared.Complete /\ snapshot.artifact = shared /\ snapshot.visibleFields = Finset.univ

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
  | .thinkingPanelWorkers => role.IsThinking
  | .implementationWorker => role = .implementation
  | .reviewTripletWorkers => role.IsReview
  | .fixOrDone => role = .implementation \/ role.IsReview \/ role.IsTermination
  | .intake | .chooseWorkerMode | .metaJudge => False

def CarrierLegalAt (stage : Stage) (role : SeatRole) (carrier : Carrier) : Prop :=
  role.LegalAt stage /\ carrier != .abstain

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
  sameRoundPeerOutputs : Finset SeatRole
  deriving DecidableEq

def SeatView.IsolatedComplete (shared : GoalArtifact) (view : SeatView) : Prop :=
  view.goalArtifact.ContainsComplete shared /\ view.sameRoundPeerOutputs = {}

structure WorkerReport (Verdict : Type) where
  view : SeatView
  carrier : Carrier
  completionObservation : CompletionObservation
  verdict : Verdict

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

inductive ReviewSeat
  | architecture | quality | tests
  deriving DecidableEq, Fintype, Repr

def ReviewSeat.role : ReviewSeat -> SeatRole
  | .architecture => .architectureReview
  | .quality => .qualityReview
  | .tests => .testsReview

inductive TerminationSeat
  | criterionEvidence | residualGap | claimIntegrity
  deriving DecidableEq, Fintype, Repr

def TerminationSeat.role : TerminationSeat -> SeatRole
  | .criterionEvidence => .criterionEvidence
  | .residualGap => .residualGap
  | .claimIntegrity => .claimIntegrity

def seatsAssignedTo {Seat : Type} [Fintype Seat] [DecidableEq Seat]
    (assignment : Seat -> Carrier) (carrier : Carrier) : Finset Seat :=
  Finset.univ.filter fun seat => assignment seat = carrier

def MultiSeatLayout {Seat : Type} [Fintype Seat] [DecidableEq Seat]
    (assignment : Seat -> Carrier) : Prop :=
  (seatsAssignedTo assignment .isolatedTokenSubagent).card = 1 /\
    (seatsAssignedTo assignment .nyxidOracle).card = 1 /\
    seatsAssignedTo assignment .abstain = {}

instance {Seat : Type} [Fintype Seat] [DecidableEq Seat]
    (assignment : Seat -> Carrier) : Decidable (MultiSeatLayout assignment) := by
  unfold MultiSeatLayout
  infer_instance

structure DispatchPlan where
  thinking : ThinkingSeat -> Carrier
  implementation : Carrier
  review : ReviewSeat -> Carrier
  termination : TerminationSeat -> Carrier
  thinkingLayout : MultiSeatLayout thinking
  reviewLayout : MultiSeatLayout review
  terminationLayout : MultiSeatLayout termination

def DispatchPlan.carrierAt (plan : DispatchPlan) (stage : Stage)
    (role : SeatRole) : Option Carrier :=
  match stage, role with
  | .thinkingPanelWorkers, .teleology => some (plan.thinking .teleology)
  | .thinkingPanelWorkers, .parsimony => some (plan.thinking .parsimony)
  | .thinkingPanelWorkers, .fidelity => some (plan.thinking .fidelity)
  | .thinkingPanelWorkers, .naturalOwnership => some (plan.thinking .naturalOwnership)
  | .thinkingPanelWorkers, .proportionalContainment =>
      some (plan.thinking .proportionalContainment)
  | .thinkingPanelWorkers, .worth => some (plan.thinking .worth)
  | .implementationWorker, .implementation | .fixOrDone, .implementation =>
      some plan.implementation
  | .reviewTripletWorkers, .architectureReview | .fixOrDone, .architectureReview =>
      some (plan.review .architecture)
  | .reviewTripletWorkers, .qualityReview | .fixOrDone, .qualityReview =>
      some (plan.review .quality)
  | .reviewTripletWorkers, .testsReview | .fixOrDone, .testsReview =>
      some (plan.review .tests)
  | .fixOrDone, .criterionEvidence => some (plan.termination .criterionEvidence)
  | .fixOrDone, .residualGap => some (plan.termination .residualGap)
  | .fixOrDone, .claimIntegrity => some (plan.termination .claimIntegrity)
  | _, _ => none

def InitialPlanCompatible
    (eligible : Stage -> SeatRole -> Eligibility) (plan : DispatchPlan) : Prop :=
  forall stage role carrier, plan.carrierAt stage role = some carrier ->
    CarrierLegalAt stage role carrier /\ eligible stage role carrier = true

inductive ThinkingVerdict
  | propose | revise | reject | abstain
  deriving DecidableEq, Fintype, Repr

inductive PlanIdentity
  | planA | planB | planC
  deriving DecidableEq, Fintype, Repr

structure ThinkingReport extends WorkerReport ThinkingVerdict where
  plan : Option PlanIdentity
  presentedAsConsensus : Bool

abbrev ThinkingResults := ThinkingSeat -> ThinkingReport
abbrev PlanCompatibility := PlanIdentity -> PlanIdentity -> Bool

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

def allThinkingVerdictsAre (results : ThinkingResults) (verdict : ThinkingVerdict) : Bool :=
  (results .teleology).toWorkerReport.verdict == verdict &&
    (results .parsimony).toWorkerReport.verdict == verdict &&
    (results .fidelity).toWorkerReport.verdict == verdict &&
    (results .naturalOwnership).toWorkerReport.verdict == verdict &&
    (results .proportionalContainment).toWorkerReport.verdict == verdict &&
    (results .worth).toWorkerReport.verdict == verdict

def anyThinkingVerdictIs (results : ThinkingResults) (verdict : ThinkingVerdict) : Bool :=
  (results .teleology).toWorkerReport.verdict == verdict ||
    (results .parsimony).toWorkerReport.verdict == verdict ||
    (results .fidelity).toWorkerReport.verdict == verdict ||
    (results .naturalOwnership).toWorkerReport.verdict == verdict ||
    (results .proportionalContainment).toWorkerReport.verdict == verdict ||
    (results .worth).toWorkerReport.verdict == verdict

def thinkingPlans (results : ThinkingResults) : List PlanIdentity :=
  [(results .teleology).plan, (results .parsimony).plan, (results .fidelity).plan,
    (results .naturalOwnership).plan, (results .proportionalContainment).plan,
    (results .worth).plan].filterMap id

def plansPairwiseCompatible (compatible : PlanCompatibility) (plans : List PlanIdentity) : Bool :=
  plans.all fun first => plans.all fun second => compatible first second

def allThinkingPlansAgree (results : ThinkingResults) : Bool :=
  match (results .teleology).plan with
  | none => false
  | some plan =>
      (results .teleology).plan == some plan && (results .parsimony).plan == some plan &&
        (results .fidelity).plan == some plan &&
        (results .naturalOwnership).plan == some plan &&
        (results .proportionalContainment).plan == some plan &&
        (results .worth).plan == some plan

def thinkingSituation (compatible : PlanCompatibility)
    (results : ThinkingResults) : DesignSituation :=
  if (results .teleology).presentedAsConsensus ||
      (results .parsimony).presentedAsConsensus ||
      (results .fidelity).presentedAsConsensus ||
      (results .naturalOwnership).presentedAsConsensus ||
      (results .proportionalContainment).presentedAsConsensus ||
      (results .worth).presentedAsConsensus then
    .singlePerspective
  else if allThinkingVerdictsAre results .propose && allThinkingPlansAgree results then
    .unanimousActionable
  else if !(anyThinkingVerdictIs results .abstain || anyThinkingVerdictIs results .reject) &&
      (thinkingPlans results).length == Fintype.card ThinkingSeat &&
      plansPairwiseCompatible compatible (thinkingPlans results) &&
      !allThinkingPlansAgree results then
    .compatiblePlans
  else
    .boundedStall

inductive ReviewVerdict
  | approve | comment | reject
  deriving DecidableEq, Fintype, Repr

abbrev ReviewResults := ReviewSeat -> WorkerReport ReviewVerdict
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

inductive TerminationVerdict
  | satisfied | unsatisfied | abstain
  deriving DecidableEq, Fintype, Repr

inductive TerminationSeatResult (seat : TerminationSeat)
  | completed (report : WorkerReport TerminationVerdict)
      (roleMatches : report.view.role = seat.role)
  | invalid
  | missing

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

def TerminationSeatResult.isSatisfiedBool {seat : TerminationSeat} :
    TerminationSeatResult seat -> Bool
  | .completed report _ => report.verdict == .satisfied
  | .invalid | .missing => false

def TerminationSeatResult.isUnsatisfiedBool {seat : TerminationSeat} :
    TerminationSeatResult seat -> Bool
  | .completed report _ => report.verdict == .unsatisfied
  | .invalid | .missing => false

def allSatisfied (observation : TerminationObservation) : Prop :=
  forall seat, (observation.result seat).isSatisfiedBool = true

def allSatisfiedBool (observation : TerminationObservation) : Bool :=
  (observation.result .criterionEvidence).isSatisfiedBool &&
    (observation.result .residualGap).isSatisfiedBool &&
    (observation.result .claimIntegrity).isSatisfiedBool

def anyUnsatisfiedBool (observation : TerminationObservation) : Bool :=
  (observation.result .criterionEvidence).isUnsatisfiedBool ||
    (observation.result .residualGap).isUnsatisfiedBool ||
    (observation.result .claimIntegrity).isUnsatisfiedBool

inductive TerminationExit
  | rejectFakeConsensus | permitClaim | continueAgainstGap | escalateEvidenceGap
  deriving DecidableEq, Fintype, Repr

def terminationRouter (observation : TerminationObservation) : TerminationExit :=
  if exactRosterBool observation.roster then
    if allSatisfiedBool observation then .permitClaim
    else if anyUnsatisfiedBool observation then .continueAgainstGap
    else .escalateEvidenceGap
  else
    .rejectFakeConsensus

def correlatedConclusion (_ : Carrier) (latent : Bool) : Bool := latent

end D5.S0.History.Consensus.InlineConsensusOptimality
