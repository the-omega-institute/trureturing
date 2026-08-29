/- GID: D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three adjudication consumers factor through the signature; target laundering does not. -/

import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.RoleLedgerPrefixStability
import D5.S3.ConceptDynamics.DefinitionEscapeLaws.ScientificGainGeneralizationReversal

/- Library-search audit trail (2026-08-30):
   * Exact and shape searches for `AdjudicationSignature`, `SameOut_NA`,
     `SameOut_AJ`, `SameOut_TL`, `SameOut_SG`, and adjudication-signature
     sufficiency found no frozen declaration in `D5` or pinned Mathlib.
   * The canonical `AdjudicationSnapshot`, `ProspectiveCommitment`,
     `SketchTargetLaundering`, and `RegradeReport` carriers are imported from
     `Governance.TargetLaunderingCriterion` through the frozen scientific-gain
     module; they are not redeclared here.
   * The full finite role event and ledger carriers are imported from the frozen
     `RoleLedgerPrefixStability` module.  The Part 55 signature and consumer
     skeletons below are the source definitions over those frozen carriers.
   * Coordinate-wise search confirms that non-anticipation reads visibility and
     direct contamination, admissible judging additionally reads role existence
     and the closure-touch bit, and scientific gain adds only SameOut-frozen
     fields.  Target laundering also reads whole-commitment report identities
     and `frozenAt`, neither of which occurs in the four-coordinate signature. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.DefinitionEscapeSignatures.AdjudicationSignatureSufficiency

open D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.ScientificGainGeneralizationReversal
open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

universe u v

/-- Every recorded role event must use evidence visible at its own event. -/
def ValidTrace
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time] {n : Round}
    (ledger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time n) :
    Prop :=
  forall event, event ∈ ledger.events ->
    event.evidence ∈ snapshot.filtration.seen event.eventId

/-- The source prefix simultaneously applies its event, round, and time cuts. -/
def InAdjudicationPrefix
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time] {n : Round}
    (ledger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (_valid : ValidTrace ledger snapshot)
    (event : RoleUseEvent EventId Evidence Round Artifact Protocol Time) : Prop :=
  event ∈ ledger.events ∧ event.eventId <= snapshot.decisionEvent ∧
    event.round <= n ∧ event.usedAt <= snapshot.decidedAt

/-- Roles remain relational: only existence in the adjudication prefix is read. -/
def RolesAt
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time] {n : Round}
    (ledger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (valid : ValidTrace ledger snapshot) (record : Evidence) :
    Set LedgerEvidenceRole :=
  {role | exists event,
    InAdjudicationPrefix ledger snapshot valid event ∧
      event.evidence = record ∧ event.round = n ∧ event.role = role}

/-- Adaptive contamination is exactly an adaptive-role event whose dependency
set touches the frozen dependency closure. -/
def AdaptiveUseInClosure
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time] {n : Round}
    (ledger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (valid : ValidTrace ledger snapshot) (record : Evidence) : Prop :=
  exists event,
    InAdjudicationPrefix ledger snapshot valid event ∧
      event.evidence = record ∧
      (event.role = .generate ∨ event.role = .tune ∨ event.role = .select) ∧
      Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure)

/-- The Part 55 admissible-judge consumer over the full role ledger. -/
def AdmissibleJudge
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time] {n : Round}
    (ledger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (valid : ValidTrace ledger snapshot) (record : Evidence) : Prop :=
  .adjudicate ∈ RolesAt ledger snapshot valid record ∧
    record ∉ snapshot.filtration.seen snapshot.freezeEvent ∧
    record ∉ snapshot.evidenceDependencies ∧
    ¬AdaptiveUseInClosure ledger snapshot valid record

/-- The fourth signature coordinate retains only these four consumer roles. -/
def RelevantSignatureRole : LedgerEvidenceRole -> Prop
  | .generate | .tune | .select | .adjudicate => True
  | .replicate => False

/-- The three roles that can contaminate an admissible judge. -/
def AdaptiveSignatureRole : LedgerEvidenceRole -> Prop
  | .generate | .tune | .select => True
  | .adjudicate | .replicate => False

/-- One atom in the role-existence projection, including only the closure-touch
indicator and none of event id, time, protocol, order, or multiplicity. -/
structure RoleSignatureAtom (Evidence Round : Type u) where
  evidence : Evidence
  round : Round
  role : LedgerEvidenceRole
  touchesClosure : Bool

/-- Boolean indicator for whether one event's dependencies touch the closure. -/
noncomputable def closureTouchBit
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [Preorder EventId] [Preorder Time] {n : Round}
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (event : RoleUseEvent EventId Evidence Round Artifact Protocol Time) : Bool := by
  classical
  exact decide (Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure))

/-- The role-existence signature coordinate from Part 55.1. -/
noncomputable def roleExistenceProjection
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    [DecidableEq Evidence] {n : Round}
    (records : Finset Evidence)
    (ledger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (valid : ValidTrace ledger snapshot) :
    Set (RoleSignatureAtom Evidence Round) :=
  {atom | exists event,
    InAdjudicationPrefix ledger snapshot valid event ∧
      event.evidence ∈ records ∧ RelevantSignatureRole event.role ∧
      atom =
        { evidence := event.evidence
          round := event.round
          role := event.role
          touchesClosure := closureTouchBit snapshot event }}

/-- The four coordinates of the exact Part 55.1 adjudication signature. -/
structure AdjudicationSignature (Evidence Round : Type u) where
  freezeVisible : Set Evidence
  decisionVisible : Set Evidence
  directlyContaminated : Set Evidence
  roleProjection : Set (RoleSignatureAtom Evidence Round)

/-- Complete Part 55.1 signature of a finite valid history. -/
noncomputable def adjudicationSignature
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    [DecidableEq Evidence] {n : Round}
    (records : Finset Evidence)
    (ledger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (valid : ValidTrace ledger snapshot) :
    AdjudicationSignature Evidence Round :=
  { freezeVisible :=
      {record | record ∈ records ∧
        record ∈ snapshot.filtration.seen snapshot.freezeEvent}
    decisionVisible :=
      {record | record ∈ records ∧
        record ∈ snapshot.filtration.seen snapshot.decisionEvent}
    directlyContaminated :=
      {record | record ∈ records ∧ record ∈ snapshot.evidenceDependencies}
    roleProjection := roleExistenceProjection records ledger snapshot valid }

/-- SameOut for non-anticipation fixes the common record set and point. -/
structure SameOutNA {Evidence : Type u} [DecidableEq Evidence]
    (records : Finset Evidence) (record : Evidence) : Prop where
  recordInHistory : record ∈ records

/-- SameOut for admissible judging fixes the common record set and point. -/
structure SameOutAJ {Evidence : Type u} [DecidableEq Evidence]
    (records : Finset Evidence) (record : Evidence) : Prop where
  recordInHistory : record ∈ records

/-- Equality of every commitment field outside the adjudication snapshot. -/
structure SameCommitmentOutputs
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact] {n : Round}
    (left right :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n) :
    Prop where
  targetChain : left.targetChain = right.targetChain
  domain : left.domain = right.domain
  epsilon : left.epsilon = right.epsilon
  conditions : left.conditions = right.conditions
  comparator : left.comparator = right.comparator
  testPlan : left.testPlan = right.testPlan
  baseline : left.baseline = right.baseline
  weightSpec : left.weightSpec = right.weightSpec
  decision : left.decision = right.decision
  committedArtifacts : left.committedArtifacts = right.committedArtifacts
  baselineArtifacts : left.baselineArtifacts = right.baselineArtifacts

/-- SameOut for target laundering fixes both commitments outside adjudication;
the evaluator, evidence point, and report are common theorem parameters. -/
structure SameOutTL
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Evidence]
    [DecidableEq Artifact] {n : Round}
    (records : Finset Evidence) (record : Evidence)
    (oldK newK oldK' newK' :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n) :
    Prop where
  recordInHistory : record ∈ records
  oldOutputs : SameCommitmentOutputs oldK oldK'
  newOutputs : SameCommitmentOutputs newK newK'

/-- SameOut for scientific gain fixes every non-history field read by it. -/
structure SameOutSG
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Evidence]
    [DecidableEq Artifact] {n : Round}
    (records : Finset Evidence) (record : Evidence)
    (left right :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n) :
    Prop where
  recordInHistory : record ∈ records
  outputs : SameCommitmentOutputs left right

private theorem restricted_membership_iff_of_eq
    {Evidence : Type u}
    {records : Finset Evidence} {left right : Set Evidence} {record : Evidence}
    (inRecords : record ∈ records)
    (equalRestricted :
      {item | item ∈ records ∧ item ∈ left} =
        {item | item ∈ records ∧ item ∈ right}) :
    record ∈ left <-> record ∈ right := by
  constructor
  · intro inLeft
    have inRestricted : record ∈ {item | item ∈ records ∧ item ∈ left} :=
      ⟨inRecords, inLeft⟩
    rw [equalRestricted] at inRestricted
    exact inRestricted.2
  · intro inRight
    have inRestricted : record ∈ {item | item ∈ records ∧ item ∈ right} :=
      ⟨inRecords, inRight⟩
    rw [← equalRestricted] at inRestricted
    exact inRestricted.2

private theorem adjudicate_role_iff_projected
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    [DecidableEq Evidence] {n : Round}
    (records : Finset Evidence)
    (ledger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (valid : ValidTrace ledger snapshot) (record : Evidence)
    (inRecords : record ∈ records) :
    .adjudicate ∈ RolesAt ledger snapshot valid record <->
      exists bit,
        ({ evidence := record
           round := n
           role := .adjudicate
           touchesClosure := bit } : RoleSignatureAtom Evidence Round) ∈
          roleExistenceProjection records ledger snapshot valid := by
  constructor
  · rintro ⟨event, inPrefix, evidenceEq, roundEq, roleEq⟩
    refine ⟨closureTouchBit snapshot event, event, inPrefix, ?_, ?_, ?_⟩
    · simpa only [evidenceEq] using inRecords
    · simp only [roleEq, RelevantSignatureRole]
    · cases event
      cases evidenceEq
      cases roundEq
      cases roleEq
      rfl
  · rintro ⟨bit, event, inPrefix, _, _, atomEq⟩
    have evidenceEq : event.evidence = record :=
      (congrArg RoleSignatureAtom.evidence atomEq).symm
    have roundEq : event.round = n :=
      (congrArg RoleSignatureAtom.round atomEq).symm
    have roleEq : event.role = .adjudicate :=
      (congrArg RoleSignatureAtom.role atomEq).symm
    exact ⟨event, inPrefix, evidenceEq, roundEq, roleEq⟩

private theorem adaptive_use_iff_projected
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    [DecidableEq Evidence] {n : Round}
    (records : Finset Evidence)
    (ledger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (valid : ValidTrace ledger snapshot) (record : Evidence)
    (inRecords : record ∈ records) :
    AdaptiveUseInClosure ledger snapshot valid record <->
      exists round role,
        AdaptiveSignatureRole role ∧
          ({ evidence := record
             round := round
             role := role
             touchesClosure := true } : RoleSignatureAtom Evidence Round) ∈
            roleExistenceProjection records ledger snapshot valid := by
  constructor
  · rintro ⟨event, inPrefix, evidenceEq, adaptiveRole, touches⟩
    refine ⟨event.round, event.role, ?_, event, inPrefix, ?_, ?_, ?_⟩
    · rcases adaptiveRole with roleEq | roleEq | roleEq <;>
        simp only [roleEq, AdaptiveSignatureRole]
    · simpa only [evidenceEq] using inRecords
    · rcases adaptiveRole with roleEq | roleEq | roleEq <;>
        simp only [roleEq, RelevantSignatureRole]
    · have bitEq : closureTouchBit snapshot event = true := by
        simp [closureTouchBit, touches]
      rw [← evidenceEq, ← bitEq]
  · rintro ⟨round, role, adaptiveRole, event, inPrefix, _, _, atomEq⟩
    have evidenceEq : event.evidence = record :=
      (congrArg RoleSignatureAtom.evidence atomEq).symm
    have roleEq : event.role = role :=
      (congrArg RoleSignatureAtom.role atomEq).symm
    have bitEq : closureTouchBit snapshot event = true :=
      (congrArg RoleSignatureAtom.touchesClosure atomEq).symm
    have touches :
        Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure) := by
      classical
      simpa [closureTouchBit] using bitEq
    have adaptiveEventRole :
        event.role = .generate ∨ event.role = .tune ∨ event.role = .select := by
      cases role <;> simp_all [AdaptiveSignatureRole]
    exact ⟨event, inPrefix, evidenceEq, adaptiveEventRole, touches⟩

/-- OP1-NA is true: decision visibility, freeze visibility, and direct
contamination are literal signature coordinates. -/
theorem non_anticipating_signature_sufficiency
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    [DecidableEq Evidence] {n : Round}
    (records : Finset Evidence)
    (leftLedger rightLedger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (left right : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (leftValid : ValidTrace leftLedger left)
    (rightValid : ValidTrace rightLedger right) (record : Evidence)
    (signatureEq :
      adjudicationSignature records leftLedger left leftValid =
        adjudicationSignature records rightLedger right rightValid)
    (sameOut : SameOutNA records record) :
    NonAnticipating left record <-> NonAnticipating right record := by
  have freezeEq :
      {item | item ∈ records ∧ item ∈ left.filtration.seen left.freezeEvent} =
        {item | item ∈ records ∧ item ∈ right.filtration.seen right.freezeEvent} := by
    simpa only [adjudicationSignature] using
      congrArg AdjudicationSignature.freezeVisible signatureEq
  have decisionEq :
      {item | item ∈ records ∧ item ∈ left.filtration.seen left.decisionEvent} =
        {item | item ∈ records ∧ item ∈ right.filtration.seen right.decisionEvent} := by
    simpa only [adjudicationSignature] using
      congrArg AdjudicationSignature.decisionVisible signatureEq
  have contaminationEq :
      {item | item ∈ records ∧ item ∈ left.evidenceDependencies} =
        {item | item ∈ records ∧ item ∈ right.evidenceDependencies} := by
    simpa only [adjudicationSignature] using
      congrArg AdjudicationSignature.directlyContaminated signatureEq
  have freezeIff := restricted_membership_iff_of_eq
    sameOut.recordInHistory freezeEq
  have decisionIff := restricted_membership_iff_of_eq
    sameOut.recordInHistory decisionEq
  have contaminationIff := restricted_membership_iff_of_eq
    sameOut.recordInHistory contaminationEq
  simp only [NonAnticipating]
  tauto

/-- OP1-AJ is true: adjudication-role existence and every adaptive
closure-touch witness are exactly recoverable from the fourth coordinate. -/
theorem admissible_judge_signature_sufficiency
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    [DecidableEq Evidence] {n : Round}
    (records : Finset Evidence)
    (leftLedger rightLedger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (left right : AdjudicationSnapshot EventId Evidence Round Artifact Time n)
    (leftValid : ValidTrace leftLedger left)
    (rightValid : ValidTrace rightLedger right) (record : Evidence)
    (signatureEq :
      adjudicationSignature records leftLedger left leftValid =
        adjudicationSignature records rightLedger right rightValid)
    (sameOut : SameOutAJ records record) :
    AdmissibleJudge leftLedger left leftValid record <->
      AdmissibleJudge rightLedger right rightValid record := by
  have freezeEq :
      {item | item ∈ records ∧ item ∈ left.filtration.seen left.freezeEvent} =
        {item | item ∈ records ∧ item ∈ right.filtration.seen right.freezeEvent} := by
    simpa only [adjudicationSignature] using
      congrArg AdjudicationSignature.freezeVisible signatureEq
  have contaminationEq :
      {item | item ∈ records ∧ item ∈ left.evidenceDependencies} =
        {item | item ∈ records ∧ item ∈ right.evidenceDependencies} := by
    simpa only [adjudicationSignature] using
      congrArg AdjudicationSignature.directlyContaminated signatureEq
  have roleEq :
      roleExistenceProjection records leftLedger left leftValid =
        roleExistenceProjection records rightLedger right rightValid := by
    simpa only [adjudicationSignature] using
      congrArg AdjudicationSignature.roleProjection signatureEq
  have freezeIff := restricted_membership_iff_of_eq
    sameOut.recordInHistory freezeEq
  have contaminationIff := restricted_membership_iff_of_eq
    sameOut.recordInHistory contaminationEq
  have judgeRoleIff :
      .adjudicate ∈ RolesAt leftLedger left leftValid record <->
        .adjudicate ∈ RolesAt rightLedger right rightValid record := by
    rw [adjudicate_role_iff_projected records leftLedger left leftValid record
      sameOut.recordInHistory]
    rw [adjudicate_role_iff_projected records rightLedger right rightValid record
      sameOut.recordInHistory]
    constructor <;> rintro ⟨bit, projected⟩ <;> refine ⟨bit, ?_⟩
    · rwa [← roleEq]
    · rwa [roleEq]
  have adaptiveIff :
      AdaptiveUseInClosure leftLedger left leftValid record <->
        AdaptiveUseInClosure rightLedger right rightValid record := by
    rw [adaptive_use_iff_projected records leftLedger left leftValid record
      sameOut.recordInHistory]
    rw [adaptive_use_iff_projected records rightLedger right rightValid record
      sameOut.recordInHistory]
    constructor <;> rintro ⟨round, role, adaptiveRole, projected⟩ <;>
      refine ⟨round, role, adaptiveRole, ?_⟩
    · rwa [← roleEq]
    · rwa [roleEq]
  simp only [AdmissibleJudge]
  tauto

/-- OP1-SG is true: SameOut freezes the action sets and comparator, while its
only history-dependent conjunct is OP1-NA. -/
theorem scientific_gain_signature_sufficiency
    {EventId Evidence Round Action Protocol Time TargetChain Domain Epsilon
      Condition Comparator TestPlan Baseline WeightSpec : Type u}
    {Loss : Type v} [LT Loss]
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    [DecidableEq Evidence] [DecidableEq Action] {n : Round}
    (records : Finset Evidence)
    (leftLedger rightLedger :
      VersionedRoleLedger EventId Evidence Round Action Protocol Time)
    (left right :
      ProspectiveCommitment EventId Evidence Round Action Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
    (leftValid : ValidTrace leftLedger left.adjudication)
    (rightValid : ValidTrace rightLedger right.adjudication)
    (evaluate : Comparator -> Action -> Evidence -> Loss)
    (record : Evidence) (committed baselineAction : Action)
    (signatureEq :
      adjudicationSignature records leftLedger left.adjudication leftValid =
        adjudicationSignature records rightLedger right.adjudication rightValid)
    (sameOut : SameOutSG records record left right) :
    ScientificGain evaluate left record committed baselineAction <->
      ScientificGain evaluate right record committed baselineAction := by
  have nonAnticipatingIff := non_anticipating_signature_sufficiency
    records leftLedger rightLedger left.adjudication right.adjudication
      leftValid rightValid record signatureEq
      ⟨sameOut.recordInHistory⟩
  have committedIff :
      committed ∈ left.committedArtifacts <->
        committed ∈ right.committedArtifacts := by
    rw [sameOut.outputs.committedArtifacts]
  have baselineIff :
      baselineAction ∈ left.baselineArtifacts <->
        baselineAction ∈ right.baselineArtifacts := by
    rw [sameOut.outputs.baselineArtifacts]
  have evaluationIff :
      evaluate left.comparator committed record <
          evaluate left.comparator baselineAction record <->
        evaluate right.comparator committed record <
          evaluate right.comparator baselineAction record := by
    rw [sameOut.outputs.comparator]
  simp only [ScientificGain]
  tauto

namespace TargetLaunderingCounterexample

abbrev Commitment :=
  ProspectiveCommitment Bool Bool Unit Bool Bool Bool Unit Unit Bool Unit Unit Unit Unit ()

abbrev Ledger := VersionedRoleLedger Bool Bool Unit Bool Unit Bool

def filtration : EvidenceFiltration Bool Bool where
  seen _ := Set.univ
  monotone := by
    intro _ _ _
    exact Set.Subset.rfl

def snapshot (frozenAt : Bool) : AdjudicationSnapshot Bool Bool Unit Bool Bool () where
  freezeEvent := false
  decisionEvent := true
  frozenAt := frozenAt
  decidedAt := true
  freezeBeforeDecision := by decide
  timeBeforeDecision := by cases frozenAt <;> decide
  filtration := filtration
  dependencyClosure := Set.univ
  evidenceDependencies := ∅

def decision : DecisionSet Bool where
  candidates := Finset.univ
  feasible := Finset.univ
  current := none
  feasibleFromCandidates := Finset.Subset.rfl

def commitment (frozenAt condition : Bool) : Commitment where
  adjudication := snapshot frozenAt
  targetChain := false
  domain := ()
  epsilon := ()
  conditions := condition
  comparator := ()
  testPlan := ()
  baseline := ()
  weightSpec := ()
  decision := decision
  committedArtifacts := ∅
  baselineArtifacts := ∅
  committedFromCandidates := by simp
  baselinesFromCandidates := by simp
  committedInClosure := by simp

def oldK : Commitment := commitment false false
def newK : Commitment := commitment false true
def newK' : Commitment := commitment true true

def ledger : Ledger where
  events := []
  uniqueEventIds := by simp
  strictEventOrder := by simp
  indexRespectsRound := by simp
  indexRespectsTime := by simp

theorem valid (K : Commitment) : ValidTrace ledger K.adjudication := by
  simp [ValidTrace, ledger]

def evaluate : Commitment -> Bool -> Unit := fun _ _ => ()

def report : RegradeReport Commitment Bool Unit Bool evaluate where
  original := oldK
  revised := newK
  evidence := true
  regradedVerdict := ()
  regradesOldRound := rfl
  attributedTo := oldK
  occurredAt := false

def records : Finset Bool := {true}

theorem same_outputs_new : SameCommitmentOutputs newK newK' := by
  constructor <;> rfl

theorem left_target_laundering :
    SketchTargetLaundering evaluate oldK newK true report := by
  simp [SketchTargetLaundering, oldK, newK, commitment, snapshot, filtration,
    protectedCoordinates, report, evaluate]

theorem right_not_target_laundering :
    ¬SketchTargetLaundering evaluate oldK newK' true report := by
  intro laundering
  rcases laundering with ⟨_, _, _, revisedEq, _⟩
  have frozenAtEq : false = true := congrArg
    (fun K : Commitment => K.adjudication.frozenAt) revisedEq
  exact Bool.false_ne_true frozenAtEq

end TargetLaunderingCounterexample

/-- OP1-TL is false.  Two finite valid histories have equal complete
signatures and all SameOut fields, but changing only the omitted `frozenAt`
field makes the common report point to the left new commitment and not the
right one. -/
theorem target_laundering_signature_counterexample :
    exists (records : Finset Bool)
      (oldK newK oldK' newK' : TargetLaunderingCounterexample.Commitment)
      (oldLedger newLedger oldLedger' newLedger' :
        TargetLaunderingCounterexample.Ledger)
      (oldValid : ValidTrace oldLedger oldK.adjudication)
      (newValid : ValidTrace newLedger newK.adjudication)
      (oldValid' : ValidTrace oldLedger' oldK'.adjudication)
      (newValid' : ValidTrace newLedger' newK'.adjudication)
      (evaluate : TargetLaunderingCounterexample.Commitment -> Bool -> Unit)
      (report : RegradeReport TargetLaunderingCounterexample.Commitment Bool
        Unit Bool evaluate),
      adjudicationSignature records oldLedger oldK.adjudication oldValid =
        adjudicationSignature records oldLedger' oldK'.adjudication oldValid' ∧
      adjudicationSignature records newLedger newK.adjudication newValid =
        adjudicationSignature records newLedger' newK'.adjudication newValid' ∧
      SameOutTL records true oldK newK oldK' newK' ∧
      SketchTargetLaundering evaluate oldK newK true report ∧
      ¬SketchTargetLaundering evaluate oldK' newK' true report := by
  open TargetLaunderingCounterexample in
  refine ⟨records, oldK, newK, oldK, newK', ledger, ledger, ledger, ledger,
    valid oldK, valid newK, valid oldK, valid newK', evaluate, report,
    rfl, rfl, ?_, left_target_laundering, right_not_target_laundering⟩
  exact
    { recordInHistory := by simp [records]
      oldOutputs := by constructor <;> rfl
      newOutputs := same_outputs_new }

/-- The three sufficient atoms have jointly satisfiable finite hypotheses,
independently of their proofs; the fourth atom has the counterexample above. -/
example :
    let K := TargetLaunderingCounterexample.oldK
    let ledger := TargetLaunderingCounterexample.ledger
    let valid := TargetLaunderingCounterexample.valid K
    adjudicationSignature TargetLaunderingCounterexample.records ledger
          K.adjudication valid =
        adjudicationSignature TargetLaunderingCounterexample.records ledger
          K.adjudication valid ∧
      SameOutNA TargetLaunderingCounterexample.records true ∧
      SameOutAJ TargetLaunderingCounterexample.records true ∧
      SameOutSG TargetLaunderingCounterexample.records true K K := by
  dsimp only
  refine ⟨rfl, ⟨?_⟩, ⟨?_⟩, ⟨?_, ?_⟩⟩
  · simp [TargetLaunderingCounterexample.records]
  · simp [TargetLaunderingCounterexample.records]
  · simp [TargetLaunderingCounterexample.records]
  · constructor <;> rfl

#print axioms non_anticipating_signature_sufficiency
#print axioms admissible_judge_signature_sufficiency
#print axioms scientific_gain_signature_sufficiency
#print axioms target_laundering_signature_counterexample

end D5.S3.ConceptDynamics.DefinitionEscapeSignatures.AdjudicationSignatureSufficiency
