/- GID: D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/TargetLaunderingCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Temporal post-arrival change, regrading, and original attribution. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Fin.Basic

/- Library-search audit trail (2026-08-25):
   * `rg -n 'structure .*Commitment|structure .*Report|Finset Artifact|targetChain|
     weightSpec|regradedVerdict|attributedTo' D5/S3/ConceptDynamics` found no
     matching commitment/report carrier outside this module. `TransportReport`,
     `TruthfulnessSufficiencyIndependence.ReportProfile`, and `ProvenanceReport`
     have different fields and do not encode a prospective regrade.
   * `rg -n 'filtration|first.?seen|arrival|freezeEvent|frozenAt|decisionEvent|
     decidedAt' D5/S3/ConceptDynamics` found no reusable filtration or
     adjudication snapshot outside the previous version of this module.
   * `rg -n -i 'commitment|pledge|seal|regrade|reassess|evaluate|verdict|launder|
     bleach|whitewash|retroactive|protected|guarded|coordinate'
     D5/S3/ConceptDynamics` found only neighboring transport, provenance, and
     coordinate results; none combines the canonical field family below.
   * `ls D5/S3/ConceptDynamics` and `git grep -n '^def \|^  def ' --
     D5/S3/ConceptDynamics | head -60` surveyed the domain vocabulary. The two
     neighboring Governance modules contain theorem-only criteria and no carrier.
   * The exact-name search after merge hits only this lane's pre-existing file;
     the source-sketch signatures occur at DECT 4645, 4686,
     4798, 4804, 4872, 4882, 4899, and 4910. No frozen-ledger selector names
     this module.
   * Source closure: DECT 3611-3631 defines first access from the ledger; 3755-3809
     defines commitments, arrival as `FirstSeen`, and its strict timing law;
     3983-4029 gives the boxed temporal target-laundering criterion; 4623-4932
     supplies the canonical Lean sketches. Prose 3994 compares `Arrival Z` with
     `Time K'`, while sketch 4927 instead tests freeze-event visibility. Snapshot
     fields 4689-4695 keep EventId and Time independent and state no bridge.
     The exact-bridge theorem below records when the predicates agree; the named
     simultaneous-arrival witness proves that first-seen derivation plus a
     monotone event clock still does not imply their equivalence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

/-- The canonical versioned evidence filtration from the source sketch. -/
structure EvidenceFiltration
    (EventId Evidence : Type u) [Preorder EventId] where
  seen : EventId -> Set Evidence
  monotone : forall {i j}, i <= j -> seen i <= seen j

/-- The canonical adjudication snapshot keeps event and clock coordinates distinct. -/
structure AdjudicationSnapshot
    (EventId Evidence Round Artifact Time : Type u)
    [Preorder EventId] [Preorder Time] (n : Round) where
  freezeEvent : EventId
  decisionEvent : EventId
  frozenAt : Time
  decidedAt : Time
  freezeBeforeDecision : freezeEvent <= decisionEvent
  timeBeforeDecision : frozenAt <= decidedAt
  filtration : EvidenceFiltration EventId Evidence
  dependencyClosure : Set Artifact
  evidenceDependencies : Set Evidence

/-- The candidate and feasible actions sealed into a prospective commitment. -/
structure DecisionSet (Action : Type u) [DecidableEq Action] where
  candidates : Finset Action
  feasible : Finset Action
  current : Option Action
  feasibleFromCandidates : feasible <= candidates

/-- The canonical same-round prospective commitment from the source sketch. -/
structure ProspectiveCommitment
    (EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u)
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    (n : Round) where
  adjudication : AdjudicationSnapshot EventId Evidence Round Artifact Time n
  targetChain : TargetChain
  domain : Domain
  epsilon : Epsilon
  conditions : Condition
  comparator : Comparator
  testPlan : TestPlan
  baseline : Baseline
  weightSpec : WeightSpec
  decision : DecisionSet Artifact
  committedArtifacts : Finset Artifact
  baselineArtifacts : Finset Artifact
  committedFromCandidates : committedArtifacts <= decision.candidates
  baselinesFromCandidates : baselineArtifacts <= decision.candidates
  committedInClosure : forall a, a ∈ committedArtifacts ->
    a ∈ adjudication.dependencyClosure

/-- Exactly the seven source-protected coordinates. -/
structure ProtectedCoordinates
    (TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec : Type u) where
  targetChain : TargetChain
  domain : Domain
  epsilon : Epsilon
  conditions : Condition
  comparator : Comparator
  baseline : Baseline
  weightSpec : WeightSpec

/-- Direct projection of all protected coordinates from a commitment. -/
def protectedCoordinates
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (K : ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
      Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n) :
    ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator
      Baseline WeightSpec :=
  { targetChain := K.targetChain
    domain := K.domain
    epsilon := K.epsilon
    conditions := K.conditions
    comparator := K.comparator
    baseline := K.baseline
    weightSpec := K.weightSpec }

/-- A regrade report carries the actual revised evaluation as a typed field. -/
structure RegradeReport
    (Commitment Evidence Verdict Time : Type u)
    (evaluate : Commitment -> Evidence -> Verdict) where
  original : Commitment
  revised : Commitment
  evidence : Evidence
  regradedVerdict : Verdict
  regradesOldRound : regradedVerdict = evaluate revised evidence
  attributedTo : Commitment
  occurredAt : Time

/-- The later source sketch's freeze-visible formulation, retained under an
explicit name because it is not equivalent to the boxed prose definition. -/
def SketchTargetLaundering
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Verdict : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (evaluate :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n ->
        Evidence -> Verdict)
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence)
    (report : RegradeReport
      (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
      Evidence Verdict Time evaluate) : Prop :=
  Z ∈ newK.adjudication.filtration.seen newK.adjudication.freezeEvent ∧
    protectedCoordinates newK ≠ protectedCoordinates oldK ∧
    report.original = oldK ∧ report.revised = newK ∧
    report.evidence = Z ∧ report.regradedVerdict = evaluate newK Z ∧
    report.attributedTo = oldK ∧
    report.occurredAt = newK.adjudication.frozenAt

/-- The prose-level post-arrival predicate compares two `Time` values. -/
def PostArrivalProtectedChange
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (arrival : Evidence -> Time)
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence) : Prop :=
  arrival Z < newK.adjudication.frozenAt ∧
    protectedCoordinates newK ≠ protectedCoordinates oldK

/-- The freeze-visibility pair used by the later source sketch. -/
def FreezeVisibleProtectedChange
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence) : Prop :=
  Z ∈ newK.adjudication.filtration.seen newK.adjudication.freezeEvent ∧
    protectedCoordinates newK ≠ protectedCoordinates oldK

/-- Report identities saying that old evidence was evaluated in the revised
same-round commitment. The boxed source clause imposes no report timestamp. -/
def RegradesOldRound
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Verdict : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (evaluate :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n ->
        Evidence -> Verdict)
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence)
    (report : RegradeReport
      (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
      Evidence Verdict Time evaluate) : Prop :=
  report.original = oldK ∧ report.revised = newK ∧ report.evidence = Z

/-- A success report pairs the reported verdict with its attributed commitment. -/
def ReportedAsSuccess
    {Commitment Evidence Verdict Time : Type u}
    {evaluate : Commitment -> Evidence -> Verdict}
    (verdict : Verdict) (commitment : Commitment)
    (report : RegradeReport Commitment Evidence Verdict Time evaluate) : Prop :=
  report.regradedVerdict = verdict ∧ report.attributedTo = commitment

/-- Attribution applies the actual revised evaluator to the old evidence. -/
def AttributesToOriginalCommitment
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Verdict : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (evaluate :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n ->
        Evidence -> Verdict)
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence)
    (report : RegradeReport
      (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
      Evidence Verdict Time evaluate) : Prop :=
  ReportedAsSuccess (evaluate newK Z) oldK report

/-- The boxed prose definition: strict post-arrival change, old-round regrading,
and attribution of the revised evaluation to the original commitment. -/
def TargetLaundering
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Verdict : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (arrival : Evidence -> Time)
    (evaluate :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n ->
        Evidence -> Verdict)
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence)
    (report : RegradeReport
      (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
      Evidence Verdict Time evaluate) : Prop :=
  PostArrivalProtectedChange arrival oldK newK Z ∧
    RegradesOldRound evaluate oldK newK Z report ∧
    AttributesToOriginalCommitment evaluate oldK newK Z report

/-- Directly consumes the proof field indexed by the actual evaluator. -/
theorem regrade_report_carries_actual_evaluation
    {Commitment Evidence Verdict Time : Type u}
    {evaluate : Commitment -> Evidence -> Verdict}
    (report : RegradeReport Commitment Evidence Verdict Time evaluate) :
    report.regradedVerdict = evaluate report.revised report.evidence :=
  report.regradesOldRound

/-- The source-sketch fields expose freeze visibility and its extra timestamp. -/
theorem target_laundering_sketch_criterion
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Verdict : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (evaluate :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n ->
        Evidence -> Verdict)
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence)
    (report : RegradeReport
      (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
      Evidence Verdict Time evaluate) :
    SketchTargetLaundering evaluate oldK newK Z report <->
      FreezeVisibleProtectedChange oldK newK Z ∧
        RegradesOldRound evaluate oldK newK Z report ∧
        AttributesToOriginalCommitment evaluate oldK newK Z report ∧
        report.occurredAt = newK.adjudication.frozenAt := by
  constructor
  · rintro ⟨visible, changed, original, revised, evidence, verdict, attributed, occurred⟩
    exact ⟨⟨visible, changed⟩, ⟨original, revised, evidence⟩,
      ⟨verdict, attributed⟩, occurred⟩
  · rintro ⟨⟨visible, changed⟩, ⟨original, revised, evidence⟩,
      ⟨verdict, attributed⟩, occurred⟩
    exact ⟨visible, changed, original, revised, evidence, verdict, attributed, occurred⟩

/-- The boxed prose criterion uses strict Time-valued arrival, with no extra bridge
or specialization of the source parameters. -/
theorem target_laundering_criterion
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Verdict : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (arrival : Evidence -> Time)
    (evaluate :
      ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n ->
        Evidence -> Verdict)
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence)
    (report : RegradeReport
      (ProspectiveCommitment EventId Evidence Round Artifact Time TargetChain
        Domain Epsilon Condition Comparator TestPlan Baseline WeightSpec n)
      Evidence Verdict Time evaluate) :
    TargetLaundering arrival evaluate oldK newK Z report <->
      (PostArrivalProtectedChange arrival oldK newK Z ∧
      RegradesOldRound evaluate oldK newK Z report ∧
        AttributesToOriginalCommitment evaluate oldK newK Z report) :=
  Iff.rfl

/-- The prose and sketch protected-change clauses agree exactly when their two
arrival tests are related by an explicit bridge. -/
theorem freeze_visible_iff_post_arrival_under_exact_bridge
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (arrival : Evidence -> Time)
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence)
    (bridge :
      (Z ∈ newK.adjudication.filtration.seen newK.adjudication.freezeEvent) <->
        arrival Z < newK.adjudication.frozenAt) :
    FreezeVisibleProtectedChange oldK newK Z <->
      PostArrivalProtectedChange arrival oldK newK Z := by
  exact and_congr bridge Iff.rfl

/-- The temporal post-arrival definition unfolds without identifying event and clock types. -/
theorem post_arrival_protected_change_criterion
    {EventId Evidence Round Artifact Time TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec : Type u}
    [LinearOrder EventId] [Preorder Time] [DecidableEq Artifact]
    {n : Round}
    (arrival : Evidence -> Time)
    (oldK newK : ProspectiveCommitment EventId Evidence Round Artifact Time
      TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec n)
    (Z : Evidence) :
    PostArrivalProtectedChange arrival oldK newK Z <->
      arrival Z < newK.adjudication.frozenAt ∧
        protectedCoordinates newK ≠ protectedCoordinates oldK :=
  Iff.rfl

namespace FiniteWitness

abbrev EventId := Fin 2
abbrev Evidence := Bool
abbrev Round := Bool
abbrev Artifact := Bool
abbrev Time := Fin 3
abbrev RoundIndex : Round := false

abbrev Commitment :=
  ProspectiveCommitment EventId Evidence Round Artifact Time Unit Unit Unit Bool
    Unit Unit Unit Unit RoundIndex

def seenFiltration : EvidenceFiltration EventId Evidence where
  seen := fun _ => Set.univ
  monotone := by
    intro i j hij evidence evidenceSeen
    exact evidenceSeen

def unseenFiltration : EvidenceFiltration EventId Evidence where
  seen := fun _ => ∅
  monotone := by
    intro i j hij evidence evidenceSeen
    exact evidenceSeen

def seenSnapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time RoundIndex where
  freezeEvent := 1
  decisionEvent := 1
  frozenAt := 1
  decidedAt := 2
  freezeBeforeDecision := le_rfl
  timeBeforeDecision := by decide
  filtration := seenFiltration
  dependencyClosure := Set.univ
  evidenceDependencies := ∅

def unseenSnapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time RoundIndex where
  freezeEvent := 1
  decisionEvent := 1
  frozenAt := 1
  decidedAt := 2
  freezeBeforeDecision := le_rfl
  timeBeforeDecision := by decide
  filtration := unseenFiltration
  dependencyClosure := Set.univ
  evidenceDependencies := ∅

def decision : DecisionSet Artifact where
  candidates := {false}
  feasible := {false}
  current := some false
  feasibleFromCandidates := by simp

def commitment
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time RoundIndex)
    (condition : Bool) : Commitment where
  adjudication := snapshot
  targetChain := ()
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

def oldK : Commitment := commitment seenSnapshot false
def newK : Commitment := commitment seenSnapshot true
def unseenNewK : Commitment := commitment unseenSnapshot true
def unchangedK : Commitment := commitment seenSnapshot false

def evaluate : Commitment -> Evidence -> Bool := fun _ evidence => evidence

def validReport : RegradeReport Commitment Evidence Bool Time evaluate where
  original := oldK
  revised := newK
  evidence := true
  regradedVerdict := true
  regradesOldRound := rfl
  attributedTo := oldK
  occurredAt := newK.adjudication.frozenAt

def unseenReport : RegradeReport Commitment Evidence Bool Time evaluate where
  original := oldK
  revised := unseenNewK
  evidence := true
  regradedVerdict := true
  regradesOldRound := rfl
  attributedTo := oldK
  occurredAt := unseenNewK.adjudication.frozenAt

def wrongRoundReport : RegradeReport Commitment Evidence Bool Time evaluate where
  original := newK
  revised := newK
  evidence := true
  regradedVerdict := true
  regradesOldRound := rfl
  attributedTo := oldK
  occurredAt := newK.adjudication.frozenAt

def wrongAttributionReport : RegradeReport Commitment Evidence Bool Time evaluate where
  original := oldK
  revised := newK
  evidence := true
  regradedVerdict := true
  regradesOldRound := rfl
  attributedTo := newK
  occurredAt := newK.adjudication.frozenAt

def lateTimestampReport : RegradeReport Commitment Evidence Bool Time evaluate where
  original := oldK
  revised := newK
  evidence := true
  regradedVerdict := true
  regradesOldRound := rfl
  attributedTo := oldK
  occurredAt := 2

def arrival : Evidence -> Time := fun evidence => if evidence then 0 else 2
def lateArrival : Evidence -> Time := fun _ => 2

/-- The event clock embeds the two event indices into the first two clock ticks. -/
def eventTime (event : EventId) : Time :=
  ⟨event.val, lt_trans event.isLt (by decide)⟩

theorem eventTime_monotone : Monotone eventTime := by
  intro i j hij
  simpa [eventTime] using hij

/-- `true` first becomes visible at event one; `false` is never visible. -/
def simultaneousFiltration : EvidenceFiltration EventId Evidence where
  seen := fun event => {evidence | evidence = true ∧ (1 : EventId) ≤ event}
  monotone := by
    intro i j hij evidence evidenceSeen
    exact ⟨evidenceSeen.1, le_trans evidenceSeen.2 hij⟩

def simultaneousSnapshot :
    AdjudicationSnapshot EventId Evidence Round Artifact Time RoundIndex where
  freezeEvent := 1
  decisionEvent := 1
  frozenAt := eventTime 1
  decidedAt := 2
  freezeBeforeDecision := le_rfl
  timeBeforeDecision := by decide
  filtration := simultaneousFiltration
  dependencyClosure := Set.univ
  evidenceDependencies := ∅

def simultaneousNewK : Commitment := commitment simultaneousSnapshot true

/-- The source convention sends an unseen record to the terminal clock value. -/
def firstSeenArrival : Evidence -> Time := fun evidence => if evidence then eventTime 1 else 2

/-- `firstSeenArrival true` is derived from the filtration: event one contains the
record and is below every event that contains it. -/
theorem first_seen_true_source_model :
    firstSeenArrival true = eventTime 1 ∧
      true ∈ simultaneousFiltration.seen (1 : EventId) ∧
      ∀ event, true ∈ simultaneousFiltration.seen event -> (1 : EventId) ≤ event := by
  simp [firstSeenArrival, simultaneousFiltration]

/-- The commitment clock is the monotone image of its freeze event. -/
theorem simultaneous_freeze_clock_link :
    simultaneousNewK.adjudication.frozenAt =
      eventTime simultaneousNewK.adjudication.freezeEvent := by
  rfl

theorem oldK_ne_newK : oldK ≠ newK := by
  intro commitmentsEqual
  have conditionsEqual := congrArg (fun K : Commitment => K.conditions) commitmentsEqual
  simp [oldK, newK, commitment] at conditionsEqual

theorem protected_coordinates_changed :
    protectedCoordinates newK ≠ protectedCoordinates oldK := by
  intro coordinatesEqual
  have conditionsEqual := congrArg
    (fun coordinates : ProtectedCoordinates Unit Unit Unit Bool Unit Unit Unit =>
      coordinates.conditions)
    coordinatesEqual
  simp [protectedCoordinates, oldK, newK, commitment] at conditionsEqual

theorem simultaneous_protected_coordinates_changed :
    protectedCoordinates simultaneousNewK ≠ protectedCoordinates oldK := by
  intro coordinatesEqual
  have conditionsEqual := congrArg
    (fun coordinates : ProtectedCoordinates Unit Unit Unit Bool Unit Unit Unit =>
      coordinates.conditions)
    coordinatesEqual
  simp [protectedCoordinates, simultaneousNewK, oldK, commitment] at conditionsEqual

end FiniteWitness

/-- Positive control: the boxed criterion holds although old and new evaluations agree. -/
theorem same_verdict_target_laundering :
    TargetLaundering FiniteWitness.arrival FiniteWitness.evaluate
      FiniteWitness.oldK FiniteWitness.newK true FiniteWitness.validReport ∧
      FiniteWitness.evaluate FiniteWitness.oldK true =
        FiniteWitness.evaluate FiniteWitness.newK true := by
  constructor
  · apply (target_laundering_criterion FiniteWitness.arrival FiniteWitness.evaluate
      FiniteWitness.oldK FiniteWitness.newK true FiniteWitness.validReport).2
    exact ⟨⟨by decide, FiniteWitness.protected_coordinates_changed⟩,
      ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · rfl

/-- The boxed criterion does not require the report timestamp to equal freeze time. -/
theorem report_timestamp_not_required_by_boxed_criterion :
    TargetLaundering FiniteWitness.arrival FiniteWitness.evaluate
      FiniteWitness.oldK FiniteWitness.newK true FiniteWitness.lateTimestampReport ∧
      FiniteWitness.lateTimestampReport.occurredAt ≠
        FiniteWitness.newK.adjudication.frozenAt := by
  constructor
  · apply (target_laundering_criterion FiniteWitness.arrival FiniteWitness.evaluate
      FiniteWitness.oldK FiniteWitness.newK true FiniteWitness.lateTimestampReport).2
    exact ⟨⟨by decide, FiniteWitness.protected_coordinates_changed⟩,
      ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · decide

/-- False-side control for the canonical freeze-visible protected-change clause. -/
theorem false_neighbor_no_freeze_visible_change :
    (¬FreezeVisibleProtectedChange FiniteWitness.oldK FiniteWitness.unseenNewK true) ∧
      RegradesOldRound FiniteWitness.evaluate FiniteWitness.oldK
        FiniteWitness.unseenNewK true FiniteWitness.unseenReport ∧
      AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.oldK
        FiniteWitness.unseenNewK true FiniteWitness.unseenReport ∧
      ¬SketchTargetLaundering FiniteWitness.evaluate FiniteWitness.oldK
        FiniteWitness.unseenNewK true FiniteWitness.unseenReport := by
  have noVisible :
      ¬FreezeVisibleProtectedChange FiniteWitness.oldK FiniteWitness.unseenNewK true := by
    simp [FreezeVisibleProtectedChange, FiniteWitness.unseenNewK,
      FiniteWitness.commitment, FiniteWitness.unseenSnapshot,
      FiniteWitness.unseenFiltration]
  refine ⟨noVisible, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
  intro laundering
  exact noVisible ((target_laundering_sketch_criterion FiniteWitness.evaluate
    FiniteWitness.oldK
    FiniteWitness.unseenNewK true FiniteWitness.unseenReport).1 laundering).1

/-- False-side control for old-round report identity. -/
theorem false_neighbor_no_old_round_regrade :
    PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
        FiniteWitness.newK true ∧
      (¬RegradesOldRound FiniteWitness.evaluate FiniteWitness.oldK FiniteWitness.newK
        true FiniteWitness.wrongRoundReport) ∧
      AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.oldK
        FiniteWitness.newK true FiniteWitness.wrongRoundReport ∧
      ¬(PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
          FiniteWitness.newK true ∧
        RegradesOldRound FiniteWitness.evaluate FiniteWitness.oldK FiniteWitness.newK
          true FiniteWitness.wrongRoundReport ∧
        AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.oldK
          FiniteWitness.newK true FiniteWitness.wrongRoundReport) := by
  have postArrival :
      PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
        FiniteWitness.newK true :=
    ⟨by decide, FiniteWitness.protected_coordinates_changed⟩
  have noRegrade :
      ¬RegradesOldRound FiniteWitness.evaluate FiniteWitness.oldK FiniteWitness.newK
        true FiniteWitness.wrongRoundReport := by
    intro regrade
    exact FiniteWitness.oldK_ne_newK regrade.1.symm
  exact ⟨postArrival, noRegrade, ⟨rfl, rfl⟩, fun criterion => noRegrade criterion.2.1⟩

/-- False-side control for attribution to the original commitment. -/
theorem false_neighbor_no_original_attribution :
    PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
        FiniteWitness.newK true ∧
      RegradesOldRound FiniteWitness.evaluate FiniteWitness.oldK FiniteWitness.newK
        true FiniteWitness.wrongAttributionReport ∧
      (¬AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.oldK
        FiniteWitness.newK true FiniteWitness.wrongAttributionReport) ∧
      ¬(PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
          FiniteWitness.newK true ∧
        RegradesOldRound FiniteWitness.evaluate FiniteWitness.oldK FiniteWitness.newK
          true FiniteWitness.wrongAttributionReport ∧
        AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.oldK
          FiniteWitness.newK true FiniteWitness.wrongAttributionReport) := by
  have postArrival :
      PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
        FiniteWitness.newK true :=
    ⟨by decide, FiniteWitness.protected_coordinates_changed⟩
  have noAttribution :
      ¬AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.oldK
        FiniteWitness.newK true FiniteWitness.wrongAttributionReport := by
    intro attribution
    exact FiniteWitness.oldK_ne_newK attribution.2.symm
  exact ⟨postArrival, ⟨rfl, rfl, rfl⟩, noAttribution,
    fun criterion => noAttribution criterion.2.2⟩

/-- Positive control for the independent Time-valued arrival predicate. -/
theorem temporal_post_arrival_change :
    PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
      FiniteWitness.newK true := by
  apply (post_arrival_protected_change_criterion FiniteWitness.arrival
    FiniteWitness.oldK FiniteWitness.newK true).2
  exact ⟨by decide, FiniteWitness.protected_coordinates_changed⟩

/-- Temporal false-side control: coordinates change, but arrival is not before freeze. -/
theorem false_neighbor_arrival_not_before :
    (¬PostArrivalProtectedChange FiniteWitness.lateArrival FiniteWitness.oldK
      FiniteWitness.newK true) ∧
      protectedCoordinates FiniteWitness.newK ≠
        protectedCoordinates FiniteWitness.oldK ∧
      RegradesOldRound FiniteWitness.evaluate FiniteWitness.oldK FiniteWitness.newK
        true FiniteWitness.validReport ∧
      AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.oldK
        FiniteWitness.newK true FiniteWitness.validReport ∧
      ¬(PostArrivalProtectedChange FiniteWitness.lateArrival FiniteWitness.oldK
          FiniteWitness.newK true ∧
        RegradesOldRound FiniteWitness.evaluate FiniteWitness.oldK FiniteWitness.newK
          true FiniteWitness.validReport ∧
        AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.oldK
          FiniteWitness.newK true FiniteWitness.validReport) := by
  have noPostArrival :
      ¬PostArrivalProtectedChange FiniteWitness.lateArrival FiniteWitness.oldK
        FiniteWitness.newK true := by
    intro postArrival
    have before := ((post_arrival_protected_change_criterion FiniteWitness.lateArrival
      FiniteWitness.oldK FiniteWitness.newK true).1 postArrival).1
    simp [FiniteWitness.lateArrival, FiniteWitness.newK, FiniteWitness.commitment,
      FiniteWitness.seenSnapshot] at before
  exact ⟨noPostArrival, FiniteWitness.protected_coordinates_changed,
    ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩,
    fun criterion => noPostArrival criterion.1⟩

/-- Coordinate false-side control: arrival is before freeze, but no coordinate changed. -/
theorem false_neighbor_protected_coordinates_unchanged :
    FiniteWitness.arrival true < FiniteWitness.unchangedK.adjudication.frozenAt ∧
      ¬PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
        FiniteWitness.unchangedK true := by
  refine ⟨by decide, ?_⟩
  intro postArrival
  have changed := ((post_arrival_protected_change_criterion FiniteWitness.arrival
    FiniteWitness.oldK FiniteWitness.unchangedK true).1 postArrival).2
  apply changed
  rfl

/-- Source-tension witness: even with filtration-derived first arrival, a monotone
event clock, and an exact freeze-event/clock link, arrival exactly at the freeze
event satisfies sketch visibility but not the prose's strict inequality. -/
theorem simultaneous_arrival_separates_source_formulations :
    Monotone FiniteWitness.eventTime ∧
      (FiniteWitness.firstSeenArrival true = FiniteWitness.eventTime 1 ∧
        true ∈ FiniteWitness.simultaneousFiltration.seen (1 : FiniteWitness.EventId) ∧
        ∀ event, true ∈ FiniteWitness.simultaneousFiltration.seen event ->
          (1 : FiniteWitness.EventId) ≤ event) ∧
      FiniteWitness.simultaneousNewK.adjudication.frozenAt =
        FiniteWitness.eventTime
          FiniteWitness.simultaneousNewK.adjudication.freezeEvent ∧
      FreezeVisibleProtectedChange FiniteWitness.oldK
        FiniteWitness.simultaneousNewK true ∧
      ¬PostArrivalProtectedChange FiniteWitness.firstSeenArrival FiniteWitness.oldK
        FiniteWitness.simultaneousNewK true := by
  refine ⟨FiniteWitness.eventTime_monotone,
    FiniteWitness.first_seen_true_source_model,
    FiniteWitness.simultaneous_freeze_clock_link, ?_, ?_⟩
  · exact ⟨by simp [FiniteWitness.simultaneousNewK, FiniteWitness.commitment,
      FiniteWitness.simultaneousSnapshot, FiniteWitness.simultaneousFiltration],
      FiniteWitness.simultaneous_protected_coordinates_changed⟩
  · intro postArrival
    have before := ((post_arrival_protected_change_criterion
      FiniteWitness.firstSeenArrival FiniteWitness.oldK
      FiniteWitness.simultaneousNewK true).1 postArrival).1
    simp [FiniteWitness.firstSeenArrival, FiniteWitness.simultaneousNewK,
      FiniteWitness.commitment, FiniteWitness.simultaneousSnapshot] at before

/-- Fail-closed consumer for every named positive and false-side witness. -/
theorem target_laundering_nondegeneracy :
    (PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
        FiniteWitness.newK true ∧
      RegradesOldRound FiniteWitness.evaluate FiniteWitness.oldK FiniteWitness.newK
        true FiniteWitness.validReport ∧
      AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.oldK
        FiniteWitness.newK true FiniteWitness.validReport) ∧
    (TargetLaundering FiniteWitness.arrival FiniteWitness.evaluate
      FiniteWitness.oldK FiniteWitness.newK true FiniteWitness.lateTimestampReport ∧
      FiniteWitness.lateTimestampReport.occurredAt ≠
        FiniteWitness.newK.adjudication.frozenAt) ∧
    (¬FreezeVisibleProtectedChange FiniteWitness.oldK FiniteWitness.unseenNewK true) ∧
    (¬RegradesOldRound FiniteWitness.evaluate FiniteWitness.oldK FiniteWitness.newK
      true FiniteWitness.wrongRoundReport) ∧
    (¬AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.oldK
      FiniteWitness.newK true FiniteWitness.wrongAttributionReport) ∧
    PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
      FiniteWitness.newK true ∧
    (¬PostArrivalProtectedChange FiniteWitness.lateArrival FiniteWitness.oldK
      FiniteWitness.newK true) ∧
    (¬PostArrivalProtectedChange FiniteWitness.arrival FiniteWitness.oldK
      FiniteWitness.unchangedK true) ∧
    (Monotone FiniteWitness.eventTime ∧
      (FiniteWitness.firstSeenArrival true = FiniteWitness.eventTime 1 ∧
        true ∈ FiniteWitness.simultaneousFiltration.seen (1 : FiniteWitness.EventId) ∧
        ∀ event, true ∈ FiniteWitness.simultaneousFiltration.seen event ->
          (1 : FiniteWitness.EventId) ≤ event) ∧
      FiniteWitness.simultaneousNewK.adjudication.frozenAt =
        FiniteWitness.eventTime
          FiniteWitness.simultaneousNewK.adjudication.freezeEvent ∧
      FreezeVisibleProtectedChange FiniteWitness.oldK
        FiniteWitness.simultaneousNewK true ∧
      ¬PostArrivalProtectedChange FiniteWitness.firstSeenArrival FiniteWitness.oldK
        FiniteWitness.simultaneousNewK true) ∧
    FiniteWitness.validReport.regradedVerdict =
      FiniteWitness.evaluate FiniteWitness.validReport.revised
        FiniteWitness.validReport.evidence := by
  exact ⟨same_verdict_target_laundering.1,
    report_timestamp_not_required_by_boxed_criterion,
    false_neighbor_no_freeze_visible_change.1,
    false_neighbor_no_old_round_regrade.2.1,
    false_neighbor_no_original_attribution.2.2.1,
    temporal_post_arrival_change,
    false_neighbor_arrival_not_before.1,
    false_neighbor_protected_coordinates_unchanged.2,
    simultaneous_arrival_separates_source_formulations,
    regrade_report_carries_actual_evaluation FiniteWitness.validReport⟩

#print axioms target_laundering_criterion
#print axioms target_laundering_sketch_criterion
#print axioms freeze_visible_iff_post_arrival_under_exact_bridge
#print axioms post_arrival_protected_change_criterion
#print axioms simultaneous_arrival_separates_source_formulations
#print axioms regrade_report_carries_actual_evaluation
#print axioms report_timestamp_not_required_by_boxed_criterion
#print axioms target_laundering_nondegeneracy

end D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion
