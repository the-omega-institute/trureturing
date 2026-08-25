/- GID: D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Role admission over independent event, evidence, and artifact carriers. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation

/- Library-search audit trail (2026-08-25):
   * `rg -n 'Set \([A-Za-z]+ x [A-Za-z]+\)|Relation\.ReflTransGen|'\
       'structure EvidenceFiltration|def Contam|def .*Closure' \
       D5/S3/ConceptDynamics --glob '*.lean' | head -220`
     found the existing `Contam` and incoming dependency-closure declarations in
     this lane, plus unrelated pair relations; no second evidence-role ledger or
     equivalent admission predicate exists.
   * `rg -n -i 'incoming|outgoing|predecessor|ancestor|dependency closure|'\
       'joint|common|shared|indexed|family|union|intersection|kernel|readout' \
       D5/S3/ConceptDynamics/Provenance --glob '*.lean' | head -40`
     found finite proof-path semantics but no reusable access filtration. The
     outgoing name `Contam` is retained, and the incoming closure keeps its
     opposite `artifact -> commitment root` reachability direction.
   * `git grep -n -E \
       '^def |^  def |^structure |^inductive |^abbrev |^theorem ' -- \
       D5/S3/ConceptDynamics/Provenance | head -120`
     found only `FiniteProofGraphSourceSemantics` beside the two lane modules;
     its finite paths do not carry role events, freeze snapshots, or filtrations.
   * `rg -n 'EvidenceRole|UseEvent|EvidenceFiltration|AdjudicationSnapshot|'\
       'ValidTrace|AdmissibleJudge' \
       docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md`
     found the source definitions at lines 3635-3717 and the independent-carrier
     Lean sketch at lines 4632-4761. It separately types EventId, Evidence, and
     Artifact and reads `seen`, `evidenceDependencies`, and artifact dependencies.
   * `grep -rl \
       'RoleAdmissionContaminationClosure\|SeenDirectionAndAppendCounterexample' \
       Golden/Frozen/accepted/*.json`
     returned no paths, so both lane modules are outside the accepted freeze set.
   * `rg -n 'event\.evidence .* seen|evidence .* seen' \
       docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md`
     found lines 3661 and 4714 for `ValidTrace`; these are membership reads from
     the already-directed filtration, not independent choices of edge direction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure

universe u

inductive EvidenceRole where
  | generate
  | tune
  | select
  | adjudicate
  | replicate
  deriving DecidableEq, Repr

def adaptiveRoles : Set EvidenceRole :=
  {.generate, .tune, .select}

/-- The outgoing contamination closure from a set of records. -/
def Contam {Artifact : Type u}
    (dependsOn : Artifact -> Artifact -> Prop) (records : Set Artifact) : Set Artifact :=
  {artifact | exists record, record ∈ records /\
    Relation.ReflTransGen dependsOn record artifact}

structure EvidenceFiltration
    (EventId Evidence : Type u) [Preorder EventId] where
  seen : EventId -> Set Evidence
  monotone : forall {i j}, i <= j -> seen i ⊆ seen j

theorem EvidenceFiltration.seen_mono
    {EventId Evidence : Type u} [Preorder EventId]
    (filtration : EvidenceFiltration EventId Evidence) {i j : EventId} (hij : i <= j) :
    filtration.seen i ⊆ filtration.seen j :=
  filtration.monotone hij

structure UseEvent
    (EventId Evidence Round Artifact Protocol Time : Type u) where
  eventId : EventId
  evidence : Evidence
  round : Round
  role : EvidenceRole
  dependencies : Set Artifact
  protocol : Protocol
  usedAt : Time

structure RoleLedger
    (EventId Evidence Round Artifact Protocol Time : Type u)
    [LinearOrder EventId] [Preorder Round] [Preorder Time] where
  events : List (UseEvent EventId Evidence Round Artifact Protocol Time)
  uniqueEventIds : (events.map fun event => event.eventId).Nodup
  strictEventOrder : events.Pairwise (fun event later => event.eventId < later.eventId)
  indexRespectsRound : forall {event later}, event ∈ events -> later ∈ events ->
    event.eventId <= later.eventId -> event.round <= later.round
  indexRespectsTime : forall {event later}, event ∈ events -> later ∈ events ->
    event.eventId <= later.eventId -> event.usedAt <= later.usedAt

def RolePrefixAtEvent
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (cutoff : EventId) :
    Set (UseEvent EventId Evidence Round Artifact Protocol Time) :=
  {event | event ∈ ledger.events /\ event.eventId <= cutoff}

def RolePrefixAtRound
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (round : Round) :
    Set (UseEvent EventId Evidence Round Artifact Protocol Time) :=
  {event | event ∈ ledger.events /\ event.round <= round}

def RolePrefixAtTime
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (cutoff : Time) :
    Set (UseEvent EventId Evidence Round Artifact Protocol Time) :=
  {event | event ∈ ledger.events /\ event.usedAt <= cutoff}

structure AdjudicationSnapshot
    (EventId Evidence Round Artifact Time : Type u)
    [LinearOrder EventId] [Preorder Time] (round : Round) where
  freezeEvent : EventId
  decisionEvent : EventId
  frozenAt : Time
  decidedAt : Time
  freezeBeforeDecision : freezeEvent <= decisionEvent
  timeBeforeDecision : frozenAt <= decidedAt
  filtration : EvidenceFiltration EventId Evidence
  artifactDependsOn : Artifact -> Artifact -> Prop
  commitmentRoots : Set Artifact
  evidenceDependsOn : Evidence -> Evidence -> Prop
  evidenceDependencies : Set Evidence
  commitmentClosureVisibleAtFreeze :
    evidenceDependencies ⊆ filtration.seen freezeEvent

/-- The incoming artifact closure: an artifact belongs when it reaches a root. -/
def AdjudicationSnapshot.dependencyClosure
    {EventId Evidence Round Artifact Time : Type u}
    [LinearOrder EventId] [Preorder Time] {round : Round}
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round) :
    Set Artifact :=
  {artifact | exists commitment, commitment ∈ snapshot.commitmentRoots /\
    Relation.ReflTransGen snapshot.artifactDependsOn artifact commitment}

def AppendOnlyExtension
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (oldLedger newLedger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round) : Prop :=
  exists tail, newLedger.events = oldLedger.events ++ tail /\
    forall event, event ∈ tail -> snapshot.decisionEvent < event.eventId

def ValidTrace
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round) : Prop :=
  forall event, event ∈ ledger.events ->
    event.evidence ∈ snapshot.filtration.seen event.eventId

def InAdjudicationPrefix
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (_validTrace : ValidTrace ledger snapshot)
    (event : UseEvent EventId Evidence Round Artifact Protocol Time) : Prop :=
  event ∈ RolePrefixAtEvent ledger snapshot.decisionEvent /\
    event ∈ RolePrefixAtRound ledger round /\
    event ∈ RolePrefixAtTime ledger snapshot.decidedAt

def RolesAt
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validTrace : ValidTrace ledger snapshot) (evidence : Evidence) : Set EvidenceRole :=
  {role | exists event, InAdjudicationPrefix ledger snapshot validTrace event /\
    event.evidence = evidence /\ event.round = round /\ event.role = role}

def AdaptiveUseInClosure
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validTrace : ValidTrace ledger snapshot) (evidence : Evidence) : Prop :=
  exists event, InAdjudicationPrefix ledger snapshot validTrace event /\
    event.evidence = evidence /\
    event.role ∈ adaptiveRoles /\
    Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure)

def AdmissibleJudge
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validTrace : ValidTrace ledger snapshot) (evidence : Evidence) : Prop :=
  .adjudicate ∈ RolesAt ledger snapshot validTrace evidence /\
    evidence ∉ snapshot.filtration.seen snapshot.freezeEvent /\
    evidence ∉ snapshot.evidenceDependencies /\
    Not (AdaptiveUseInClosure ledger snapshot validTrace evidence)

def NonAnticipating
    {EventId Evidence Round Artifact Time : Type u}
    [LinearOrder EventId] [Preorder Time] {round : Round}
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (evidence : Evidence) : Prop :=
  evidence ∈ snapshot.filtration.seen snapshot.decisionEvent /\
    evidence ∉ snapshot.filtration.seen snapshot.freezeEvent /\
    evidence ∉ snapshot.evidenceDependencies

def AdjudicationSetClean
    {EventId Evidence Round Artifact Time : Type u}
    [LinearOrder EventId] [Preorder Time] {round : Round}
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (judges : Set Evidence) : Prop :=
  Contam snapshot.evidenceDependsOn judges ∩ snapshot.evidenceDependencies = ∅ /\
    forall judge, judge ∈ judges ->
      judge ∉ snapshot.filtration.seen snapshot.freezeEvent

noncomputable def ReuseDepth
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validTrace : ValidTrace ledger snapshot) (evidence : Evidence) : Nat := by
  classical
  exact (ledger.events.filter fun event =>
    InAdjudicationPrefix ledger snapshot validTrace event /\
      event.evidence = evidence /\
      event.role ∈ adaptiveRoles /\
      Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure)).length

theorem role_admission_contamination_spec
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validTrace : ValidTrace ledger snapshot) :
    (forall evidence,
      AdaptiveUseInClosure ledger snapshot validTrace evidence <->
        exists event, InAdjudicationPrefix ledger snapshot validTrace event /\
          event.evidence = evidence /\
          event.role ∈ adaptiveRoles /\
          Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure)) /\
    (forall evidence,
      AdmissibleJudge ledger snapshot validTrace evidence <->
        .adjudicate ∈ RolesAt ledger snapshot validTrace evidence /\
          evidence ∉ snapshot.filtration.seen snapshot.freezeEvent /\
          evidence ∉ snapshot.evidenceDependencies /\
          Not (AdaptiveUseInClosure ledger snapshot validTrace evidence)) /\
    (forall evidence,
      NonAnticipating snapshot evidence <->
        evidence ∈ snapshot.filtration.seen snapshot.decisionEvent /\
          evidence ∉ snapshot.filtration.seen snapshot.freezeEvent /\
          evidence ∉ snapshot.evidenceDependencies) /\
    ((forall (dependsOn : Evidence -> Evidence -> Prop)
        (records : Set Evidence) (evidence : Evidence),
      evidence ∈ Contam dependsOn records <->
        exists record, record ∈ records /\
          Relation.ReflTransGen dependsOn record evidence) /\
      (forall judges : Set Evidence,
        AdjudicationSetClean snapshot judges <->
          Contam snapshot.evidenceDependsOn judges ∩ snapshot.evidenceDependencies = ∅ /\
          forall judge, judge ∈ judges ->
            judge ∉ snapshot.filtration.seen snapshot.freezeEvent)) /\
    (EvidenceRole.generate ∈ adaptiveRoles /\
      EvidenceRole.tune ∈ adaptiveRoles /\
      EvidenceRole.select ∈ adaptiveRoles /\
      EvidenceRole.adjudicate ∉ adaptiveRoles /\
      EvidenceRole.replicate ∉ adaptiveRoles) /\
    (forall evidence, evidence ∈ snapshot.evidenceDependencies ->
      Not (AdmissibleJudge ledger snapshot validTrace evidence)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro evidence
    rfl
  · intro evidence
    rfl
  · intro evidence
    rfl
  · exact ⟨fun _ _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  · simp [adaptiveRoles, Set.mem_insert_iff, Set.mem_singleton_iff]
  · intro evidence contaminated admitted
    exact admitted.2.2.1 contaminated

private theorem prefix_event_append_iff
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger :
      RoleLedger EventId Evidence Round Artifact Protocol Time}
    {snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round}
    {tail : List (UseEvent EventId Evidence Round Artifact Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : forall event, event ∈ tail -> snapshot.decisionEvent < event.eventId)
    (event : UseEvent EventId Evidence Round Artifact Protocol Time) :
    event ∈ RolePrefixAtEvent extendedLedger snapshot.decisionEvent <->
      event ∈ RolePrefixAtEvent oldLedger snapshot.decisionEvent := by
  constructor
  · rintro ⟨inEvents, beforeCutoff⟩
    rw [extendedEvents] at inEvents
    rcases List.mem_append.mp inEvents with inOld | inTail
    · exact ⟨inOld, beforeCutoff⟩
    · exact False.elim ((not_lt_of_ge beforeCutoff) (late event inTail))
  · rintro ⟨inOld, beforeCutoff⟩
    exact ⟨by rw [extendedEvents]; exact List.mem_append_left tail inOld, beforeCutoff⟩

private theorem in_prefix_append_iff
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger :
      RoleLedger EventId Evidence Round Artifact Protocol Time}
    {snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round}
    {tail : List (UseEvent EventId Evidence Round Artifact Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : forall event, event ∈ tail -> snapshot.decisionEvent < event.eventId)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (event : UseEvent EventId Evidence Round Artifact Protocol Time) :
    InAdjudicationPrefix extendedLedger snapshot validExtended event <->
      InAdjudicationPrefix oldLedger snapshot validOld event := by
  constructor
  · intro inExtended
    have inOld := (prefix_event_append_iff extendedEvents late event).mp inExtended.1
    exact ⟨inOld, ⟨inOld.1, inExtended.2.1.2⟩, ⟨inOld.1, inExtended.2.2.2⟩⟩
  · intro inOld
    have inExtended := (prefix_event_append_iff extendedEvents late event).mpr inOld.1
    exact ⟨inExtended, ⟨inExtended.1, inOld.2.1.2⟩,
      ⟨inExtended.1, inOld.2.2.2⟩⟩

private theorem roles_append_iff
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger :
      RoleLedger EventId Evidence Round Artifact Protocol Time}
    {snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round}
    {tail : List (UseEvent EventId Evidence Round Artifact Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : forall event, event ∈ tail -> snapshot.decisionEvent < event.eventId)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (evidence : Evidence) :
    RolesAt extendedLedger snapshot validExtended evidence =
      RolesAt oldLedger snapshot validOld evidence := by
  ext role
  constructor
  · rintro ⟨event, inExtended, evidenceEq, roundEq, roleEq⟩
    exact ⟨event, (in_prefix_append_iff extendedEvents late validOld validExtended event).mp
      inExtended, evidenceEq, roundEq, roleEq⟩
  · rintro ⟨event, inOld, evidenceEq, roundEq, roleEq⟩
    exact ⟨event, (in_prefix_append_iff extendedEvents late validOld validExtended event).mpr
      inOld, evidenceEq, roundEq, roleEq⟩

private theorem adaptive_append_iff
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger :
      RoleLedger EventId Evidence Round Artifact Protocol Time}
    {snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round}
    {tail : List (UseEvent EventId Evidence Round Artifact Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : forall event, event ∈ tail -> snapshot.decisionEvent < event.eventId)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (evidence : Evidence) :
    AdaptiveUseInClosure extendedLedger snapshot validExtended evidence <->
      AdaptiveUseInClosure oldLedger snapshot validOld evidence := by
  constructor
  · rintro ⟨event, inExtended, evidenceEq, adaptiveRole, touches⟩
    exact ⟨event, (in_prefix_append_iff extendedEvents late validOld validExtended event).mp
      inExtended, evidenceEq, adaptiveRole, touches⟩
  · rintro ⟨event, inOld, evidenceEq, adaptiveRole, touches⟩
    exact ⟨event, (in_prefix_append_iff extendedEvents late validOld validExtended event).mpr
      inOld, evidenceEq, adaptiveRole, touches⟩

theorem admissible_judge_append_invariant
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (oldLedger extendedLedger :
      RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (extension : AppendOnlyExtension oldLedger extendedLedger snapshot) :
    forall evidence,
      AdmissibleJudge extendedLedger snapshot validExtended evidence <->
        AdmissibleJudge oldLedger snapshot validOld evidence := by
  rcases extension with ⟨tail, extendedEvents, late⟩
  have roles := roles_append_iff extendedEvents late validOld validExtended
  have adaptive := adaptive_append_iff extendedEvents late validOld validExtended
  intro evidence
  unfold AdmissibleJudge
  rw [roles evidence, adaptive evidence]

private def witnessFiltration : EvidenceFiltration Nat Bool :=
  { seen := fun cutoff =>
      {evidence | (evidence = true /\ 1 <= cutoff) \/
        (evidence = false /\ 3 <= cutoff)}
    monotone := by
      intro i j hij evidence seen
      rcases seen with seen | seen
      · exact Or.inl ⟨seen.1, seen.2.trans hij⟩
      · exact Or.inr ⟨seen.1, seen.2.trans hij⟩ }

private def witnessGenerateEvent : UseEvent Nat Bool Nat Bool Unit Nat :=
  { eventId := 1, evidence := true, round := 7, role := .generate,
    dependencies := {true}, protocol := (), usedAt := 1 }

private def witnessAdjudicateEvent : UseEvent Nat Bool Nat Bool Unit Nat :=
  { eventId := 3, evidence := false, round := 7, role := .adjudicate,
    dependencies := ∅, protocol := (), usedAt := 2 }

private def witnessLedger : RoleLedger Nat Bool Nat Bool Unit Nat :=
  { events := [witnessGenerateEvent, witnessAdjudicateEvent]
    uniqueEventIds := by simp [witnessGenerateEvent, witnessAdjudicateEvent]
    strictEventOrder := by simp [witnessGenerateEvent, witnessAdjudicateEvent]
    indexRespectsRound := by
      intro event later inEvents inLater _before
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inEvents inLater
      rcases inEvents with rfl | rfl <;> rcases inLater with rfl | rfl <;>
        simp [witnessGenerateEvent, witnessAdjudicateEvent]
    indexRespectsTime := by
      intro event later inEvents inLater before
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inEvents inLater
      rcases inEvents with rfl | rfl <;> rcases inLater with rfl | rfl <;>
        simp_all [witnessGenerateEvent, witnessAdjudicateEvent] }

private def witnessSnapshot : AdjudicationSnapshot Nat Bool Nat Bool Nat 7 :=
  { freezeEvent := 1
    decisionEvent := 3
    frozenAt := 1
    decidedAt := 2
    freezeBeforeDecision := by decide
    timeBeforeDecision := by decide
    filtration := witnessFiltration
    artifactDependsOn := fun source target => source = target
    commitmentRoots := {true}
    evidenceDependsOn := fun source target => source = target
    evidenceDependencies := {true}
    commitmentClosureVisibleAtFreeze := by
      intro evidence dependency
      have evidenceEq : evidence = true := by simpa using dependency
      subst evidence
      exact Or.inl ⟨rfl, le_rfl⟩ }

private theorem witness_reachable_eq {source target : Bool}
    (reachable : Relation.ReflTransGen
      (fun left right : Bool => left = right) source target) :
    source = target := by
  simpa only [Relation.reflTransGen_eq_self] using reachable

private theorem witnessValidTrace : ValidTrace witnessLedger witnessSnapshot := by
  intro event inLedger
  simp only [witnessLedger, List.mem_cons, List.not_mem_nil, or_false] at inLedger
  rcases inLedger with rfl | rfl
  · exact Or.inl ⟨rfl, le_rfl⟩
  · exact Or.inr ⟨rfl, le_rfl⟩

theorem adaptive_use_present_witness :
    AdaptiveUseInClosure witnessLedger witnessSnapshot witnessValidTrace true := by
  refine ⟨witnessGenerateEvent, ?_, rfl,
    by simp [adaptiveRoles, witnessGenerateEvent], ?_⟩
  · simp [InAdjudicationPrefix, RolePrefixAtEvent, RolePrefixAtRound,
      RolePrefixAtTime, witnessLedger, witnessSnapshot, witnessGenerateEvent]
  · refine ⟨true, by simp [witnessGenerateEvent], ?_⟩
    exact ⟨true, by simp [witnessSnapshot], Relation.ReflTransGen.refl⟩

theorem admissible_judge_present_witness :
    AdmissibleJudge witnessLedger witnessSnapshot witnessValidTrace false := by
  unfold AdmissibleJudge
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨witnessAdjudicateEvent, ?_, rfl, rfl, rfl⟩
    simp [InAdjudicationPrefix, RolePrefixAtEvent, RolePrefixAtRound,
      RolePrefixAtTime, witnessLedger, witnessSnapshot, witnessAdjudicateEvent]
  · simp [witnessSnapshot, witnessFiltration]
  · simp [witnessSnapshot]
  · rintro ⟨event, inPrefix, evidenceEq, adaptiveRole, _touches⟩
    have eventCases :
        event = witnessGenerateEvent \/ event = witnessAdjudicateEvent := by
      simpa only [witnessLedger, List.mem_cons, List.not_mem_nil, or_false] using
        inPrefix.1.1
    rcases eventCases with rfl | rfl
    · simp [witnessGenerateEvent] at evidenceEq
    · simp [adaptiveRoles, witnessAdjudicateEvent] at adaptiveRole

theorem nonanticipating_boundary_witness :
    NonAnticipating witnessSnapshot false /\
      Not (NonAnticipating witnessSnapshot true) := by
  simp [NonAnticipating, witnessSnapshot, witnessFiltration]

theorem contamination_clean_set_boundary_witness :
    false ∈ Contam (fun source target : Bool => source = target) {false} /\
      AdjudicationSetClean witnessSnapshot ({false} : Set Bool) /\
      Not (AdjudicationSetClean witnessSnapshot ({true} : Set Bool)) := by
  refine ⟨⟨false, by simp, Relation.ReflTransGen.refl⟩, ?_, ?_⟩
  · constructor
    · apply Set.eq_empty_iff_forall_notMem.2
      intro evidence membership
      rcases membership with ⟨contaminated, dependency⟩
      rcases contaminated with ⟨record, recordMem, reachable⟩
      have recordEq : record = false := by simpa using recordMem
      subst record
      change Relation.ReflTransGen
        (fun left right : Bool => left = right) false evidence at reachable
      have evidenceEq : evidence = false := (witness_reachable_eq reachable).symm
      have evidenceTrue : evidence = true := by
        simpa [witnessSnapshot] using dependency
      simp [evidenceTrue] at evidenceEq
    · intro judge inJudges
      have judgeEq : judge = false := by simpa using inJudges
      subst judge
      simp [witnessSnapshot, witnessFiltration]
  · intro clean
    have trueInContam : true ∈
        Contam witnessSnapshot.evidenceDependsOn ({true} : Set Bool) :=
      ⟨true, by simp, Relation.ReflTransGen.refl⟩
    have trueInDependencies : true ∈ witnessSnapshot.evidenceDependencies := by
      simp [witnessSnapshot]
    have membership : true ∈
        Contam witnessSnapshot.evidenceDependsOn ({true} : Set Bool) ∩
          witnessSnapshot.evidenceDependencies :=
      ⟨trueInContam, trueInDependencies⟩
    rw [clean.1] at membership
    exact membership

theorem role_partition_boundary_witness :
    EvidenceRole.generate ∈ adaptiveRoles /\
      EvidenceRole.tune ∈ adaptiveRoles /\
      EvidenceRole.select ∈ adaptiveRoles /\
      EvidenceRole.adjudicate ∉ adaptiveRoles /\
      EvidenceRole.replicate ∉ adaptiveRoles := by
  simp [adaptiveRoles]

theorem dependency_rejection_witness :
    true ∈ witnessSnapshot.evidenceDependencies /\
      Not (AdmissibleJudge witnessLedger witnessSnapshot witnessValidTrace true) := by
  have inDependencies : true ∈ witnessSnapshot.evidenceDependencies := by
    simp [witnessSnapshot]
  exact ⟨inDependencies, (role_admission_contamination_spec
    witnessLedger witnessSnapshot witnessValidTrace).2.2.2.2.2 true inDependencies⟩

theorem role_admission_nonvacuity :
    AdaptiveUseInClosure witnessLedger witnessSnapshot witnessValidTrace true /\
    AdmissibleJudge witnessLedger witnessSnapshot witnessValidTrace false /\
    (NonAnticipating witnessSnapshot false /\
      Not (NonAnticipating witnessSnapshot true)) /\
    (false ∈ Contam (fun source target : Bool => source = target) {false} /\
      AdjudicationSetClean witnessSnapshot ({false} : Set Bool) /\
      Not (AdjudicationSetClean witnessSnapshot ({true} : Set Bool))) /\
    (EvidenceRole.generate ∈ adaptiveRoles /\
      EvidenceRole.tune ∈ adaptiveRoles /\
      EvidenceRole.select ∈ adaptiveRoles /\
      EvidenceRole.adjudicate ∉ adaptiveRoles /\
      EvidenceRole.replicate ∉ adaptiveRoles) /\
    (true ∈ witnessSnapshot.evidenceDependencies /\
      Not (AdmissibleJudge witnessLedger witnessSnapshot witnessValidTrace true)) := by
  exact ⟨adaptive_use_present_witness, admissible_judge_present_witness,
    nonanticipating_boundary_witness, contamination_clean_set_boundary_witness,
    role_partition_boundary_witness, dependency_rejection_witness⟩

#print axioms EvidenceFiltration.seen_mono
#print axioms role_admission_contamination_spec
#print axioms admissible_judge_append_invariant
#print axioms role_admission_nonvacuity

end D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure
