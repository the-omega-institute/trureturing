/- GID: D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Access-derived first-seen times and snapshot-bounded role admission. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation
import Mathlib.Probability.Process.HittingTime

/- Library-search audit trail (2026-08-25):
   * `rg -n -i \
       'RoleEvent|role event|role.*ledger|ledger.*role|AdaptiveUse|'\
       'RolesUpTo|FirstSeen|freezePoint|adjudicationPoint|adjudicat|'\
       'Generate|Tune|Select|Replicate' \
       D5/S0/History D5/S1/Ledger D5/S3/ConceptDynamics --glob '*.lean'`
     found no other five-role evidence ledger, access-derived first-seen time,
     snapshot prefix, or matching admission theorem. History opcodes and grading
     ledgers do not carry the seven UseEvent fields.
   * `rg -n \
       '(List \([^)]*Event|List [A-Za-z0-9_.]*Event|'\
       ': Set [A-Za-z][A-Za-z0-9_]*|Relation\.ReflTransGen)' \
       D5/S0/History D5/S1/Ledger D5/S3/ConceptDynamics \
       --glob '*.lean' --glob '!RoleAdmissionContaminationClosure.lean' | head -160`
     found reusable `Relation.ReflTransGen` reachability, but no access log whose
     first k entries generate a dependency-closed filtration.
   * `rg -n -i \
       'admission|eligibility|contam|taint|pollut|provenance.*closure|'\
       'source.*closure|joint|common|shared|indexed|family|union|'\
       'intersection|kernel|readout' D5/S3/ConceptDynamics \
       --glob '*.lean' --glob '!RoleAdmissionContaminationClosure.lean' | head -220`
     found unrelated attack reachability and readout kernels; none combines
     role admission, access time, and contamination closure.
   * `git grep -n -E \
       '^def |^  def |^structure |^inductive |^abbrev |^theorem ' -- \
       D5/S3/ConceptDynamics/Provenance | head -120`
     found only finite proof-path source semantics beside this module. Those
     paths do not carry access events, role events, or freeze snapshots.
   * `rg -n 'hittingAfter_(eq_top|le|lt)|noncomputable def hittingAfter' \
       .lake/packages/mathlib/Mathlib/Probability/Process/HittingTime.lean`
     found the exact first-hitting-time construction with an empty-set value of
     top. `FirstSeen` below reuses `MeasureTheory.hittingAfter` rather than
     defining a second infimum convention.
   * `rg -n -i \
       'new observation|observation event|protocol independence|'\
       'independent protocol|新.*观察事件|观察事件|协议独立|独立关系' \
       docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md`
     found only the §48.2 requirement, not a definition of observation events
     or protocol independence. No free-Prop independence certificate is made
     load-bearing here; that source gap remains unresolved.
   * `rg -n -i \
       'access ledger|access event|访问账本|访问事件|EvidenceFiltration|FirstSeen' \
       docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md`
     found §48.1 lines 3621-3631: F_k is exactly the dependency closure of the
     first k access events, and FirstSeen is its first hitting time (top when
     never hit). `AccessLedger`, `EvidenceFiltration.seen`, and `FirstSeen`
     below implement that definition chain.
   * `rg -n 'Set EvidenceRole|generate.*tune.*select|role.*partition' \
       D5/S3/ConceptDynamics --glob '*.lean'`
     found the adaptive-role set only as three literals in this module and no
     reusable named set. `adaptiveRoles` below replaces all three copies.
   * `rg -n -i 'incoming|outgoing|predecessor|ancestor|dependency closure|'\
       'reachable.*commitment|commitment.*reachable' D5 --glob '*.lean'`
     found no existing incoming commitment closure. `Contam` remains outgoing,
     while `EvidenceFiltration.seen` is the incoming dependency closure of each
     accessed object, exactly as §48.1 requires; `AdjudicationSnapshot.dependencyClosure`
     separately traverses from a record into a commitment root, as required by §48.3.
   * `rg -n 'reflTransGen_swap|ReflTransGen.swap' \
       .lake/packages/mathlib/Mathlib/Logic/Relation.lean`
     found the pinned reversal lemmas; no second reversed relation is defined.
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

def Contam {Object : Type u}
    (dependsOn : Object → Object → Prop) (records : Set Object) : Set Object :=
  {object | ∃ record ∈ records, Relation.ReflTransGen dependsOn record object}

inductive AccessEvent (Object Round : Type u) where
  | access (object : Object)
  | commitmentFreeze (round : Round)
  deriving DecidableEq, Repr

structure AccessLedger (Object Round : Type u) where
  events : List (AccessEvent Object Round)

structure EvidenceFiltration (Object Round : Type u) where
  accessLedger : AccessLedger Object Round
  dependsOn : Object → Object → Prop

def EvidenceFiltration.seen {Object Round : Type u}
    (filtration : EvidenceFiltration Object Round) (cutoff : Nat) : Set Object :=
  {object | ∃ index accessed,
    index < cutoff ∧
    filtration.accessLedger.events[index]? = some (.access accessed) ∧
    Relation.ReflTransGen filtration.dependsOn object accessed}

theorem EvidenceFiltration.seen_mono {Object Round : Type u}
    (filtration : EvidenceFiltration Object Round) {i j : Nat} (hij : i ≤ j) :
    filtration.seen i ⊆ filtration.seen j := by
  rintro object ⟨index, accessed, before, atIndex, reachable⟩
  exact ⟨index, accessed, before.trans_le hij, atIndex, reachable⟩

noncomputable def FirstSeen {Object Round : Type u}
    (filtration : EvidenceFiltration Object Round) (object : Object) : WithTop Nat :=
  MeasureTheory.hittingAfter
    (fun cutoff candidate ↦ candidate ∈ filtration.seen cutoff)
    {proposition : Prop | proposition} 0 object

theorem first_seen_le_iff {Object Round : Type u}
    (filtration : EvidenceFiltration Object Round) (object : Object) (cutoff : Nat) :
    FirstSeen filtration object ≤ (cutoff : WithTop Nat) ↔
      ∃ index ≤ cutoff, object ∈ filtration.seen index := by
  simpa [FirstSeen] using
    (MeasureTheory.hittingAfter_bot_le_iff
      (u := fun index candidate ↦ candidate ∈ filtration.seen index)
      (s := {proposition : Prop | proposition})
      (i := cutoff) (ω := object))

theorem first_seen_eq_top_iff {Object Round : Type u}
    (filtration : EvidenceFiltration Object Round) (object : Object) :
    FirstSeen filtration object = ⊤ ↔
      ∀ index, object ∉ filtration.seen index := by
  simpa [FirstSeen] using
    (MeasureTheory.hittingAfter_eq_top_iff
      (u := fun index candidate ↦ candidate ∈ filtration.seen index)
      (s := {proposition : Prop | proposition})
      (n := 0) (ω := object))

theorem freeze_lt_first_seen_iff {Object Round : Type u}
    (filtration : EvidenceFiltration Object Round) (freezeEvent : Nat) (object : Object) :
    (freezeEvent : WithTop Nat) < FirstSeen filtration object ↔
      ∀ index ≤ freezeEvent, object ∉ filtration.seen index := by
  constructor
  · intro after index before seen
    exact (not_le_of_gt after)
      ((first_seen_le_iff filtration object freezeEvent).2 ⟨index, before, seen⟩)
  · intro unseen
    exact lt_of_not_ge fun atOrBefore ↦ by
      rcases (first_seen_le_iff filtration object freezeEvent).1 atOrBefore with
        ⟨index, before, seen⟩
      exact unseen index before seen

structure UseEvent
    (Object Round Protocol Time : Type u) where
  eventId : Nat
  evidence : Object
  round : Round
  role : EvidenceRole
  dependencies : Set Object
  protocol : Protocol
  usedAt : Time

structure RoleLedger
    (Object Round Protocol Time : Type u)
    [Preorder Round] [Preorder Time] where
  events : List (UseEvent Object Round Protocol Time)
  uniqueEventIds : (events.map fun event ↦ event.eventId).Nodup
  strictEventOrder : events.Pairwise (fun event later ↦ event.eventId < later.eventId)
  indexRespectsRound : ∀ {event later}, event ∈ events → later ∈ events →
    event.eventId ≤ later.eventId → event.round ≤ later.round
  indexRespectsTime : ∀ {event later}, event ∈ events → later ∈ events →
    event.eventId ≤ later.eventId → event.usedAt ≤ later.usedAt

def RolePrefixAtEvent
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    (ledger : RoleLedger Object Round Protocol Time) (cutoff : Nat) :
    Set (UseEvent Object Round Protocol Time) :=
  {event | event ∈ ledger.events ∧ event.eventId ≤ cutoff}

def RolePrefixAtRound
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    (ledger : RoleLedger Object Round Protocol Time) (round : Round) :
    Set (UseEvent Object Round Protocol Time) :=
  {event | event ∈ ledger.events ∧ event.round ≤ round}

def RolePrefixAtTime
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    (ledger : RoleLedger Object Round Protocol Time) (cutoff : Time) :
    Set (UseEvent Object Round Protocol Time) :=
  {event | event ∈ ledger.events ∧ event.usedAt ≤ cutoff}

structure AdjudicationSnapshot
    (Object Round Time : Type u) [Preorder Time] (round : Round) where
  freezeEvent : Nat
  decisionEvent : Nat
  frozenAt : Time
  decidedAt : Time
  freezeBeforeDecision : freezeEvent ≤ decisionEvent
  timeBeforeDecision : frozenAt ≤ decidedAt
  filtration : EvidenceFiltration Object Round
  commitmentRoots : Set Object
  freezeRecorded :
    filtration.accessLedger.events[freezeEvent]? = some (.commitmentFreeze round)
  commitmentClosureVisibleAtFreeze :
    Contam filtration.dependsOn commitmentRoots ⊆ filtration.seen freezeEvent

def AdjudicationSnapshot.dependencyClosure
    {Object Round Time : Type u} [Preorder Time] {round : Round}
    (snapshot : AdjudicationSnapshot Object Round Time round) : Set Object :=
  {record | ∃ commitment ∈ snapshot.commitmentRoots,
    Relation.ReflTransGen snapshot.filtration.dependsOn record commitment}

def AppendOnlyExtension
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    (oldLedger newLedger : RoleLedger Object Round Protocol Time)
    (snapshot : AdjudicationSnapshot Object Round Time round) : Prop :=
  ∃ tail, newLedger.events = oldLedger.events ++ tail ∧
    ∀ event, event ∈ tail → snapshot.decisionEvent < event.eventId

def ValidTrace
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger Object Round Protocol Time)
    (snapshot : AdjudicationSnapshot Object Round Time round) : Prop :=
  ∀ event, event ∈ ledger.events →
    event.evidence ∈ snapshot.filtration.seen event.eventId

def InAdjudicationPrefix
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger Object Round Protocol Time)
    (snapshot : AdjudicationSnapshot Object Round Time round)
    (_validTrace : ValidTrace ledger snapshot)
    (event : UseEvent Object Round Protocol Time) : Prop :=
  event ∈ RolePrefixAtEvent ledger snapshot.decisionEvent ∧
    event ∈ RolePrefixAtRound ledger round ∧
    event ∈ RolePrefixAtTime ledger snapshot.decidedAt

def RolesAt
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger Object Round Protocol Time)
    (snapshot : AdjudicationSnapshot Object Round Time round)
    (validTrace : ValidTrace ledger snapshot) (evidence : Object) : Set EvidenceRole :=
  {role | ∃ event, InAdjudicationPrefix ledger snapshot validTrace event ∧
    event.evidence = evidence ∧ event.round = round ∧ event.role = role}

def AdaptiveUseInClosure
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger Object Round Protocol Time)
    (snapshot : AdjudicationSnapshot Object Round Time round)
    (validTrace : ValidTrace ledger snapshot) (evidence : Object) : Prop :=
  ∃ event, InAdjudicationPrefix ledger snapshot validTrace event ∧
    event.evidence = evidence ∧
    event.role ∈ adaptiveRoles ∧
    Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure)

def AdmissibleJudge
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger Object Round Protocol Time)
    (snapshot : AdjudicationSnapshot Object Round Time round)
    (validTrace : ValidTrace ledger snapshot) (evidence : Object) : Prop :=
  .adjudicate ∈ RolesAt ledger snapshot validTrace evidence ∧
    (snapshot.freezeEvent : WithTop Nat) < FirstSeen snapshot.filtration evidence ∧
    evidence ∉ snapshot.dependencyClosure ∧
    ¬ AdaptiveUseInClosure ledger snapshot validTrace evidence

def NonAnticipating
    {Object Round Time : Type u} [Preorder Time] {round : Round}
    (snapshot : AdjudicationSnapshot Object Round Time round) (evidence : Object) : Prop :=
  evidence ∈ snapshot.filtration.seen snapshot.decisionEvent ∧
    evidence ∉ snapshot.filtration.seen snapshot.freezeEvent ∧
    evidence ∉ snapshot.dependencyClosure

def AdjudicationSetClean
    {Object Round Time : Type u} [Preorder Time] {round : Round}
    (snapshot : AdjudicationSnapshot Object Round Time round)
    (judges : Set Object) : Prop :=
  Contam snapshot.filtration.dependsOn judges ∩ snapshot.dependencyClosure = ∅ ∧
    ∀ judge ∈ judges,
      (snapshot.freezeEvent : WithTop Nat) < FirstSeen snapshot.filtration judge

noncomputable def ReuseDepth
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger Object Round Protocol Time)
    (snapshot : AdjudicationSnapshot Object Round Time round)
    (validTrace : ValidTrace ledger snapshot) (evidence : Object) : Nat := by
  classical
  exact (ledger.events.filter fun event ↦
    InAdjudicationPrefix ledger snapshot validTrace event ∧
      event.evidence = evidence ∧
      event.role ∈ adaptiveRoles ∧
      Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure)).length

theorem role_admission_contamination_spec
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger Object Round Protocol Time)
    (snapshot : AdjudicationSnapshot Object Round Time round)
    (validTrace : ValidTrace ledger snapshot) :
    (∀ evidence,
      AdaptiveUseInClosure ledger snapshot validTrace evidence ↔
        ∃ event, InAdjudicationPrefix ledger snapshot validTrace event ∧
          event.evidence = evidence ∧
          event.role ∈ adaptiveRoles ∧
          Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure)) ∧
    (∀ evidence,
      AdmissibleJudge ledger snapshot validTrace evidence ↔
        .adjudicate ∈ RolesAt ledger snapshot validTrace evidence ∧
          (snapshot.freezeEvent : WithTop Nat) <
            FirstSeen snapshot.filtration evidence ∧
          evidence ∉ snapshot.dependencyClosure ∧
          ¬ AdaptiveUseInClosure ledger snapshot validTrace evidence) ∧
    (∀ evidence,
      NonAnticipating snapshot evidence ↔
          evidence ∈ snapshot.filtration.seen snapshot.decisionEvent ∧
          evidence ∉ snapshot.filtration.seen snapshot.freezeEvent ∧
          evidence ∉ snapshot.dependencyClosure) ∧
    ((∀ (dependsOn : Object → Object → Prop) (records : Set Object) (object : Object),
      object ∈ Contam dependsOn records ↔
        ∃ record ∈ records, Relation.ReflTransGen dependsOn record object) ∧
      (∀ judges : Set Object,
        AdjudicationSetClean snapshot judges ↔
          Contam snapshot.filtration.dependsOn judges ∩ snapshot.dependencyClosure = ∅ ∧
          ∀ judge ∈ judges,
            (snapshot.freezeEvent : WithTop Nat) <
              FirstSeen snapshot.filtration judge)) ∧
    (EvidenceRole.generate ∈ adaptiveRoles ∧
      EvidenceRole.tune ∈ adaptiveRoles ∧
      EvidenceRole.select ∈ adaptiveRoles ∧
      EvidenceRole.adjudicate ∉ adaptiveRoles ∧
      EvidenceRole.replicate ∉ adaptiveRoles) ∧
    (∀ evidence, evidence ∈ snapshot.dependencyClosure →
      ¬ AdmissibleJudge ledger snapshot validTrace evidence) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro evidence
    rfl
  · intro evidence
    rfl
  · intro evidence
    rfl
  · exact ⟨fun _ _ _ ↦ Iff.rfl, fun _ ↦ Iff.rfl⟩
  · simp [adaptiveRoles, Set.mem_insert_iff, Set.mem_singleton_iff]
  · intro evidence contaminated admitted
    exact admitted.2.2.1 contaminated

private theorem prefix_event_append_iff
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger : RoleLedger Object Round Protocol Time}
    {snapshot : AdjudicationSnapshot Object Round Time round}
    {tail : List (UseEvent Object Round Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : ∀ event, event ∈ tail → snapshot.decisionEvent < event.eventId)
    (event : UseEvent Object Round Protocol Time) :
    event ∈ RolePrefixAtEvent extendedLedger snapshot.decisionEvent ↔
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
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger : RoleLedger Object Round Protocol Time}
    {snapshot : AdjudicationSnapshot Object Round Time round}
    {tail : List (UseEvent Object Round Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : ∀ event, event ∈ tail → snapshot.decisionEvent < event.eventId)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (event : UseEvent Object Round Protocol Time) :
    InAdjudicationPrefix extendedLedger snapshot validExtended event ↔
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
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger : RoleLedger Object Round Protocol Time}
    {snapshot : AdjudicationSnapshot Object Round Time round}
    {tail : List (UseEvent Object Round Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : ∀ event, event ∈ tail → snapshot.decisionEvent < event.eventId)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (evidence : Object) :
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
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger : RoleLedger Object Round Protocol Time}
    {snapshot : AdjudicationSnapshot Object Round Time round}
    {tail : List (UseEvent Object Round Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : ∀ event, event ∈ tail → snapshot.decisionEvent < event.eventId)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (evidence : Object) :
    AdaptiveUseInClosure extendedLedger snapshot validExtended evidence ↔
      AdaptiveUseInClosure oldLedger snapshot validOld evidence := by
  constructor
  · rintro ⟨event, inExtended, evidenceEq, adaptiveRole, touches⟩
    exact ⟨event, (in_prefix_append_iff extendedEvents late validOld validExtended event).mp
      inExtended, evidenceEq, adaptiveRole, touches⟩
  · rintro ⟨event, inOld, evidenceEq, adaptiveRole, touches⟩
    exact ⟨event, (in_prefix_append_iff extendedEvents late validOld validExtended event).mpr
      inOld, evidenceEq, adaptiveRole, touches⟩

theorem admissible_judge_append_invariant
    {Object Round Protocol Time : Type u} [Preorder Round] [Preorder Time]
    {round : Round}
    (oldLedger extendedLedger : RoleLedger Object Round Protocol Time)
    (snapshot : AdjudicationSnapshot Object Round Time round)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (extension : AppendOnlyExtension oldLedger extendedLedger snapshot) :
    ∀ evidence,
      AdmissibleJudge extendedLedger snapshot validExtended evidence ↔
        AdmissibleJudge oldLedger snapshot validOld evidence := by
  rcases extension with ⟨tail, extendedEvents, late⟩
  have roles := roles_append_iff extendedEvents late validOld validExtended
  have adaptive := adaptive_append_iff extendedEvents late validOld validExtended
  intro evidence
  unfold AdmissibleJudge
  rw [roles evidence, adaptive evidence]

private def witnessFiltration : EvidenceFiltration Bool Nat :=
  { accessLedger := ⟨[.access true, .commitmentFreeze 7, .access false]⟩
    dependsOn := fun source target ↦ source = target }

private theorem witness_reachable_eq {source target : Bool}
    (reachable : Relation.ReflTransGen witnessFiltration.dependsOn source target) :
    source = target := by
  change Relation.ReflTransGen (fun left right : Bool ↦ left = right) source target at reachable
  simpa only [Relation.reflTransGen_eq_self] using reachable

private def witnessGenerateEvent : UseEvent Bool Nat Unit Nat :=
  { eventId := 1, evidence := true, round := 7, role := .generate,
    dependencies := {true}, protocol := (), usedAt := 1 }

private def witnessAdjudicateEvent : UseEvent Bool Nat Unit Nat :=
  { eventId := 3, evidence := false, round := 7, role := .adjudicate,
    dependencies := ∅, protocol := (), usedAt := 2 }

private def witnessLedger : RoleLedger Bool Nat Unit Nat :=
  { events := [witnessGenerateEvent, witnessAdjudicateEvent]
    uniqueEventIds := by simp [witnessGenerateEvent, witnessAdjudicateEvent]
    strictEventOrder := by simp [witnessGenerateEvent, witnessAdjudicateEvent]
    indexRespectsRound := by
      intro event later inEvents inLater before
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inEvents inLater
      rcases inEvents with rfl | rfl <;> rcases inLater with rfl | rfl <;>
        simp [witnessGenerateEvent, witnessAdjudicateEvent]
    indexRespectsTime := by
      intro event later inEvents inLater before
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inEvents inLater
      rcases inEvents with rfl | rfl <;> rcases inLater with rfl | rfl <;>
        simp_all [witnessGenerateEvent, witnessAdjudicateEvent] }

private def witnessSnapshot : AdjudicationSnapshot Bool Nat Nat 7 :=
  { freezeEvent := 1
    decisionEvent := 3
    frozenAt := 1
    decidedAt := 2
    freezeBeforeDecision := by decide
    timeBeforeDecision := by decide
    filtration := witnessFiltration
    commitmentRoots := {true}
    freezeRecorded := rfl
    commitmentClosureVisibleAtFreeze := by
      intro object contaminated
      rcases contaminated with ⟨root, rootMem, reachable⟩
      have rootEq : root = true := by simpa using rootMem
      subst root
      have objectEq : object = true := (witness_reachable_eq reachable).symm
      subst object
      exact ⟨0, true, by decide, rfl, Relation.ReflTransGen.refl⟩ }

private theorem witnessValidTrace : ValidTrace witnessLedger witnessSnapshot := by
  intro event inLedger
  simp only [witnessLedger, List.mem_cons, List.not_mem_nil, or_false] at inLedger
  rcases inLedger with rfl | rfl
  · exact ⟨0, true, by decide, rfl, Relation.ReflTransGen.refl⟩
  · exact ⟨2, false, by decide, rfl, Relation.ReflTransGen.refl⟩

theorem adaptive_use_present_witness :
    AdaptiveUseInClosure witnessLedger witnessSnapshot witnessValidTrace true := by
  apply (role_admission_contamination_spec
    witnessLedger witnessSnapshot witnessValidTrace).1 true |>.2
  refine ⟨witnessGenerateEvent, ?_, rfl,
    by simp [adaptiveRoles, witnessGenerateEvent], ?_⟩
  · simp [InAdjudicationPrefix, RolePrefixAtEvent, RolePrefixAtRound,
      RolePrefixAtTime, witnessLedger, witnessSnapshot, witnessGenerateEvent]
  · refine ⟨true, by simp [witnessGenerateEvent], ?_⟩
    exact ⟨true, by simp [witnessSnapshot], Relation.ReflTransGen.refl⟩

theorem admissible_judge_present_witness :
    AdmissibleJudge witnessLedger witnessSnapshot witnessValidTrace false := by
  apply (role_admission_contamination_spec
    witnessLedger witnessSnapshot witnessValidTrace).2.1 false |>.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨witnessAdjudicateEvent, ?_, rfl, rfl, rfl⟩
    simp [InAdjudicationPrefix, RolePrefixAtEvent, RolePrefixAtRound,
      RolePrefixAtTime, witnessLedger, witnessSnapshot, witnessAdjudicateEvent]
  · rw [freeze_lt_first_seen_iff]
    intro index before seen
    rcases seen with ⟨accessIndex, accessed, accessBefore, atIndex, reachable⟩
    change index ≤ 1 at before
    have accessIndexEq : accessIndex = 0 := by omega
    have indexEq : index = 1 := by omega
    subst accessIndex
    subst index
    have accessedEq : accessed = true := by
      simpa [witnessSnapshot, witnessFiltration] using atIndex.symm
    subst accessed
    exact Bool.noConfusion (witness_reachable_eq reachable)
  · rintro ⟨root, rootMem, reachable⟩
    have rootEq : root = true := by simpa [witnessSnapshot] using rootMem
    subst root
    exact Bool.noConfusion (witness_reachable_eq reachable)
  · intro adaptive
    rcases (role_admission_contamination_spec
      witnessLedger witnessSnapshot witnessValidTrace).1 false |>.1 adaptive with
      ⟨event, inPrefix, evidenceEq, adaptiveRole, _touches⟩
    have eventCases :
        event = witnessGenerateEvent ∨ event = witnessAdjudicateEvent := by
      simpa only [witnessLedger, List.mem_cons, List.not_mem_nil, or_false] using
        inPrefix.1.1
    rcases eventCases with rfl | rfl
    · simp [witnessGenerateEvent] at evidenceEq
    · simp [adaptiveRoles, witnessAdjudicateEvent] at adaptiveRole

theorem nonanticipating_boundary_witness :
    NonAnticipating witnessSnapshot false ∧
      ¬ NonAnticipating witnessSnapshot true := by
  have characterization := (role_admission_contamination_spec
    witnessLedger witnessSnapshot witnessValidTrace).2.2.1
  constructor
  · apply (characterization false).2
    refine ⟨⟨2, false, by decide, rfl, Relation.ReflTransGen.refl⟩, ?_, ?_⟩
    · rintro ⟨index, accessed, before, atIndex, reachable⟩
      change index < 1 at before
      have indexEq : index = 0 := by omega
      subst index
      have accessedEq : accessed = true := by
        simpa [witnessSnapshot, witnessFiltration] using atIndex.symm
      subst accessed
      exact Bool.noConfusion (witness_reachable_eq reachable)
    · rintro ⟨root, rootMem, reachable⟩
      have rootEq : root = true := by simpa [witnessSnapshot] using rootMem
      subst root
      exact Bool.noConfusion (witness_reachable_eq reachable)
  · intro anticipatory
    exact ((characterization true).1 anticipatory).2.1
      ⟨0, true, by decide, rfl, Relation.ReflTransGen.refl⟩

theorem contamination_clean_set_boundary_witness :
    false ∈ Contam (fun source target : Bool ↦ source = target) {false} ∧
      AdjudicationSetClean witnessSnapshot ({false} : Set Bool) ∧
      ¬ AdjudicationSetClean witnessSnapshot ({true} : Set Bool) := by
  have characterization := (role_admission_contamination_spec
    witnessLedger witnessSnapshot witnessValidTrace).2.2.2.1
  refine ⟨(characterization.1 _ _ false).2
      ⟨false, by simp, Relation.ReflTransGen.refl⟩, ?_, ?_⟩
  · apply (characterization.2 {false}).2
    constructor
    · apply Set.eq_empty_iff_forall_notMem.2
      intro object membership
      rcases membership with ⟨contaminated, inClosure⟩
      rcases contaminated with ⟨root, rootMem, reachable⟩
      have rootEq : root = false := by simpa using rootMem
      subst root
      have objectEq : object = false := (witness_reachable_eq reachable).symm
      subst object
      rcases inClosure with ⟨commitment, commitmentMem, commitmentReachable⟩
      have commitmentEq : commitment = true := by
        simpa [witnessSnapshot] using commitmentMem
      subst commitment
      exact Bool.noConfusion (witness_reachable_eq commitmentReachable)
    · intro judge inJudges
      have judgeEq : judge = false := by simpa using inJudges
      subst judge
      exact (role_admission_contamination_spec
        witnessLedger witnessSnapshot witnessValidTrace).2.1 false |>.1
          admissible_judge_present_witness |>.2.1
  · intro clean
    have expanded := (characterization.2 {true}).1 clean
    have trueInContam : true ∈
        Contam witnessSnapshot.filtration.dependsOn ({true} : Set Bool) :=
      ⟨true, by simp, Relation.ReflTransGen.refl⟩
    have trueInClosure : true ∈ witnessSnapshot.dependencyClosure :=
      ⟨true, by simp [witnessSnapshot], Relation.ReflTransGen.refl⟩
    have : true ∈
        Contam witnessSnapshot.filtration.dependsOn ({true} : Set Bool) ∩
          witnessSnapshot.dependencyClosure := ⟨trueInContam, trueInClosure⟩
    rw [expanded.1] at this
    exact this

theorem role_partition_boundary_witness :
    EvidenceRole.generate ∈ adaptiveRoles ∧
      EvidenceRole.tune ∈ adaptiveRoles ∧
      EvidenceRole.select ∈ adaptiveRoles ∧
      EvidenceRole.adjudicate ∉ adaptiveRoles ∧
      EvidenceRole.replicate ∉ adaptiveRoles :=
  (role_admission_contamination_spec
    witnessLedger witnessSnapshot witnessValidTrace).2.2.2.2.1

theorem dependency_rejection_witness :
    true ∈ witnessSnapshot.dependencyClosure ∧
      ¬ AdmissibleJudge witnessLedger witnessSnapshot witnessValidTrace true := by
  have inClosure : true ∈ witnessSnapshot.dependencyClosure :=
    ⟨true, by simp [witnessSnapshot], Relation.ReflTransGen.refl⟩
  exact ⟨inClosure, (role_admission_contamination_spec
    witnessLedger witnessSnapshot witnessValidTrace).2.2.2.2.2 true inClosure⟩

private def directionFiltration : EvidenceFiltration Bool Nat :=
  { accessLedger := ⟨[.access true, .commitmentFreeze 7, .access false]⟩
    dependsOn := fun source target ↦ source = false ∧ target = true }
private theorem direction_from_true_eq {target : Bool}
    (reachable : Relation.ReflTransGen directionFiltration.dependsOn true target) :
    target = true := by
  induction reachable with
  | refl => rfl
  | tail _ step _ => exact step.2
private def directionAdjudicateEvent : UseEvent Bool Nat Unit Nat :=
  { eventId := 3, evidence := false, round := 7, role := .adjudicate,
    dependencies := ∅, protocol := (), usedAt := 2 }
private def directionLedger : RoleLedger Bool Nat Unit Nat :=
  { events := [directionAdjudicateEvent]
    uniqueEventIds := by simp [directionAdjudicateEvent], strictEventOrder := by simp
    indexRespectsRound := by
      intro event later inEvents inLater _before
      simp only [List.mem_singleton] at inEvents inLater
      subst event; subst later; exact le_rfl
    indexRespectsTime := by
      intro event later inEvents inLater _before
      simp only [List.mem_singleton] at inEvents inLater
      subst event; subst later; exact le_rfl }
private def directionSnapshot : AdjudicationSnapshot Bool Nat Nat 7 :=
  { freezeEvent := 1, decisionEvent := 3, frozenAt := 1, decidedAt := 2
    freezeBeforeDecision := by decide, timeBeforeDecision := by decide
    filtration := directionFiltration
    commitmentRoots := {true}
    freezeRecorded := rfl
    commitmentClosureVisibleAtFreeze := by
      intro object contaminated
      rcases contaminated with ⟨root, rootMem, reachable⟩
      have rootEq : root = true := by simpa using rootMem
      subst root
      have objectEq : object = true := direction_from_true_eq reachable
      subst object
      exact ⟨0, true, by decide, rfl, Relation.ReflTransGen.refl⟩ }
private theorem directionValidTrace : ValidTrace directionLedger directionSnapshot := by
  intro event inLedger
  simp only [directionLedger, List.mem_singleton] at inLedger
  subst event
  exact ⟨2, false, by decide, rfl, Relation.ReflTransGen.refl⟩
private theorem direction_role_present : EvidenceRole.adjudicate ∈
    RolesAt directionLedger directionSnapshot directionValidTrace false := by
  refine ⟨directionAdjudicateEvent, ?_, rfl, rfl, rfl⟩
  simp [InAdjudicationPrefix, RolePrefixAtEvent, RolePrefixAtRound,
    RolePrefixAtTime, directionLedger, directionSnapshot, directionAdjudicateEvent]
private theorem direction_not_outbound :
    false ∉ Contam directionFiltration.dependsOn ({true} : Set Bool) := by
  rintro ⟨root, rootMem, reachable⟩
  have rootEq : root = true := by simpa using rootMem
  subst root
  exact Bool.noConfusion (direction_from_true_eq reachable)

private theorem direction_not_adaptive : ¬ AdaptiveUseInClosure
    directionLedger directionSnapshot directionValidTrace false := by
  rintro ⟨event, inPrefix, _evidenceEq, adaptiveRole, _touches⟩
  have eventEq : event = directionAdjudicateEvent := by
    simpa [directionLedger, directionAdjudicateEvent] using inPrefix.1.1
  subst event
  simp [adaptiveRoles, directionAdjudicateEvent] at adaptiveRole

/-- The asymmetric edge `false → true` separates the §48.3 incoming closure from
outgoing `Contam`. The last conjunct substitutes the old closure in the judge
formula: it accepts `false`, while the incoming closure rejects it. -/
theorem dependency_direction_witness :
    directionSnapshot.dependencyClosure ≠
        Contam directionFiltration.dependsOn directionSnapshot.commitmentRoots ∧
      ¬ AdmissibleJudge
        directionLedger directionSnapshot directionValidTrace false ∧
      (EvidenceRole.adjudicate ∈
          RolesAt directionLedger directionSnapshot directionValidTrace false ∧
        false ∉ Contam directionFiltration.dependsOn
          directionSnapshot.commitmentRoots ∧
        ¬ AdaptiveUseInClosure
          directionLedger directionSnapshot directionValidTrace false) := by
  have incoming : false ∈ directionSnapshot.dependencyClosure := by
    refine ⟨true, by simp [directionSnapshot], ?_⟩
    exact Relation.ReflTransGen.single (by simp [directionSnapshot, directionFiltration])
  have outbound : false ∉
      Contam directionFiltration.dependsOn directionSnapshot.commitmentRoots := by
    simpa [directionSnapshot] using direction_not_outbound
  refine ⟨?_, ?_, direction_role_present,
    outbound, direction_not_adaptive⟩
  · intro sameClosure
    exact outbound (sameClosure ▸ incoming)
  · intro admitted
    exact admitted.2.2.1 incoming

/-- Deleting or weakening any named leaf breaks this proof. This aggregate has no
outer machine consumer; another Lean wrapper would only move that boundary. The
natural outer consumer is the post-deposit frozen ledger, unavailable this round. -/
theorem role_admission_nonvacuity :
    AdaptiveUseInClosure witnessLedger witnessSnapshot witnessValidTrace true ∧
    AdmissibleJudge witnessLedger witnessSnapshot witnessValidTrace false ∧
    (NonAnticipating witnessSnapshot false ∧
      ¬ NonAnticipating witnessSnapshot true) ∧
    (false ∈ Contam (fun source target : Bool ↦ source = target) {false} ∧
      AdjudicationSetClean witnessSnapshot ({false} : Set Bool) ∧
      ¬ AdjudicationSetClean witnessSnapshot ({true} : Set Bool)) ∧
    (EvidenceRole.generate ∈ adaptiveRoles ∧
      EvidenceRole.tune ∈ adaptiveRoles ∧
      EvidenceRole.select ∈ adaptiveRoles ∧
      EvidenceRole.adjudicate ∉ adaptiveRoles ∧
      EvidenceRole.replicate ∉ adaptiveRoles) ∧
    (true ∈ witnessSnapshot.dependencyClosure ∧
      ¬ AdmissibleJudge witnessLedger witnessSnapshot witnessValidTrace true) ∧
    (directionSnapshot.dependencyClosure ≠
        Contam directionFiltration.dependsOn directionSnapshot.commitmentRoots ∧
      ¬ AdmissibleJudge
        directionLedger directionSnapshot directionValidTrace false ∧
      (EvidenceRole.adjudicate ∈
          RolesAt directionLedger directionSnapshot directionValidTrace false ∧
        false ∉ Contam directionFiltration.dependsOn
          directionSnapshot.commitmentRoots ∧
        ¬ AdaptiveUseInClosure
          directionLedger directionSnapshot directionValidTrace false)) := by
  exact ⟨adaptive_use_present_witness, admissible_judge_present_witness,
    nonanticipating_boundary_witness, contamination_clean_set_boundary_witness,
    role_partition_boundary_witness, dependency_rejection_witness,
    dependency_direction_witness⟩

#print axioms first_seen_le_iff
#print axioms first_seen_eq_top_iff
#print axioms role_admission_contamination_spec
#print axioms admissible_judge_append_invariant
#print axioms dependency_direction_witness
#print axioms role_admission_nonvacuity

end D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure
