/- GID: D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Versioned evidence filtration and snapshot-bounded role admission. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation

/- Library-search audit trail (2026-08-25):
   * `rg -n -i 'RoleEvent|role event|role.*ledger|ledger.*role|AdaptiveUse|RolesUpTo|FirstSeen|freezePoint|adjudicationPoint|adjudicat|Generate|Tune|Select|Replicate' D5/S0/History D5/S1/Ledger D5/S3/ConceptDynamics --glob '*.lean'`
     found no five-role evidence ledger, filtration-backed first-seen predicate,
     snapshot prefix, or matching admission theorem. Existing History events
     are opcodes and LedgerLimit histories are grading records, not UseEvent.
   * `rg -n '(List \([^)]*Event|List [A-Za-z0-9_.]*Event|: Set [A-Za-z][A-Za-z0-9_]*|Relation\.ReflTransGen)' D5/S0/History D5/S1/Ledger D5/S3/ConceptDynamics --glob '*.lean' --glob '!RoleAdmissionContaminationClosure.lean' | head -160`
     found statement/revision-time sets and permission-indexed Reach, but no
     event list carrying evidence, role, dependencies, round, protocol, and time.
   * `rg -n -i 'admission|eligibility|contam|taint|pollut|provenance.*closure|source.*closure|joint|common|shared|indexed|family|union|intersection|kernel|readout' D5/S3/ConceptDynamics --glob '*.lean' --glob '!RoleAdmissionContaminationClosure.lean' | head -220`
     found only unrelated admission, attack reachability, and readout kernels;
     no source-level role admission or contamination closure covers this shape.
   * `git grep -n -E '^def |^  def |^structure |^inductive |^abbrev |^theorem ' -- D5/S3/ConceptDynamics/Provenance | head -120`
     found only FiniteProofGraphSourceSemantics declarations beside this file;
     its finite proof paths do not carry filtration or role-ledger fields.
   * `rg -n -i '证据|角色|账本|滤过|首次出现|首次可达|可达|闭包|污染|准入|裁决|冻结|复制|协议|时间' D5/S3/ConceptDynamics --glob '*.lean' --glob '!RoleAdmissionContaminationClosure.lean'`
     found no matching Chinese-domain declaration. The exact five-role and
     snapshot interfaces are therefore introduced here from CAS §48.1-48.3/
     §54.3; no existing local declaration is shadowed.
   * `rg -n 'EvidenceFiltration|UseEvent|RoleLedger|AdjudicationSnapshot|ValidTrace|InAdjudicationPrefix|AdmissibleJudge|NonAnticipating' docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md`
     found the complete formal interface at §54.3 (lines 4630-4900), including
     the required typeclass assumptions. `FirstSeen` is defined in §48.1 from
     filtration history; this file derives it as a set of minimal seen times,
     rather than accepting a caller-supplied function.
   * The CAS does not define the internal meaning of `Protocol`, `Time`, a new
     observation, or protocol independence. They remain general parameters;
     `ReplicateIndependent` only consumes explicit propositions for those
     missing semantics and never invents a structure.
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

structure UseEvent
    (EventId Evidence Round Artifact Protocol Time : Type u) where
  eventId : EventId
  evidence : Evidence
  round : Round
  role : EvidenceRole
  dependencies : Set Artifact
  protocol : Protocol
  usedAt : Time

structure EvidenceFiltration
    (EventId Evidence : Type u) [Preorder EventId] where
  seen : EventId → Set Evidence
  monotone : ∀ {i j}, i ≤ j → seen i ⊆ seen j

structure RoleLedger
    (EventId Evidence Round Artifact Protocol Time : Type u)
    [LinearOrder EventId] [Preorder Round] [Preorder Time] where
  events : List (UseEvent EventId Evidence Round Artifact Protocol Time)
  uniqueEventIds : (events.map fun e => e.eventId).Nodup
  strictEventOrder : events.Pairwise (fun e e' => e.eventId < e'.eventId)
  indexRespectsRound : ∀ {e e'}, e ∈ events → e' ∈ events →
    e.eventId ≤ e'.eventId → e.round ≤ e'.round
  indexRespectsTime : ∀ {e e'}, e ∈ events → e' ∈ events →
    e.eventId ≤ e'.eventId → e.usedAt ≤ e'.usedAt

def RolePrefixAtEvent
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (cutoff : EventId) :
    Set (UseEvent EventId Evidence Round Artifact Protocol Time) :=
  {e | e ∈ ledger.events ∧ e.eventId ≤ cutoff}

def RolePrefixAtRound
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (round : Round) :
    Set (UseEvent EventId Evidence Round Artifact Protocol Time) :=
  {e | e ∈ ledger.events ∧ e.round ≤ round}

def RolePrefixAtTime
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (cutoff : Time) :
    Set (UseEvent EventId Evidence Round Artifact Protocol Time) :=
  {e | e ∈ ledger.events ∧ e.usedAt ≤ cutoff}

structure AdjudicationSnapshot
    (EventId Evidence Round Artifact Time : Type u)
    [Preorder EventId] [Preorder Time] (round : Round) where
  freezeEvent : EventId
  decisionEvent : EventId
  frozenAt : Time
  decidedAt : Time
  freezeBeforeDecision : freezeEvent ≤ decisionEvent
  timeBeforeDecision : frozenAt ≤ decidedAt
  filtration : EvidenceFiltration EventId Evidence
  dependencyClosure : Set Artifact
  evidenceDependencies : Set Evidence

def AppendOnlyExtension
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (oldLedger newLedger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round) : Prop :=
  ∃ tail, newLedger.events = oldLedger.events ++ tail ∧
    ∀ event, event ∈ tail → snapshot.decisionEvent < event.eventId

def ValidTrace
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round) : Prop :=
  ∀ event, event ∈ ledger.events → event.evidence ∈ snapshot.filtration.seen event.eventId

def InAdjudicationPrefix
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (_validTrace : ValidTrace ledger snapshot)
    (event : UseEvent EventId Evidence Round Artifact Protocol Time) : Prop :=
  event ∈ RolePrefixAtEvent ledger snapshot.decisionEvent ∧
    event ∈ RolePrefixAtRound ledger round ∧
    event ∈ RolePrefixAtTime ledger snapshot.decidedAt

def RolesAt
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validTrace : ValidTrace ledger snapshot)
    (evidence : Evidence) : Set EvidenceRole :=
  {role | ∃ event, InAdjudicationPrefix ledger snapshot validTrace event ∧
    event.evidence = evidence ∧ event.round = round ∧ event.role = role}

def AdaptiveUseInClosure
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validTrace : ValidTrace ledger snapshot)
    (evidence : Evidence) : Prop :=
  ∃ event, InAdjudicationPrefix ledger snapshot validTrace event ∧
    event.evidence = evidence ∧
    (event.role = .generate ∨ event.role = .tune ∨ event.role = .select) ∧
    Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure)

def AdmissibleJudge
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validTrace : ValidTrace ledger snapshot)
    (evidence : Evidence) : Prop :=
  .adjudicate ∈ RolesAt ledger snapshot validTrace evidence ∧
    evidence ∉ snapshot.filtration.seen snapshot.freezeEvent ∧
    evidence ∉ snapshot.evidenceDependencies ∧
      ¬ AdaptiveUseInClosure ledger snapshot validTrace evidence

def FirstSeen
    {EventId Evidence : Type u} [Preorder EventId]
    (filtration : EvidenceFiltration EventId Evidence)
    (evidence : Evidence) : Set EventId :=
  {time | evidence ∈ filtration.seen time ∧
    ∀ earlier, earlier < time → evidence ∉ filtration.seen earlier}

def FirstSeenAfter
    {EventId Evidence : Type u} [Preorder EventId]
    (filtration : EvidenceFiltration EventId Evidence)
    (cutoff : EventId) (evidence : Evidence) : Prop :=
  ∀ time, time ∈ FirstSeen filtration evidence → ¬ time ≤ cutoff

def Contam {Artifact : Type u}
    (dependsOn : Artifact → Artifact → Prop) (records : Set Artifact) : Set Artifact :=
  {artifact | ∃ record ∈ records, Relation.ReflTransGen dependsOn record artifact}

def NonAnticipating
    {EventId Evidence Round Artifact Time : Type u}
    [Preorder EventId] [Preorder Time] {round : Round}
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (evidence : Evidence) : Prop :=
  evidence ∈ snapshot.filtration.seen snapshot.decisionEvent ∧
    evidence ∉ snapshot.filtration.seen snapshot.freezeEvent ∧
    evidence ∉ snapshot.evidenceDependencies

def ReplicateIndependent
    {EventId Evidence Round Artifact Protocol Time : Type u}
    (event : UseEvent EventId Evidence Round Artifact Protocol Time)
    (newObservation protocolIndependent : Prop) : Prop :=
  event.role = .replicate ∧ newObservation ∧ protocolIndependent

noncomputable def ReuseDepth
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validTrace : ValidTrace ledger snapshot)
    (evidence : Evidence) : Nat := by
  classical
  exact (ledger.events.filter fun event =>
    InAdjudicationPrefix ledger snapshot validTrace event ∧
      event.evidence = evidence ∧
      (event.role = .generate ∨ event.role = .tune ∨ event.role = .select) ∧
      Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure)).length

theorem first_seen_is_filtration_derived
    {EventId Evidence : Type u} [Preorder EventId]
    (filtration : EvidenceFiltration EventId Evidence) (evidence : Evidence) :
    FirstSeen filtration evidence =
      {time | evidence ∈ filtration.seen time ∧
        ∀ earlier, earlier < time → evidence ∉ filtration.seen earlier} := by
  rfl

theorem role_admission_contamination_spec
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (ledger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validTrace : ValidTrace ledger snapshot) :
    (∀ evidence,
      AdaptiveUseInClosure ledger snapshot validTrace evidence ↔
        ∃ event, InAdjudicationPrefix ledger snapshot validTrace event ∧
          event.evidence = evidence ∧
          (event.role = .generate ∨ event.role = .tune ∨ event.role = .select) ∧
          Set.Nonempty (event.dependencies ∩ snapshot.dependencyClosure)) ∧
    (∀ evidence,
      AdmissibleJudge ledger snapshot validTrace evidence ↔
        .adjudicate ∈ RolesAt ledger snapshot validTrace evidence ∧
          evidence ∉ snapshot.filtration.seen snapshot.freezeEvent ∧
          evidence ∉ snapshot.evidenceDependencies ∧
          ¬ AdaptiveUseInClosure ledger snapshot validTrace evidence) ∧
    (∀ evidence,
      NonAnticipating snapshot evidence ↔
        evidence ∈ snapshot.filtration.seen snapshot.decisionEvent ∧
          evidence ∉ snapshot.filtration.seen snapshot.freezeEvent ∧
          evidence ∉ snapshot.evidenceDependencies) ∧
    (∀ (records : Set Artifact) (artifact : Artifact),
      artifact ∈ Contam (fun a b => a = b) records ↔
        ∃ record ∈ records,
          Relation.ReflTransGen (fun x y => x = y) record artifact) ∧
    (EvidenceRole.generate ∈ ({.generate, .tune, .select} : Set EvidenceRole) ∧
      EvidenceRole.tune ∈ ({.generate, .tune, .select} : Set EvidenceRole) ∧
      EvidenceRole.select ∈ ({.generate, .tune, .select} : Set EvidenceRole) ∧
      EvidenceRole.adjudicate ∉ ({.generate, .tune, .select} : Set EvidenceRole) ∧
      EvidenceRole.replicate ∉ ({.generate, .tune, .select} : Set EvidenceRole)) ∧
    (∀ evidence,
      evidence ∈ snapshot.evidenceDependencies →
        ¬ AdmissibleJudge ledger snapshot validTrace evidence) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro evidence
    rfl
  · intro evidence
    rfl
  · intro evidence
    rfl
  · intro records artifact
    rfl
  · simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  · intro evidence contaminated
    exact fun admitted => (admitted.2.2.1 contaminated)

private theorem prefix_event_append_iff
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger : RoleLedger EventId Evidence Round Artifact Protocol Time}
    {snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round}
    {tail : List (UseEvent EventId Evidence Round Artifact Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : ∀ event, event ∈ tail → snapshot.decisionEvent < event.eventId)
    (event : UseEvent EventId Evidence Round Artifact Protocol Time) :
    event ∈ RolePrefixAtEvent extendedLedger snapshot.decisionEvent ↔
      event ∈ RolePrefixAtEvent oldLedger snapshot.decisionEvent := by
  constructor
  · intro membership
    rcases membership with ⟨inEvents, beforeCutoff⟩
    rw [extendedEvents] at inEvents
    rcases List.mem_append.mp inEvents with inOld | inTail
    · exact ⟨inOld, beforeCutoff⟩
    · exact False.elim ((not_lt_of_ge beforeCutoff) (late event inTail))
  · intro membership
    exact ⟨by rw [extendedEvents]; exact List.mem_append_left tail membership.1,
      membership.2⟩

private theorem in_prefix_append_iff
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger : RoleLedger EventId Evidence Round Artifact Protocol Time}
    {snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round}
    {tail : List (UseEvent EventId Evidence Round Artifact Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : ∀ event, event ∈ tail → snapshot.decisionEvent < event.eventId)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (event : UseEvent EventId Evidence Round Artifact Protocol Time) :
    InAdjudicationPrefix extendedLedger snapshot validExtended event ↔
      InAdjudicationPrefix oldLedger snapshot validOld event := by
  constructor
  · intro h
    have oldPrefix := (prefix_event_append_iff extendedEvents late event).mp h.1
    exact ⟨oldPrefix, ⟨oldPrefix.1, h.2.1.2⟩, ⟨oldPrefix.1, h.2.2.2⟩⟩
  · intro h
    have extendedPrefix := (prefix_event_append_iff extendedEvents late event).mpr h.1
    exact ⟨extendedPrefix, ⟨extendedPrefix.1, h.2.1.2⟩,
      ⟨extendedPrefix.1, h.2.2.2⟩⟩

private theorem roles_append_iff
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger : RoleLedger EventId Evidence Round Artifact Protocol Time}
    {snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round}
    {tail : List (UseEvent EventId Evidence Round Artifact Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : ∀ event, event ∈ tail → snapshot.decisionEvent < event.eventId)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (evidence : Evidence) :
    RolesAt extendedLedger snapshot validExtended evidence =
      RolesAt oldLedger snapshot validOld evidence := by
  ext role
  constructor
  · rintro ⟨event, inExtended, evidenceEq, roundEq, roleEq⟩
    exact ⟨event, (in_prefix_append_iff extendedEvents late validOld validExtended event).mp inExtended,
      evidenceEq, roundEq, roleEq⟩
  · rintro ⟨event, inOld, evidenceEq, roundEq, roleEq⟩
    exact ⟨event, (in_prefix_append_iff extendedEvents late validOld validExtended event).mpr inOld,
      evidenceEq, roundEq, roleEq⟩

private theorem adaptive_append_iff
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    {oldLedger extendedLedger : RoleLedger EventId Evidence Round Artifact Protocol Time}
    {snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round}
    {tail : List (UseEvent EventId Evidence Round Artifact Protocol Time)}
    (extendedEvents : extendedLedger.events = oldLedger.events ++ tail)
    (late : ∀ event, event ∈ tail → snapshot.decisionEvent < event.eventId)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (evidence : Evidence) :
    AdaptiveUseInClosure extendedLedger snapshot validExtended evidence ↔
      AdaptiveUseInClosure oldLedger snapshot validOld evidence := by
  constructor
  · rintro ⟨event, inExtended, evidenceEq, adaptiveRole, touches⟩
    exact ⟨event, (in_prefix_append_iff extendedEvents late validOld validExtended event).mp inExtended,
      evidenceEq, adaptiveRole, touches⟩
  · rintro ⟨event, inOld, evidenceEq, adaptiveRole, touches⟩
    exact ⟨event, (in_prefix_append_iff extendedEvents late validOld validExtended event).mpr inOld,
      evidenceEq, adaptiveRole, touches⟩

theorem admissible_judge_append_invariant
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    {round : Round}
    (oldLedger extendedLedger : RoleLedger EventId Evidence Round Artifact Protocol Time)
    (snapshot : AdjudicationSnapshot EventId Evidence Round Artifact Time round)
    (validOld : ValidTrace oldLedger snapshot)
    (validExtended : ValidTrace extendedLedger snapshot)
    (extension : AppendOnlyExtension oldLedger extendedLedger snapshot) :
    ∀ evidence,
      AdmissibleJudge extendedLedger snapshot validExtended evidence ↔
        AdmissibleJudge oldLedger snapshot validOld evidence := by
  rcases extension with ⟨tail, extendedEvents, late⟩
  have hRoles := roles_append_iff extendedEvents late validOld validExtended
  have hAdaptive := adaptive_append_iff extendedEvents late validOld validExtended
  intro evidence
  unfold AdmissibleJudge
  rw [hRoles evidence, hAdaptive evidence]

/- Positive witness: a real adjudication is visible only after freeze and is
   admitted under the four source conditions. -/
example :
    ∃ (ledger : RoleLedger Nat Nat Nat Nat Unit Nat)
      (snapshot : AdjudicationSnapshot Nat Nat Nat Nat Nat 7)
      (valid : ValidTrace ledger snapshot),
      AdmissibleJudge ledger snapshot valid 0 := by
  let filtration : EvidenceFiltration Nat Nat :=
    { seen := fun i => if i < 8 then ∅ else {0}
      monotone := by
        intro i j hij
        by_cases hi : i < 8
        · by_cases hj : j < 8 <;> simp [hi, hj]
        · by_cases hj : j < 8
          · exact False.elim (hi (lt_of_le_of_lt hij hj))
          · simp [hi, hj] }
  let event : UseEvent Nat Nat Nat Nat Unit Nat :=
    { eventId := 8, evidence := 0, round := 7, role := .adjudicate,
      dependencies := ∅, protocol := (), usedAt := 8 }
  let ledger : RoleLedger Nat Nat Nat Nat Unit Nat :=
    { events := [event]
      uniqueEventIds := by simp [event]
      strictEventOrder := by simp
      indexRespectsRound := by
        intro e e' he he' h
        simp_all [event]
      indexRespectsTime := by
        intro e e' he he' h
        simp_all [event] }
  let snapshot : AdjudicationSnapshot Nat Nat Nat Nat Nat 7 :=
    { freezeEvent := 3, decisionEvent := 10, frozenAt := 3, decidedAt := 10,
      freezeBeforeDecision := by decide, timeBeforeDecision := by decide,
      filtration := filtration, dependencyClosure := ∅, evidenceDependencies := ∅ }
  have valid : ValidTrace ledger snapshot := by
    intro e he
    have eventEq : e = event := by simpa [ledger] using he
    subst e
    change (0 : Nat) ∈ ({0} : Set Nat)
    exact Set.mem_singleton 0
  refine ⟨ledger, snapshot, valid, ?_⟩
  simp [AdmissibleJudge, RolesAt, InAdjudicationPrefix, RolePrefixAtEvent,
    RolePrefixAtRound, RolePrefixAtTime, AdaptiveUseInClosure, snapshot,
    ledger, event, filtration]

/- Nonanticipation witness: the same evidence is nonanticipatory when it is
   first visible after freeze, and becomes false under the single dependency-set
   mutation. -/
example :
    ∃ snapshot : AdjudicationSnapshot Nat Nat Nat Nat Nat 7,
      NonAnticipating snapshot 0 ∧
        ¬ NonAnticipating
          ({ freezeEvent := snapshot.freezeEvent, decisionEvent := snapshot.decisionEvent,
             frozenAt := snapshot.frozenAt, decidedAt := snapshot.decidedAt,
             freezeBeforeDecision := snapshot.freezeBeforeDecision,
             timeBeforeDecision := snapshot.timeBeforeDecision,
             filtration := snapshot.filtration,
             dependencyClosure := snapshot.dependencyClosure,
             evidenceDependencies := ({0} : Set Nat) } :
            AdjudicationSnapshot Nat Nat Nat Nat Nat 7) 0 := by
  let filtration : EvidenceFiltration Nat Nat :=
    { seen := fun i => if i < 8 then ∅ else {0}
      monotone := by
        intro i j hij
        by_cases hi : i < 8
        · by_cases hj : j < 8 <;> simp [hi, hj]
        · by_cases hj : j < 8
          · exact False.elim (hi (lt_of_le_of_lt hij hj))
          · simp [hi, hj] }
  let snapshot : AdjudicationSnapshot Nat Nat Nat Nat Nat 7 :=
    { freezeEvent := 3, decisionEvent := 10, frozenAt := 3, decidedAt := 10,
      freezeBeforeDecision := by decide, timeBeforeDecision := by decide,
      filtration := filtration, dependencyClosure := ∅, evidenceDependencies := ∅ }
  refine ⟨snapshot, ?_, ?_⟩
  · simp [NonAnticipating, snapshot, filtration]
  · intro nonAnticipating
    exact nonAnticipating.2.2 (by exact Set.mem_singleton 0)

/- Negative witness: a Replicate label without a new observation or explicit
   independent protocol is not an independence certificate. -/
example :
    ∃ event : UseEvent Nat Nat Nat Nat Unit Nat,
      event.role = .replicate ∧
      ¬ ReplicateIndependent event False False := by
  let replicateEvent : UseEvent Nat Nat Nat Nat Unit Nat :=
    { eventId := 1, evidence := 0, round := 0, role := .replicate,
      dependencies := ∅, protocol := (), usedAt := 0 }
  refine ⟨replicateEvent, by simp [replicateEvent], ?_⟩
  simp [ReplicateIndependent]

#print axioms first_seen_is_filtration_derived
#print axioms role_admission_contamination_spec
#print axioms admissible_judge_append_invariant

end D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure
