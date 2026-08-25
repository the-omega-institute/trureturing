/- GID: D5/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/RoleAdmissionContaminationClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Late ledger events preserve snapshot-bounded admission and provenance exclusions. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

/- Library-search audit trail (2026-08-25):
   * `rg -n -i 'RoleEvent|role event|role.*ledger|ledger.*role|AdaptiveUse|RolesUpTo|FirstSeen|freezePoint|adjudicationPoint|adjudicat|Generate|Tune|Select' D5/S0/History D5/S1/Ledger D5/S3/ConceptDynamics --glob '*.lean'`
     found no role-event ledger, snapshot-bounded role set, adaptive-use predicate,
     or judge-admission theorem. `HistoryCarrier.Event` is an opcode event and
     `LedgerLimit.LedgerHistory` is a time-indexed grading; neither has the
     evidence, role, dependency, round, or adjudication-point fields used here.
   * `rg -n '(List \([^)]*Event|List [A-Za-z0-9_.]*Event|: Set [A-Za-z][A-Za-z0-9_]*|Relation\.ReflTransGen)' D5/S0/History D5/S1/Ledger D5/S3/ConceptDynamics --glob '*.lean' --glob '!RoleAdmissionContaminationClosure.lean' | head -160`
     checked the declaration shapes independently of the new names. It found
     statement and revision-time sets in `LedgerLimit` and the permission-indexed
     forward `Reach` set in `AttackSurfaceMonotonicity`, but no event list with
     role dependencies or predecessor closure toward a frozen commitment.
   * `rg -n -i 'AdmissibleJudge|admissible.*judge|contam|taint|pollut|provenance.*closure|source.*closure' D5/S0/History D5/S1/Ledger D5/S3/ConceptDynamics --glob '*.lean'`
     found no contamination closure or matching admission predicate.
     `ProvenanceAdmissionCountermodel` concerns validation of a content report,
     not graph reachability, access time, or a cutoff-filtered role ledger.
   * `rg -n -i 'Relation\.ReflTransGen|reachab(le|ility)|dependency.*closure|closure.*dependency' D5 --glob '*.lean'`
     found `Interventions.AttackSurfaceMonotonicity.Reach`, whose relation is
     permission-indexed forward reachability from a start state. It does not
     express the predecessor closure of a frozen commitment. No local wrapper is
     reused; the exact pinned primitive `Relation.ReflTransGen` is used directly.
   * `git grep -n -E '^def |^  def |^structure |^inductive |^abbrev |^theorem ' -- D5/S0/History D5/S1/Ledger | head -120`
     confirmed the neighboring vocabulary above and no exact domain declaration.
   * `rg -n 'inductive ReflTransGen|namespace ReflTransGen|ReflTransGen\.trans' .lake/packages/mathlib/Mathlib/Logic/Relation.lean`
     found mathlib's documented reflexive-transitive closure and its `refl`,
     `single`, and `trans` constructors. `List.mem_append` is provided by pinned
     `Mathlib.Data.List.Basic` and is reused for cutoff-preserving append proofs.
   * English synonyms checked: reachable/reachability/dependency closure,
     admission/eligibility/judge, contamination/taint/pollution/provenance, and
     role/adaptive use/ledger. Chinese synonyms checked with
     `rg -n '可达|可及|依赖|闭包|角色|准入|适应性|污染|账本|裁决|冻结|首次出现|来源图|主观记忆' D5 --glob '*.lean'`;
     no exact declaration was found.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure

/-- Roles recorded by the role ledger. Only the first three are adaptive uses. -/
inductive Role where
  | generate
  | tune
  | select
  | adjudicate
  deriving DecidableEq, Repr

/-- The round and both cutoffs are fields of the frozen commitment snapshot. -/
structure FrozenCommitment (Artifact : Type*) where
  commitment : Artifact
  round : Nat
  freezePoint : Nat
  adjudicationPoint : Nat

/-- A role event carries its ledger number, evidence, role, round, and dependencies. -/
structure RoleEvent (Artifact : Type*) where
  eventNumber : Nat
  evidence : Artifact
  role : Role
  round : Nat
  dependencies : Set Artifact

/-- The three adaptive roles, deliberately excluding adjudication. -/
def adaptiveRoles : Set Role
  | .generate => True
  | .tune => True
  | .select => True
  | .adjudicate => False

/-- The reflexive-transitive predecessor closure of an artifact. -/
def dependencyClosure {Artifact : Type*}
    (dependsOn : Artifact -> Artifact -> Prop) (target : Artifact) : Set Artifact :=
  {source | Relation.ReflTransGen dependsOn source target}

/-- Roles for evidence and a round, using only events at or before the cutoff. -/
def rolesUpTo {Artifact : Type*} (ledger : List (RoleEvent Artifact))
    (cutoff : Nat) (evidence : Artifact) (round : Nat) : Set Role :=
  {role | ∃ event ∈ ledger,
    event.eventNumber <= cutoff ∧
      event.evidence = evidence ∧ event.round = round ∧ event.role = role}

/-- An adaptive use is a cutoff-visible adaptive-role event whose dependencies
meet the frozen commitment's dependency closure. -/
def AdaptiveUse {Artifact : Type*} (dependsOn : Artifact -> Artifact -> Prop)
    (ledger : List (RoleEvent Artifact)) (evidence : Artifact)
    (snapshot : FrozenCommitment Artifact) : Prop :=
  ∃ event ∈ ledger,
    event.eventNumber <= snapshot.adjudicationPoint ∧
      event.evidence = evidence ∧
        event.role ∈ adaptiveRoles ∧
          (event.dependencies ∩
            dependencyClosure dependsOn snapshot.commitment).Nonempty

/-- Judge admission is the source's four-part condition. All round and cutoff
values are projected from `snapshot`; callers cannot supply independent values. -/
def AdmissibleJudge {Artifact : Type*} (dependsOn : Artifact -> Artifact -> Prop)
    (firstSeen : Artifact -> Nat) (ledger : List (RoleEvent Artifact))
    (evidence : Artifact) (snapshot : FrozenCommitment Artifact) : Prop :=
  Role.adjudicate ∈
      rolesUpTo ledger snapshot.adjudicationPoint evidence snapshot.round ∧
    snapshot.freezePoint < firstSeen evidence ∧
    evidence ∉ dependencyClosure dependsOn snapshot.commitment ∧
    ¬ AdaptiveUse dependsOn ledger evidence snapshot

/-- The contamination closure of a record set consists of all artifacts
reachable from at least one record in the set. -/
def Contam {Artifact : Type*} (dependsOn : Artifact -> Artifact -> Prop)
    (records : Set Artifact) : Set Artifact :=
  {artifact | ∃ record ∈ records,
    Relation.ReflTransGen dependsOn record artifact}

/-- The judge set is nonanticipatory exactly when its contamination closure is
disjoint from the commitment closure and every judge is first seen after freeze. -/
def Nonanticipatory {Artifact : Type*} (dependsOn : Artifact -> Artifact -> Prop)
    (firstSeen : Artifact -> Nat) (snapshot : FrozenCommitment Artifact)
    (judges : Set Artifact) : Prop :=
  Contam dependsOn judges ∩ dependencyClosure dependsOn snapshot.commitment = ∅ ∧
    ∀ judge ∈ judges, snapshot.freezePoint < firstSeen judge

/-- The definitions jointly realize reflexive-transitive dependence, the exact
three adaptive roles, four-part admission, contamination, and nonanticipation.
The final conjunct states that hiding the original record cannot restore
admission when any artifact derived from it reaches the frozen commitment. -/
theorem role_admission_contamination_spec
    {Artifact : Type*} (dependsOn : Artifact -> Artifact -> Prop)
    (firstSeen : Artifact -> Nat) (ledger : List (RoleEvent Artifact))
    (snapshot : FrozenCommitment Artifact) :
    (∀ source,
      source ∈ dependencyClosure dependsOn snapshot.commitment ↔
        Relation.ReflTransGen dependsOn source snapshot.commitment) ∧
    (∀ evidence,
      AdaptiveUse dependsOn ledger evidence snapshot ↔
        ∃ event ∈ ledger,
          event.eventNumber <= snapshot.adjudicationPoint ∧
            event.evidence = evidence ∧
              event.role ∈ adaptiveRoles ∧
                (event.dependencies ∩
                  dependencyClosure dependsOn snapshot.commitment).Nonempty) ∧
    (∀ evidence,
      AdmissibleJudge dependsOn firstSeen ledger evidence snapshot ↔
        Role.adjudicate ∈
            rolesUpTo ledger snapshot.adjudicationPoint evidence snapshot.round ∧
          snapshot.freezePoint < firstSeen evidence ∧
          evidence ∉ dependencyClosure dependsOn snapshot.commitment ∧
          ¬ AdaptiveUse dependsOn ledger evidence snapshot) ∧
    (∀ records artifact,
      artifact ∈ Contam dependsOn records ↔
        ∃ record ∈ records,
          Relation.ReflTransGen dependsOn record artifact) ∧
    (∀ judges,
      Nonanticipatory dependsOn firstSeen snapshot judges ↔
        Contam dependsOn judges ∩
            dependencyClosure dependsOn snapshot.commitment = ∅ ∧
          ∀ judge ∈ judges, snapshot.freezePoint < firstSeen judge) ∧
    (Role.generate ∈ adaptiveRoles ∧ Role.tune ∈ adaptiveRoles ∧
      Role.select ∈ adaptiveRoles ∧ Role.adjudicate ∉ adaptiveRoles) ∧
    (∀ evidence,
      (Contam dependsOn {evidence} ∩
          dependencyClosure dependsOn snapshot.commitment).Nonempty ->
        ¬ AdmissibleJudge dependsOn firstSeen ledger evidence snapshot) := by
  refine ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ => Iff.rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change True
      trivial
    · change True
      trivial
    · change True
      trivial
    · change ¬ False
      simp
  · intro evidence contaminated admitted
    rcases contaminated with ⟨artifact, derived, reachesCommitment⟩
    rcases derived with ⟨record, recordIsEvidence, reachesArtifact⟩
    have recordEq : record = evidence := by
      change record = evidence at recordIsEvidence
      exact recordIsEvidence
    subst record
    exact admitted.2.2.1 (reachesArtifact.trans reachesCommitment)

private theorem exists_up_to_append_late
    {Artifact : Type*} {ledger delta : List (RoleEvent Artifact)}
    {cutoff : Nat} {predicate : RoleEvent Artifact -> Prop}
    (late : ∀ event ∈ delta, cutoff < event.eventNumber) :
    (∃ event ∈ ledger ++ delta,
      event.eventNumber <= cutoff ∧ predicate event) ↔
      ∃ event ∈ ledger, event.eventNumber <= cutoff ∧ predicate event := by
  constructor
  · rintro ⟨event, inAppend, beforeCutoff, satisfies⟩
    rcases List.mem_append.mp inAppend with inLedger | inDelta
    · exact ⟨event, inLedger, beforeCutoff, satisfies⟩
    · exact False.elim ((Nat.not_lt_of_ge beforeCutoff) (late event inDelta))
  · rintro ⟨event, inLedger, beforeCutoff, satisfies⟩
    exact ⟨event, List.mem_append_left delta inLedger, beforeCutoff, satisfies⟩

private theorem roles_up_to_append_late
    {Artifact : Type*} {ledger delta : List (RoleEvent Artifact)}
    {cutoff : Nat} {evidence : Artifact} {round : Nat}
    (late : ∀ event ∈ delta, cutoff < event.eventNumber) :
    rolesUpTo (ledger ++ delta) cutoff evidence round =
      rolesUpTo ledger cutoff evidence round := by
  ext role
  exact exists_up_to_append_late late

private theorem adaptive_use_append_late
    {Artifact : Type*} (dependsOn : Artifact -> Artifact -> Prop)
    {ledger delta : List (RoleEvent Artifact)} {evidence : Artifact}
    {snapshot : FrozenCommitment Artifact}
    (late : ∀ event ∈ delta,
      snapshot.adjudicationPoint < event.eventNumber) :
    AdaptiveUse dependsOn (ledger ++ delta) evidence snapshot ↔
      AdaptiveUse dependsOn ledger evidence snapshot := by
  exact exists_up_to_append_late late

private theorem admissible_judge_append_late
    {Artifact : Type*} (dependsOn : Artifact -> Artifact -> Prop)
    (firstSeen : Artifact -> Nat) {ledger delta : List (RoleEvent Artifact)}
    (evidence : Artifact) (snapshot : FrozenCommitment Artifact)
    (late : ∀ event ∈ delta,
      snapshot.adjudicationPoint < event.eventNumber) :
    AdmissibleJudge dependsOn firstSeen (ledger ++ delta) evidence snapshot ↔
      AdmissibleJudge dependsOn firstSeen ledger evidence snapshot := by
  unfold AdmissibleJudge
  rw [roles_up_to_append_late late, adaptive_use_append_late dependsOn late]

/-- Snapshot-bounded admission is unchanged by arbitrary later events. The last
two conjuncts expose Tune and Adjudicate appends as explicit non-flipping cases. -/
theorem admissible_judge_append_invariant
    {Artifact : Type*} (dependsOn : Artifact -> Artifact -> Prop)
    (firstSeen : Artifact -> Nat) (ledger delta : List (RoleEvent Artifact))
    (snapshot : FrozenCommitment Artifact) :
    ((∀ event ∈ delta,
        snapshot.adjudicationPoint < event.eventNumber) ->
      ∀ evidence,
        AdmissibleJudge dependsOn firstSeen (ledger ++ delta) evidence snapshot ↔
          AdmissibleJudge dependsOn firstSeen ledger evidence snapshot) ∧
    (∀ event evidence,
      event.role = Role.tune ->
        snapshot.adjudicationPoint < event.eventNumber ->
          (AdmissibleJudge dependsOn firstSeen (ledger ++ [event]) evidence snapshot ↔
            AdmissibleJudge dependsOn firstSeen ledger evidence snapshot)) ∧
    (∀ event evidence,
      event.role = Role.adjudicate ->
        snapshot.adjudicationPoint < event.eventNumber ->
          (AdmissibleJudge dependsOn firstSeen (ledger ++ [event]) evidence snapshot ↔
            AdmissibleJudge dependsOn firstSeen ledger evidence snapshot)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro late evidence
    exact admissible_judge_append_late dependsOn firstSeen evidence snapshot late
  · intro event evidence _roleIsTune eventIsLate
    apply admissible_judge_append_late dependsOn firstSeen evidence snapshot
    simpa using eventIsLate
  · intro event evidence _roleIsAdjudicate eventIsLate
    apply admissible_judge_append_late dependsOn firstSeen evidence snapshot
    simpa using eventIsLate

/- Positive control: a real adjudication is admitted, and appending a Tune event
after the snapshot cutoff leaves that nontrivial admission true. -/
example :
    let snapshot : FrozenCommitment (Fin 3) :=
      { commitment := 2, round := 7, freezePoint := 3, adjudicationPoint := 10 }
    let judgeEvent : RoleEvent (Fin 3) :=
      { eventNumber := 8, evidence := 0, role := .adjudicate,
        round := 7, dependencies := ∅ }
    let futureTune : RoleEvent (Fin 3) :=
      { eventNumber := 11, evidence := 0, role := .tune,
        round := 7, dependencies := fun artifact => artifact = 2 }
    AdmissibleJudge (fun _ _ => False) (fun _ => 4) [judgeEvent] 0 snapshot ∧
      AdmissibleJudge (fun _ _ => False) (fun _ => 4)
        ([judgeEvent] ++ [futureTune]) 0 snapshot := by
  dsimp
  have notReachable :
      ¬ Relation.ReflTransGen (fun _ _ : Fin 3 => False) 0 2 := by
    rw [Relation.reflTransGen_iff_eq]
    · decide
    · simp
  simp [AdmissibleJudge, rolesUpTo, AdaptiveUse,
    dependencyClosure, notReachable]

/- Negative control: without the strict-later premise, an appended cutoff-visible
Tune event that touches the commitment closure flips admission from true to false. -/
example :
    let snapshot : FrozenCommitment (Fin 3) :=
      { commitment := 2, round := 7, freezePoint := 3, adjudicationPoint := 10 }
    let judgeEvent : RoleEvent (Fin 3) :=
      { eventNumber := 8, evidence := 0, role := .adjudicate,
        round := 7, dependencies := ∅ }
    let cutoffTune : RoleEvent (Fin 3) :=
      { eventNumber := 10, evidence := 0, role := .tune,
        round := 7, dependencies := fun artifact => artifact = 2 }
    AdmissibleJudge (fun _ _ => False) (fun _ => 4) [judgeEvent] 0 snapshot ∧
      ¬ AdmissibleJudge (fun _ _ => False) (fun _ => 4)
        ([judgeEvent] ++ [cutoffTune]) 0 snapshot := by
  dsimp
  have notReachable :
      ¬ Relation.ReflTransGen (fun _ _ : Fin 3 => False) 0 2 := by
    rw [Relation.reflTransGen_iff_eq]
    · decide
    · simp
  constructor
  · simp [AdmissibleJudge, rolesUpTo, AdaptiveUse,
      dependencyClosure, notReachable]
  · intro admitted
    exact admitted.2.2.2 ⟨
      { eventNumber := 10, evidence := 0, role := .tune,
        round := 7, dependencies := fun artifact => artifact = 2 },
      by simp, by simp, by simp,
      by change True; trivial,
      2, by rfl, Relation.ReflTransGen.refl⟩

#print axioms role_admission_contamination_spec
#print axioms admissible_judge_append_invariant

end D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure
