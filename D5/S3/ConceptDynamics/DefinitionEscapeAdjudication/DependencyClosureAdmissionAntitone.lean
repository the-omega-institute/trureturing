/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/DependencyClosureAdmissionAntitone
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/DependencyClosureAdmissionAntitone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Enlarging the dependency closure can only remove admissible judges. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-26):
   * `rg -n -i 'DependencyClosureAdmissionAntitone|dependency_closure_admission_antitone|
     AdmissibleJudge|AdaptiveUse|ReachesClosure|admission.*antitone|antitone.*admission|
     role admission|contamination closure' D5 --glob '*.lean'` found no adjudication-role,
     reachability, or adaptive-use declaration.  The only broad hit,
     `DomainImmunizationAudit.domain_immunization_audit`, makes complements of
     cumulative counterexample sets antitone; it has no evidence roles,
     provenance reachability, or dependency-touch condition.
   * `rg -n -i 'AdmissibleJudge|AdaptiveUse|ReachesClosure|dependency.*admission|
     admission.*dependency|contamination.*closure'
     .lake/packages/mathlib/Mathlib --glob '*.lean'` returned no hit.
   * Pinned Mathlib supplies the set membership and inclusion primitives used
     below, but no packaged theorem combining both direct and role-mediated
     dependency contamination. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u v

/-- The role under which an evidence record was used before adjudication. -/
inductive EvidenceRole
  | generate
  | tune
  | select
  | adjudicate
  | replicate
  deriving DecidableEq

/-- One event in the role ledger, including every artifact dependency touched
by that use of the evidence record. -/
structure UseEvent (Evidence : Type u) (Artifact : Type v) where
  evidence : Evidence
  role : EvidenceRole
  dependencies : Set Artifact

/-- The data fixed by an adjudication snapshot.  `events` is already restricted
to the snapshot's event, round, and time prefix, and `firstSeenAfterFreeze`
records the source condition that the evidence first appears after freezing. -/
structure AdmissionContext (Evidence : Type u) (Artifact : Type v) where
  events : Set (UseEvent Evidence Artifact)
  firstSeenAfterFreeze : Evidence -> Prop
  reaches : Evidence -> Artifact -> Prop

/-- An evidence record occurs under a specified role in the frozen prefix. -/
def HasRole {Evidence : Type u} {Artifact : Type v}
    (context : AdmissionContext Evidence Artifact)
    (record : Evidence) (role : EvidenceRole) : Prop :=
  exists event, event ∈ context.events ∧
    event.evidence = record ∧ event.role = role

/-- A record reaches the commitment when one of its reachable artifacts lies
in the commitment's reflexive-transitive dependency closure. -/
def ReachesClosure {Evidence : Type u} {Artifact : Type v}
    (context : AdmissionContext Evidence Artifact)
    (closure : Set Artifact) (record : Evidence) : Prop :=
  exists artifact, artifact ∈ closure ∧ context.reaches record artifact

/-- A role event touches the commitment closure when its dependencies have a
nonempty intersection with that closure. -/
def TouchesClosure {Evidence : Type u} {Artifact : Type v}
    (event : UseEvent Evidence Artifact) (closure : Set Artifact) : Prop :=
  Set.Nonempty (event.dependencies ∩ closure)

/-- Adaptive use is a pre-decision Generate, Tune, or Select event for the
record whose dependencies touch the commitment closure. -/
def AdaptiveUse {Evidence : Type u} {Artifact : Type v}
    (context : AdmissionContext Evidence Artifact)
    (closure : Set Artifact) (record : Evidence) : Prop :=
  exists event, event ∈ context.events ∧ event.evidence = record ∧
    (event.role = .generate ∨ event.role = .tune ∨ event.role = .select) ∧
    TouchesClosure event closure

/-- A record is an admissible judge exactly when it has the adjudication role,
was first seen after the freeze, and is free of both direct and adaptive-use
dependency contamination. -/
def AdmissibleJudge {Evidence : Type u} {Artifact : Type v}
    (context : AdmissionContext Evidence Artifact)
    (closure : Set Artifact) (record : Evidence) : Prop :=
  HasRole context record .adjudicate ∧
    context.firstSeenAfterFreeze record ∧
    ¬ ReachesClosure context closure record ∧
    ¬ AdaptiveUse context closure record

private theorem reachesClosure_mono
    {Evidence : Type u} {Artifact : Type v}
    {context : AdmissionContext Evidence Artifact}
    {oldClosure newClosure : Set Artifact}
    (included : oldClosure ⊆ newClosure) {record : Evidence} :
    ReachesClosure context oldClosure record ->
      ReachesClosure context newClosure record := by
  rintro ⟨artifact, inOld, reachable⟩
  exact ⟨artifact, included inOld, reachable⟩

private theorem adaptiveUse_mono
    {Evidence : Type u} {Artifact : Type v}
    {context : AdmissionContext Evidence Artifact}
    {oldClosure newClosure : Set Artifact}
    (included : oldClosure ⊆ newClosure) {record : Evidence} :
    AdaptiveUse context oldClosure record ->
      AdaptiveUse context newClosure record := by
  rintro ⟨event, inEvents, sameRecord, adaptiveRole,
    artifact, inDependencies, inOld⟩
  exact ⟨event, inEvents, sameRecord, adaptiveRole,
    artifact, inDependencies, included inOld⟩

/-- Enlarging the dependency closure can only disqualify evidence: every judge
admissible against the larger closure remains admissible against the smaller
one.  Both direct reachability and adaptive-use contamination are transported
along the same closure inclusion. -/
theorem dependency_closure_admission_antitone
    {Evidence : Type u} {Artifact : Type v}
    (context : AdmissionContext Evidence Artifact)
    {oldClosure newClosure : Set Artifact}
    (included : oldClosure ⊆ newClosure) :
    forall record, AdmissibleJudge context newClosure record ->
      AdmissibleJudge context oldClosure record := by
  rintro record ⟨hasRole, seenAfterFreeze, notReachable, notAdaptive⟩
  exact ⟨hasRole, seenAfterFreeze,
    fun reachesOld => notReachable (reachesClosure_mono included reachesOld),
    fun adaptiveOld => notAdaptive (adaptiveUse_mono included adaptiveOld)⟩

/-- The theorem's hypotheses are jointly satisfiable on inhabited finite
types: one uncontaminated adjudication event is admitted at the empty closure. -/
example :
    exists context : AdmissionContext Bool Bool,
      (∅ : Set Bool) ⊆ ∅ ∧ AdmissibleJudge context ∅ true := by
  let judgeEvent : UseEvent Bool Bool :=
    { evidence := true
      role := .adjudicate
      dependencies := ∅ }
  let context : AdmissionContext Bool Bool :=
    { events := {judgeEvent}
      firstSeenAfterFreeze := fun _ => True
      reaches := fun _ _ => False }
  refine ⟨context, Set.Subset.rfl, ?_⟩
  simp [AdmissibleJudge, HasRole, ReachesClosure, AdaptiveUse,
    TouchesClosure, context, judgeEvent]

/-- Antitonicity can be strict: adding one reachable artifact to the closure
disqualifies a judge that was admitted against the empty closure. -/
example :
    exists context : AdmissionContext Bool Bool,
      AdmissibleJudge context ∅ true ∧
        ¬ AdmissibleJudge context {true} true := by
  let judgeEvent : UseEvent Bool Bool :=
    { evidence := true
      role := .adjudicate
      dependencies := ∅ }
  let context : AdmissionContext Bool Bool :=
    { events := {judgeEvent}
      firstSeenAfterFreeze := fun _ => True
      reaches := fun evidence artifact => evidence = artifact }
  refine ⟨context, ?_, ?_⟩
  · simp [AdmissibleJudge, HasRole, ReachesClosure, AdaptiveUse,
      TouchesClosure, context, judgeEvent]
  · intro admitted
    exact admitted.2.2.1 ⟨true, by simp, rfl⟩

#print axioms dependency_closure_admission_antitone

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
