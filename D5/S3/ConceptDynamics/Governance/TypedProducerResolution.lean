/- GID: D5/S3/ConceptDynamics/Governance/TypedProducerResolution
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/TypedProducerResolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed producer edges require resolved artifact endpoints and fail closed on unresolved actors. -/

/- Library-search audit trail (2026-08-29):
   * Exact searches for `ProducerEdge`, `ResolutionComplete`,
     `AdmissibleProducerGraph`, and typed producer/resolve relations in `D5`
     found no declaration to reuse.
   * Shape searches for graph carriers and unresolved `Option` witnesses found
     only unrelated finite proof graphs and dependency-topology relations; none
     has the producer-actor/artifact boundary of this source atom.
   * The neighboring Governance modules were inspected directly:
     `CommitInterfaceSealPreservation` provides commitment/bundle carriers, and
     `TargetLaunderingCriterion` provides temporal commitment carriers. Neither
     contains a producer-resolution edge or a compatible theorem.
   * Pinned Mathlib v4.31.0 searches found the core `Option.some.injEq` and
     `Option.some_ne_none` discrimination lemmas; no domain-specific theorem
     exists, so the proof uses those kernel-backed facts directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.ConceptDynamics.Governance.TypedProducerResolution

/-- An artifact edge exists only when a producer actor resolves to that artifact. -/
def ProducerEdge
    {Artifact ProducerActor : Type u}
    (producer : Artifact -> Option ProducerActor)
    (resolve : ProducerActor -> Option Artifact)
    (a x : Artifact) : Prop :=
  exists q, producer x = some q /\ resolve q = some a

/-- Every declared producer actor has an artifact endpoint. -/
def ResolutionComplete
    {Artifact ProducerActor : Type u}
    (producer : Artifact -> Option ProducerActor)
    (resolve : ProducerActor -> Option Artifact) : Prop :=
  forall x q, producer x = some q -> exists a, resolve q = some a

/-- A producer graph is exact and admissible only with complete resolution. -/
def AdmissibleProducerGraph
    {Artifact ProducerActor : Type u}
    (producer : Artifact -> Option ProducerActor)
    (resolve : ProducerActor -> Option Artifact)
    (edges : Artifact -> Artifact -> Prop) : Prop :=
  ResolutionComplete producer resolve /\
    forall a x, edges a x <-> ProducerEdge producer resolve a x

/-- A producer actor that resolves to `none` yields no edge and invalidates the
resolution-completeness requirement, so no admissible graph can silently omit it. -/
theorem typed_producer_resolution_fail_closed
    {Artifact ProducerActor : Type u}
    (producer : Artifact -> Option ProducerActor)
    (resolve : ProducerActor -> Option Artifact)
    {x : Artifact} {q : ProducerActor}
    (producer_resolves : producer x = some q)
    (unresolved : resolve q = none) :
    (forall a, Not (ProducerEdge producer resolve a x)) /\
      (Not (ResolutionComplete producer resolve)) /\
      (Not (exists edges : Artifact -> Artifact -> Prop,
        AdmissibleProducerGraph producer resolve edges)) := by
  have no_edge : forall a, Not (ProducerEdge producer resolve a x) := by
    intro a edge
    rcases edge with ⟨q', producer_eq, resolve_eq⟩
    have actor_eq : q' = q := Option.some.inj (producer_eq.symm.trans producer_resolves)
    subst q'
    rw [unresolved] at resolve_eq
    cases resolve_eq
  have incomplete : Not (ResolutionComplete producer resolve) := by
    intro complete
    obtain ⟨a, resolve_eq⟩ := complete x q producer_resolves
    rw [unresolved] at resolve_eq
    cases resolve_eq
  refine ⟨no_edge, incomplete, ?_⟩
  intro admissible
  rcases admissible with ⟨_edges, complete, _exact⟩
  exact incomplete complete

end D5.S3.ConceptDynamics.Governance.TypedProducerResolution
