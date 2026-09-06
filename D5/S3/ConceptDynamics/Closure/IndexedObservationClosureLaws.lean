/- GID: D5/S3/ConceptDynamics/Closure/IndexedObservationClosureLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Closure/IndexedObservationClosureLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Indexed heterogeneous observations induce a closure with redundant added members. -/

import Mathlib.Order.GaloisConnection.Defs
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-09-04):
   * The frozen `jointKernel` and `conceptKernel` definitions already accept a
     dependent output family `Y : ι -> Type` and observations
     `q : forall i, X -> Y i`; they are reused below.
   * Repository searches found only the same-codomain, all-readouts closure in
     `DefinitionKernelGalois`, not a closure relative to an arbitrary indexed
     observation universe.
   * Pinned Mathlib provides `GaloisConnection.le_u_l`, `monotone_l`,
     `monotone_u`, and `u_l_u_eq_u`; no exact theorem packages the five public
     clauses for this indexed carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Closure.IndexedObservationClosureLaws

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- The pairs identified by every observation selected from an indexed
heterogeneous observation universe. -/
def selectedObservationKernel
    {ι : Type u} {X : Type v} {Y : ι -> Type w}
    (q : forall i, X -> Y i) (Gamma : Set ι) : Set (X × X) :=
  jointKernel (fun i : Gamma => q i.1)

/-- The indices of observations that are constant on every pair of a
relation. -/
def invariantObservationIndices
    {ι : Type u} {X : Type v} {Y : ι -> Type w}
    (q : forall i, X -> Y i) (relation : Set (X × X)) : Set ι :=
  {i | relation ⊆ conceptKernel q i}

/-- Closure inside the given indexed observation universe, defined as
`I (K Gamma)`. -/
def indexedObservationClosure
    {ι : Type u} {X : Type v} {Y : ι -> Type w}
    (q : forall i, X -> Y i) (Gamma : Set ι) : Set ι :=
  invariantObservationIndices q (selectedObservationKernel q Gamma)

/-- The selected-family kernel and invariant-index operators form the source's
antitone Galois connection, represented using the order dual of relations. -/
theorem indexedObservationGaloisConnection
    {ι : Type u} {X : Type v} {Y : ι -> Type w}
    (q : forall i, X -> Y i) :
    GaloisConnection
      (fun Gamma : Set ι =>
        OrderDual.toDual (selectedObservationKernel q Gamma))
      (fun relation : OrderDual (Set (X × X)) =>
        invariantObservationIndices q (OrderDual.ofDual relation)) := by
  intro Gamma relation
  change OrderDual.ofDual relation ⊆ selectedObservationKernel q Gamma ↔
    Gamma ⊆ invariantObservationIndices q (OrderDual.ofDual relation)
  constructor
  · intro relationSubset i iInGamma pair pairInRelation
    have pairInKernel := relationSubset pairInRelation
    exact Set.mem_iInter.1 pairInKernel ⟨i, iInGamma⟩
  · intro observationsInvariant pair pairInRelation
    apply Set.mem_iInter.2
    intro i
    have invariant := observationsInvariant i.2
    exact invariant pairInRelation

/-- For an arbitrary indexed universe of observations with heterogeneous
codomains, `Cl = I o K` is extensive, monotone, and idempotent. Every index in
the closure is kernel-redundant: inserting it leaves the selected kernel
unchanged. -/
theorem indexed_observation_closure_laws
    {ι : Type u} {X : Type v} {Y : ι -> Type w}
    (q : forall i, X -> Y i) (Gamma larger : Set ι) :
    indexedObservationClosure q Gamma =
        invariantObservationIndices q (selectedObservationKernel q Gamma) ∧
      Gamma ⊆ indexedObservationClosure q Gamma ∧
      (Gamma ⊆ larger ->
        indexedObservationClosure q Gamma ⊆
          indexedObservationClosure q larger) ∧
      indexedObservationClosure q (indexedObservationClosure q Gamma) =
        indexedObservationClosure q Gamma ∧
      forall i, i ∈ indexedObservationClosure q Gamma ->
        selectedObservationKernel q (Set.insert i Gamma) =
          selectedObservationKernel q Gamma := by
  let kernel := fun family : Set ι =>
    OrderDual.toDual (selectedObservationKernel q family)
  let invariants := fun relation : OrderDual (Set (X × X)) =>
    invariantObservationIndices q (OrderDual.ofDual relation)
  have gc : GaloisConnection kernel invariants :=
    indexedObservationGaloisConnection q
  refine ⟨rfl, gc.le_u_l Gamma, ?_, ?_, ?_⟩
  · intro subset
    exact gc.monotone_u (gc.monotone_l subset)
  · exact gc.u_l_u_eq_u (kernel Gamma)
  · intro i iInClosure
    have insertSubsetClosure : Set.insert i Gamma ⊆ invariants (kernel Gamma) := by
      intro j jInInsert
      rcases jInInsert with rfl | jInGamma
      · exact iInClosure
      · exact gc.le_u_l Gamma jInGamma
    have reverseKernelOrder : kernel (Set.insert i Gamma) ≤ kernel Gamma :=
      (gc (Set.insert i Gamma) (kernel Gamma)).2 insertSubsetClosure
    have forwardKernelOrder : kernel Gamma ≤ kernel (Set.insert i Gamma) :=
      gc.monotone_l (Set.subset_insert i Gamma)
    have kernelEquality : kernel (Set.insert i Gamma) = kernel Gamma :=
      le_antisymm reverseKernelOrder forwardKernelOrder
    exact kernelEquality

#print axioms indexed_observation_closure_laws

end D5.S3.ConceptDynamics.Closure.IndexedObservationClosureLaws
