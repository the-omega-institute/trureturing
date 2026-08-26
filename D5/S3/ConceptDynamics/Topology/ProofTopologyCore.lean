/- GID: D5/S3/ConceptDynamics/Topology/ProofTopologyCore
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/ProofTopologyCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Frozen dependency APIs support finite bases, order simplices, and certificate gluing. -/

import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
import D5.S3.ConceptDynamics.DependencyTopology.AlexandrovDependencyTopology
import D5.S3.ConceptDynamics.DependencyTopology.DepthClosedFiltration
import D5.S3.ConceptDynamics.DependencyTopology.AxiomClosureMonotonicity
import D5.S3.ConceptDynamics.DependencyTopology.DominatorCut
import D5.S3.ConceptDynamics.DependencyTopology.AlexandrovMonotoneContinuity
import Mathlib.Topology.Order.UpperLowerSetTopology
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Pairwise

/- Library-search audit trail (2026-08-25):
   * The frozen DependencyTopology batch supplies the canonical reachability,
     Alexandrov, depth, label-monotonicity, continuity, and dominator-cut APIs;
     the duplicate PR declarations were deleted and their uses rewired here.
   * Pinned Mathlib supplies the relation generators, principal filters, order
     simplices, and finite-set lattice operations, but no cross-carrier map theorem.
   * No frozen counterpart was found for the finite-release/Scott-open,
     order-simplex, or certificate-system blocks retained below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Topology.ProofTopologyCore

open Set TopologicalSpace Filter
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
open D5.S3.ConceptDynamics.DependencyTopology.AlexandrovDependencyTopology
open D5.S3.ConceptDynamics.DependencyTopology.AlexandrovMonotoneContinuity

universe u v w

/-- An edge-preserving map transports frozen strict reachability. -/
theorem strictReachable_map {V : Type u} {W : Type v}
    {edgeV : V -> V -> Prop} {edgeW : W -> W -> Prop}
    (map : V -> W)
    (preserves : RelationMonotone edgeV edgeW map)
    {source target : V} (path : StrictReachable edgeV source target) :
    StrictReachable edgeW (map source) (map target) := by
  induction path with
  | single edgeStep => exact .single (preserves edgeStep)
  | tail previous edgeStep inductionHypothesis =>
      exact .tail inductionHypothesis (preserves edgeStep)

namespace Reachable

/-- An edge-preserving map transports frozen reflexive reachability. -/
theorem map {V : Type u} {W : Type v}
    {edgeV : V -> V -> Prop} {edgeW : W -> W -> Prop}
    (f : V -> W)
    (preserves : RelationMonotone edgeV edgeW f)
    {source target : V} (path : Reachable edgeV source target) :
    Reachable edgeW (f source) (f target) := by
  induction path with
  | refl => exact .refl
  | tail previous edgeStep inductionHypothesis =>
      exact .tail inductionHypothesis (preserves edgeStep)

end Reachable

/-- Direct-edge monotonicity induces monotonicity of frozen reachability. -/
theorem conservative_map_preserves_reachability
    {V : Type u} {W : Type v}
    {edgeV : V -> V -> Prop} {edgeW : W -> W -> Prop}
    {map : V -> W} (preserves : RelationMonotone edgeV edgeW map) :
    RelationMonotone (Reachable edgeV) (Reachable edgeW) map :=
  fun ⦃_ _⦄ reachable => Reachable.map map preserves reachable

/-- The principal downstream upset is the least dependency neighbourhood. -/
theorem dependencyTopology_nhds_eq_impact_filter
    {V : Type u} (edge : V -> V -> Prop) (node : V) :
    @nhds V (dependencyTopology edge) node =
      Filter.principal (upset (Reachable edge) node) := by
  letI : TopologicalSpace V := dependencyTopology edge
  ext states
  constructor
  · intro statesInNhds
    rcases mem_nhds_iff.mp statesInNhds with
      ⟨openStates, openStatesSubset, openStatesOpen, nodeInOpenStates⟩
    change upset (Reachable edge) node ⊆ states
    exact (upset_minimal_open (Reachable edge) openStatesOpen nodeInOpenStates).trans
      openStatesSubset
  · intro impactSubset
    change upset (Reachable edge) node ⊆ states at impactSubset
    exact mem_nhds_iff.mpr
      ⟨upset (Reachable edge) node, impactSubset,
        upset_isOpen (Reachable edge) node, reachable_refl edge node⟩

/-- Finite approximations of a release are finite subsets of that release. -/
def FiniteApproximation {V : Type u} (release : Set V) :=
  {vertices : Finset V // (vertices : Set V) ⊆ release}

/-- Every released vertex already appears in a singleton finite approximation. -/
theorem finiteApproximation_contains
    {V : Type u} [DecidableEq V] {release : Set V} {vertex : V}
    (released : vertex ∈ release) :
    ∃ approximation : FiniteApproximation release,
      vertex ∈ approximation.1 := by
  refine ⟨⟨{vertex}, ?_⟩, by simp⟩
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_singleton] at hx
  simpa [hx] using released

/-- Two finite approximations have a common finite upper bound given by union. -/
theorem finiteApproximations_directed
    {V : Type u} [DecidableEq V] {release : Set V}
    (left right : FiniteApproximation release) :
    ∃ upper : FiniteApproximation release,
      (left.1 : Set V) ⊆ upper.1 ∧ (right.1 : Set V) ⊆ upper.1 := by
  refine ⟨⟨left.1 ∪ right.1, ?_⟩, ?_, ?_⟩
  · intro vertex membership
    simp only [Finset.mem_coe, Finset.mem_union] at membership
    rcases membership with membership | membership
    · exact left.2 membership
    · exact right.2 membership
  · intro vertex membership
    exact Finset.mem_union_left right.1 membership
  · intro vertex membership
    exact Finset.mem_union_right left.1 membership

/-- A directed family of releases is nonempty and has an upper member for every pair. -/
def DirectedReleaseFamily {V : Type u} (family : Set (Set V)) : Prop :=
  family.Nonempty ∧
    forall left, left ∈ family -> forall right, right ∈ family ->
      ∃ upper, upper ∈ family ∧ left ⊆ upper ∧ right ⊆ upper

/-- Every finite subset of a directed union is already contained in one family member. -/
theorem finite_subset_of_directed_sUnion
    {V : Type u} [DecidableEq V] {family : Set (Set V)}
    (directed : DirectedReleaseFamily family)
    (seed : Finset V) (contained : (seed : Set V) ⊆ ⋃₀ family) :
    ∃ release ∈ family, (seed : Set V) ⊆ release := by
  classical
  induction seed using Finset.induction_on with
  | empty =>
      rcases directed.1 with ⟨release, releaseInFamily⟩
      exact ⟨release, releaseInFamily, by simp⟩
  | @insert vertex rest vertexFresh ih =>
      have restContained : (rest : Set V) ⊆ ⋃₀ family := by
        intro x hx
        exact contained (by simp [hx])
      rcases ih restContained with ⟨restRelease, restInFamily, restSubset⟩
      have vertexInUnion : vertex ∈ ⋃₀ family :=
        contained (by simp)
      rcases Set.mem_sUnion.1 vertexInUnion with
        ⟨vertexRelease, vertexInFamily, vertexInRelease⟩
      rcases directed.2 restRelease restInFamily vertexRelease vertexInFamily with
        ⟨upper, upperInFamily, restUpper, vertexUpper⟩
      refine ⟨upper, upperInFamily, ?_⟩
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact vertexUpper vertexInRelease
      · exact restUpper (restSubset hx)

/-- A Scott-open property on the powerset release order. -/
def PowersetScottOpen {V : Type u} (openSet : Set (Set V)) : Prop :=
  IsUpperSet openSet ∧
    forall family : Set (Set V), DirectedReleaseFamily family ->
      ⋃₀ family ∈ openSet -> ∃ release ∈ family, release ∈ openSet

/-- Requiring a fixed finite certificate set is a Scott-open release property. -/
theorem finiteSupport_scottOpen
    {V : Type u} [DecidableEq V] (seed : Finset V) :
    PowersetScottOpen {release : Set V | (seed : Set V) ⊆ release} := by
  constructor
  · intro smaller larger inclusion seedInSmaller
    change smaller ⊆ larger at inclusion
    change (seed : Set V) ⊆ smaller at seedInSmaller
    change (seed : Set V) ⊆ larger
    exact seedInSmaller.trans inclusion
  · intro family directed unionContainsSeed
    rcases finite_subset_of_directed_sUnion directed seed unionContainsSeed with
      ⟨release, releaseInFamily, seedInRelease⟩
    exact ⟨release, releaseInFamily, seedInRelease⟩

/-- An order simplex is an indexed strictly increasing chain. -/
def IsOrderSimplex {Index : Type u} {Vertex : Type v}
    [Preorder Index] [Preorder Vertex] (vertices : Index -> Vertex) : Prop :=
  StrictMono vertices

/-- Order embeddings preserve all order simplices. -/
theorem orderEmbedding_preserves_simplex
    {Index : Type u} {Vertex : Type v} {Target : Type w}
    [Preorder Index] [Preorder Vertex] [Preorder Target]
    (embedding : Vertex ↪o Target) (vertices : Index -> Vertex)
    (simplex : IsOrderSimplex vertices) :
    IsOrderSimplex (embedding ∘ vertices) := by
  intro first second earlier
  exact embedding.lt_iff_lt.mpr (simplex earlier)

/-- Abstract local certificates over an index family. -/
structure CertificateSystem (Index : Type u) where
  Global : Type v
  Local : Index -> Type w
  restrict : forall index, Global -> Local index

namespace CertificateSystem

variable {Index : Type u} (system : CertificateSystem Index)

/-- The complete local readout of one global certificate. -/
def jointRestriction : system.Global -> forall index, system.Local index :=
  fun global index => system.restrict index global

/-- A family covers global certificates when all local restrictions are jointly faithful. -/
def Covers : Prop :=
  Function.Injective system.jointRestriction

/-- A local family is realizable when it is the restriction of a global certificate. -/
def Realizable (localFamily : forall index, system.Local index) : Prop :=
  ∃ global, forall index, system.restrict index global = localFamily index

/-- Coverage supplies uniqueness, while realizability supplies existence, of a gluing. -/
theorem unique_gluing_of_cover
    (covers : system.Covers)
    {localFamily : forall index, system.Local index}
    (realizable : system.Realizable localFamily) :
    ∃! global, forall index, system.restrict index global = localFamily index := by
  rcases realizable with ⟨global, localEq⟩
  refine ⟨global, localEq, ?_⟩
  intro candidate candidateEq
  apply covers
  funext index
  exact (candidateEq index).trans (localEq index).symm

end CertificateSystem

#print axioms strictReachable_map
#print axioms dependencyTopology_nhds_eq_impact_filter
#print axioms finiteApproximations_directed
#print axioms finiteSupport_scottOpen
#print axioms CertificateSystem.unique_gluing_of_cover

end D5.S3.ConceptDynamics.Topology.ProofTopologyCore
