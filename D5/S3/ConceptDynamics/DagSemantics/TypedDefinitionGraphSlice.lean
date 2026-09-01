/- GID: D5/S3/ConceptDynamics/DagSemantics/TypedDefinitionGraphSlice
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/TypedDefinitionGraphSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed graphs have dependency slices, joint kernels, and a strict witness. -/

import D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-09-01):
   * `PrerequisiteClosure.prerequisiteClosure` is the canonical current-tree
     predecessor slice, built from reflexive-transitive dependency reachability;
     it is imported rather than redeclared.
   * `JointFaithfulnessLeibnizCriterion.jointReadout` and `jointKernel` are the
     canonical dependent readout and intersection of member kernels.
   * Pinned Mathlib supplies `Relation.ReflTransGen`, `Setoid.ker`, and
     `Set.ssubset_iff_exists`; no parallel reachability or kernel is introduced.
   * Searches found no current-tree typed definition graph, scientific-state
     package, or concrete witness that a dependency slice can strictly expand. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.TypedDefinitionGraphSlice

open D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w x y z

/-- A typed definition graph with dependency edges, intensional readouts, and node ledgers. -/
structure TypedDefinitionGraph
    (Node : Type u) (Input : Type v) (NodeLedger : Type w) where
  edge : Node → Node → Prop
  nodeType : Node → Type x
  intension : ∀ node, Input → nodeType node
  ledger : Node → NodeLedger

/-- The dependency slice contains every node that can reach one of the targets. -/
def dependencySlice
    {Node : Type u} {Input : Type v} {NodeLedger : Type w}
    (graph : TypedDefinitionGraph Node Input NodeLedger) (targets : Set Node) : Set Node :=
  prerequisiteClosure graph.edge targets

/-- The dependent product of the intensional readouts at the active nodes. -/
def activeReadout
    {Node : Type u} {Input : Type v} {NodeLedger : Type w}
    (graph : TypedDefinitionGraph Node Input NodeLedger) (active : Set Node) :
    Input → ((node : active) → graph.nodeType node.1) :=
  jointReadout (fun node : active ↦ graph.intension node.1)

/-- The intersection of the kernels of all active intensional readouts. -/
def activeKernel
    {Node : Type u} {Input : Type v} {NodeLedger : Type w}
    (graph : TypedDefinitionGraph Node Input NodeLedger) (active : Set Node) :
    Set (Input × Input) :=
  jointKernel (fun node : active ↦ graph.intension node.1)

/-- The active kernel is exactly the kernel of the joint active readout. -/
theorem activeKernel_eq_jointReadout_ker
    {Node : Type u} {Input : Type v} {NodeLedger : Type w}
    (graph : TypedDefinitionGraph Node Input NodeLedger) (active : Set Node) :
    activeKernel graph active =
      {pair | Setoid.ker (activeReadout graph active) pair.1 pair.2} := by
  ext pair
  simp only [activeKernel, jointKernel, conceptKernel, Set.mem_iInter,
    Set.mem_setOf_eq, Setoid.ker_def]
  constructor
  · intro indistinguishable
    funext node
    exact indistinguishable node
  · intro sameReadout node
    exact congrFun sameReadout node

/-- A scientific state packages its typed graph, active nodes, and the two external ledgers.
Its readout kernel is derived canonically from the graph and active set. -/
structure ScientificState
    (Node : Type u) (Input : Type v) (NodeLedger : Type w)
    (SourceLedger : Type y) (ResidualLedger : Type z) where
  graph : TypedDefinitionGraph.{u, v, w, x} Node Input NodeLedger
  active : Set Node
  sourceLedger : SourceLedger
  residualLedger : ResidualLedger

/-- The readout kernel carried by a scientific state. -/
def ScientificState.readoutKernel
    {Node : Type u} {Input : Type v} {NodeLedger : Type w}
    {SourceLedger : Type y} {ResidualLedger : Type z}
    (state : ScientificState.{u, v, w, x, y, z}
      Node Input NodeLedger SourceLedger ResidualLedger) :
    Set (Input × Input) :=
  activeKernel state.graph state.active

/-- A two-node graph with `false` as a direct prerequisite of `true`. -/
def twoNodeDefinitionGraph : TypedDefinitionGraph Bool Unit Unit where
  edge prerequisite dependent := prerequisite = false ∧ dependent = true
  nodeType _ := Unit
  intension _ _ := ()
  ledger _ := ()

/-- The singleton target consisting of the dependent node. -/
def twoNodeTargets : Set Bool := {true}

/-- The concrete two-node graph witnesses that dependency slicing can strictly add nodes. -/
theorem dependencySlice_strict_witness :
    twoNodeTargets ⊂ dependencySlice twoNodeDefinitionGraph twoNodeTargets := by
  apply Set.ssubset_iff_exists.mpr
  refine ⟨subset_prerequisiteClosure twoNodeDefinitionGraph.edge twoNodeTargets,
    false, ?_, ?_⟩
  · exact ⟨true, by simp [twoNodeTargets],
      reachable_of_edge (by simp [twoNodeDefinitionGraph])⟩
  · simp [twoNodeTargets]

#print axioms activeKernel_eq_jointReadout_ker
#print axioms dependencySlice_strict_witness

end D5.S3.ConceptDynamics.DagSemantics.TypedDefinitionGraphSlice
