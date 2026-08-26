/- GID: D5/S3/ConceptDynamics/DagSemantics/FiberInternalPaths
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/FiberInternalPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Paths whose edges stay inside readout fibers cannot change the observed coordinate. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Logic.Relation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.FiberInternalPaths

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- An edge relation is internal to a readout when every edge stays in one readout fiber. -/
def FiberInternal
    {State Coordinate : Type*}
    (edge : State → State → Prop) (readout : Concept State Coordinate) : Prop :=
  ∀ ⦃first second : State⦄, edge first second → readout first = readout second

/-- Every reflexive-transitive path built from fiber-internal edges stays in one fiber. -/
theorem readout_eq_of_reachable
    {State Coordinate : Type*}
    {edge : State → State → Prop} {readout : Concept State Coordinate}
    (internal : FiberInternal edge readout)
    {first last : State}
    (path : Relation.ReflTransGen edge first last) :
    readout first = readout last := by
  induction path with
  | refl => rfl
  | tail _ edgeStep inductionHypothesis =>
      exact inductionHypothesis.trans (internal edgeStep)

/-- States with different readouts cannot be connected by a fiber-internal path. -/
theorem no_reachable_of_readout_ne
    {State Coordinate : Type*}
    {edge : State → State → Prop} {readout : Concept State Coordinate}
    (internal : FiberInternal edge readout)
    {first last : State}
    (different : readout first ≠ readout last) :
    ¬ Relation.ReflTransGen edge first last := by
  intro path
  exact different (readout_eq_of_reachable internal path)

/-- Fiber-internal reachability is contained in the kernel relation of the readout. -/
theorem reachable_subset_kernel
    {State Coordinate : Type*}
    {edge : State → State → Prop} {readout : Concept State Coordinate}
    (internal : FiberInternal edge readout) :
    {pair : State × State | Relation.ReflTransGen edge pair.1 pair.2} ⊆
      {pair : State × State | readout pair.1 = readout pair.2} := by
  intro pair path
  exact readout_eq_of_reachable internal path

#print axioms readout_eq_of_reachable
#print axioms reachable_subset_kernel

end D5.S3.ConceptDynamics.DagSemantics.FiberInternalPaths
