/- GID: D5/S3/ConceptDynamics/DagSemantics/FrontierExtensionClosure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/FrontierExtensionClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adjoining an executable frontier preserves predecessor closure. -/

import D5.S3.ConceptDynamics.DagSemantics.ExecutableFrontier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.FrontierExtensionClosure

open D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure
open D5.S3.ConceptDynamics.DagSemantics.ExecutableFrontier

/-- Adjoining one ready node to a predecessor-closed set preserves predecessor closure. -/
theorem predecessorClosed_insert_ready
    {V : Type*} {edge : V → V → Prop}
    {completed : Set V} {node : V}
    (completedClosed : PredecessorClosed edge completed)
    (nodeReady : ReadyOver edge completed node) :
    PredecessorClosed edge (Set.insert node completed) := by
  intro prerequisite dependent dependency dependentIn
  rcases dependentIn with dependentEq | dependentOld
  · subst dependent
    exact Or.inr (nodeReady dependency)
  · exact Or.inr (completedClosed dependency dependentOld)

/-- Adjoining the whole executable frontier preserves predecessor closure. -/
theorem predecessorClosed_union_frontier
    {V : Type*} {edge : V → V → Prop}
    {completed pending : Set V}
    (completedClosed : PredecessorClosed edge completed) :
    PredecessorClosed edge
      (completed ∪ executableFrontier edge completed pending) := by
  intro prerequisite dependent dependency dependentIn
  rcases dependentIn with dependentOld | dependentFrontier
  · exact Or.inl (completedClosed dependency dependentOld)
  · exact Or.inl (dependentFrontier.2 dependency)

/-- Executing a frontier batch never removes completed nodes. -/
theorem completed_subset_frontier_extension
    {V : Type*} (edge : V → V → Prop) (completed pending : Set V) :
    completed ⊆ completed ∪ executableFrontier edge completed pending :=
  Set.subset_union_left

#print axioms predecessorClosed_insert_ready
#print axioms predecessorClosed_union_frontier

end D5.S3.ConceptDynamics.DagSemantics.FrontierExtensionClosure
