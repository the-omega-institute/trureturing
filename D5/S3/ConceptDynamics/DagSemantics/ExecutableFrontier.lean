/- GID: D5/S3/ConceptDynamics/DagSemantics/ExecutableFrontier
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/ExecutableFrontier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The executable frontier consists of pending nodes whose direct prerequisites are complete. -/

import D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.ExecutableFrontier

open D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure

/-- A node is ready over a completed set when all of its direct prerequisites are complete. -/
def ReadyOver {V : Type*}
    (edge : V → V → Prop) (completed : Set V) (node : V) : Prop :=
  ∀ ⦃prerequisite : V⦄, edge prerequisite node → prerequisite ∈ completed

/-- The executable frontier is the pending part whose direct prerequisites are complete. -/
def executableFrontier {V : Type*}
    (edge : V → V → Prop) (completed pending : Set V) : Set V :=
  {node | node ∈ pending ∧ ReadyOver edge completed node}

/-- Every frontier node is pending. -/
theorem executableFrontier_subset_pending
    {V : Type*} (edge : V → V → Prop) (completed pending : Set V) :
    executableFrontier edge completed pending ⊆ pending := by
  intro node frontierMember
  exact frontierMember.1

/-- Completing more nodes can only enlarge the executable frontier. -/
theorem executableFrontier_mono_completed
    {V : Type*} {edge : V → V → Prop}
    {completedFirst completedSecond pending : Set V}
    (completedSubset : completedFirst ⊆ completedSecond) :
    executableFrontier edge completedFirst pending ⊆
      executableFrontier edge completedSecond pending := by
  rintro node ⟨pendingMember, ready⟩
  refine ⟨pendingMember, ?_⟩
  intro prerequisite dependency
  exact completedSubset (ready dependency)

/-- Restricting the pending set restricts the frontier. -/
theorem executableFrontier_mono_pending
    {V : Type*} {edge : V → V → Prop}
    {completed pendingFirst pendingSecond : Set V}
    (pendingSubset : pendingFirst ⊆ pendingSecond) :
    executableFrontier edge completed pendingFirst ⊆
      executableFrontier edge completed pendingSecond := by
  rintro node ⟨pendingMember, ready⟩
  exact ⟨pendingSubset pendingMember, ready⟩

/-- A pending node with no pending direct prerequisite is ready over the complement. -/
theorem readyOver_complement_of_no_pending_predecessor
    {V : Type*} {edge : V → V → Prop} {pending : Set V} {node : V}
    (noPendingPredecessor :
      ∀ ⦃prerequisite : V⦄, edge prerequisite node → prerequisite ∉ pending) :
    ReadyOver edge pendingᶜ node := by
  intro prerequisite dependency
  exact noPendingPredecessor dependency

/-- The complement frontier consists exactly of pending nodes with no pending prerequisite. -/
theorem mem_frontier_complement_iff
    {V : Type*} (edge : V → V → Prop) (pending : Set V) (node : V) :
    node ∈ executableFrontier edge pendingᶜ pending ↔
      node ∈ pending ∧
        ∀ ⦃prerequisite : V⦄, edge prerequisite node → prerequisite ∉ pending := by
  rfl

#print axioms executableFrontier_mono_completed
#print axioms mem_frontier_complement_iff

end D5.S3.ConceptDynamics.DagSemantics.ExecutableFrontier
