/- GID: D5/S3/ConceptDynamics/DagSemantics/PrerequisiteClosure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/PrerequisiteClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reachability generates the least predecessor-closed set containing a target set. -/

import Mathlib.Logic.Relation
import Mathlib.Data.Set.Lattice
import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

/- Library-search audit trail (2026-08-27):
   * Reuses `DependencyReachabilityOrder.Reachable` and its
     `reachable_refl`, `reachable_trans`, and `reachable_of_edge` API.
   * No local reflexive-transitive reachability carrier is defined here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure

open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

/-- A set is predecessor-closed when every direct prerequisite of a member is a member. -/
def PredecessorClosed {V : Type*} (edge : V → V → Prop) (set : Set V) : Prop :=
  ∀ ⦃prerequisite dependent : V⦄,
    edge prerequisite dependent → dependent ∈ set → prerequisite ∈ set

/-- The prerequisite closure of a target set consists of every node reaching a target. -/
def prerequisiteClosure {V : Type*}
    (edge : V → V → Prop) (targets : Set V) : Set V :=
  {node | ∃ target, target ∈ targets ∧ Reachable edge node target}

/-- Every target belongs to its prerequisite closure. -/
theorem subset_prerequisiteClosure
    {V : Type*} (edge : V → V → Prop) (targets : Set V) :
    targets ⊆ prerequisiteClosure edge targets := by
  intro target targetIn
  exact ⟨target, targetIn, reachable_refl edge target⟩

/-- Enlarging the target set enlarges its prerequisite closure. -/
theorem prerequisiteClosure_mono
    {V : Type*} {edge : V → V → Prop} {first second : Set V}
    (subset : first ⊆ second) :
    prerequisiteClosure edge first ⊆ prerequisiteClosure edge second := by
  rintro node ⟨target, targetIn, path⟩
  exact ⟨target, subset targetIn, path⟩

/-- The prerequisite closure is closed under direct prerequisites. -/
theorem prerequisiteClosure_predecessorClosed
    {V : Type*} (edge : V → V → Prop) (targets : Set V) :
    PredecessorClosed edge (prerequisiteClosure edge targets) := by
  intro prerequisite dependent dependency
  rintro ⟨target, targetIn, dependentPath⟩
  exact ⟨target, targetIn,
    (reachable_of_edge dependency).trans dependentPath⟩

/-- The prerequisite closure is the least predecessor-closed superset of its targets. -/
theorem prerequisiteClosure_least
    {V : Type*} {edge : V → V → Prop} {targets closed : Set V}
    (contains : targets ⊆ closed)
    (closedUnderPrerequisites : PredecessorClosed edge closed) :
    prerequisiteClosure edge targets ⊆ closed := by
  rintro node ⟨target, targetIn, path⟩
  exact path.head_induction_on
    (contains targetIn)
    (fun dependency _ inductionHypothesis =>
      closedUnderPrerequisites dependency inductionHypothesis)

/-- Applying prerequisite closure twice changes nothing. -/
theorem prerequisiteClosure_idempotent
    {V : Type*} (edge : V → V → Prop) (targets : Set V) :
    prerequisiteClosure edge (prerequisiteClosure edge targets) =
      prerequisiteClosure edge targets := by
  apply Set.Subset.antisymm
  · exact prerequisiteClosure_least
      (Set.Subset.rfl)
      (prerequisiteClosure_predecessorClosed edge targets)
  · exact subset_prerequisiteClosure edge (prerequisiteClosure edge targets)

/-- Prerequisite closure distributes over binary unions. -/
theorem prerequisiteClosure_union
    {V : Type*} (edge : V → V → Prop) (first second : Set V) :
    prerequisiteClosure edge (first ∪ second) =
      prerequisiteClosure edge first ∪ prerequisiteClosure edge second := by
  ext node
  constructor
  · rintro ⟨target, targetIn, path⟩
    rcases targetIn with targetInFirst | targetInSecond
    · exact Or.inl ⟨target, targetInFirst, path⟩
    · exact Or.inr ⟨target, targetInSecond, path⟩
  · rintro (nodeInFirst | nodeInSecond)
    · rcases nodeInFirst with ⟨target, targetIn, path⟩
      exact ⟨target, Or.inl targetIn, path⟩
    · rcases nodeInSecond with ⟨target, targetIn, path⟩
      exact ⟨target, Or.inr targetIn, path⟩

#print axioms prerequisiteClosure_least
#print axioms prerequisiteClosure_idempotent

end D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure
