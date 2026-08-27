/- GID: D5/S3/ConceptDynamics/DagCompletion/ConsequenceClosure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/ConsequenceClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reachability generates the least successor-closed consequence set, dual to prerequisite closure. -/

import D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure
import D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.ConsequenceClosure

open D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure
open D5.S3.ConceptDynamics.DependencyTopology.DependencyReachabilityOrder

/-- A set is successor-closed when every direct dependent of a member remains inside. -/
def SuccessorClosed {V : Type*} (edge : V → V → Prop) (set : Set V) : Prop :=
  ∀ ⦃prerequisite dependent : V⦄,
    edge prerequisite dependent → prerequisite ∈ set → dependent ∈ set

/-- The consequence closure of a source set consists of every node reachable from a source. -/
def consequenceClosure {V : Type*}
    (edge : V → V → Prop) (sources : Set V) : Set V :=
  {node | ∃ source, source ∈ sources ∧ Reachable edge source node}

/-- Every source belongs to its consequence closure. -/
theorem subset_consequenceClosure
    {V : Type*} (edge : V → V → Prop) (sources : Set V) :
    sources ⊆ consequenceClosure edge sources := by
  intro source sourceIn
  exact ⟨source, sourceIn, Relation.ReflTransGen.refl⟩

/-- Enlarging the source set enlarges its consequence closure. -/
theorem consequenceClosure_mono
    {V : Type*} {edge : V → V → Prop} {first second : Set V}
    (subset : first ⊆ second) :
    consequenceClosure edge first ⊆ consequenceClosure edge second := by
  rintro node ⟨source, sourceIn, path⟩
  exact ⟨source, subset sourceIn, path⟩

/-- Consequence closure is closed under direct dependents. -/
theorem consequenceClosure_successorClosed
    {V : Type*} (edge : V → V → Prop) (sources : Set V) :
    SuccessorClosed edge (consequenceClosure edge sources) := by
  intro prerequisite dependent dependency
  rintro ⟨source, sourceIn, path⟩
  exact ⟨source, sourceIn, path.tail dependency⟩

/-- Consequence closure is the least successor-closed superset of its sources. -/
theorem consequenceClosure_least
    {V : Type*} {edge : V → V → Prop} {sources closed : Set V}
    (contains : sources ⊆ closed)
    (closedUnderDependents : SuccessorClosed edge closed) :
    consequenceClosure edge sources ⊆ closed := by
  rintro node ⟨source, sourceIn, path⟩
  induction path with
  | refl => exact contains sourceIn
  | tail _ edgeStep inductionHypothesis =>
      exact closedUnderDependents edgeStep inductionHypothesis

/-- Consequence closure is idempotent. -/
theorem consequenceClosure_idempotent
    {V : Type*} (edge : V → V → Prop) (sources : Set V) :
    consequenceClosure edge (consequenceClosure edge sources) =
      consequenceClosure edge sources := by
  apply Set.Subset.antisymm
  · exact consequenceClosure_least Set.Subset.rfl
      (consequenceClosure_successorClosed edge sources)
  · exact subset_consequenceClosure edge (consequenceClosure edge sources)

/-- A node is a prerequisite of the target set exactly when its consequence cone meets that set. -/
theorem mem_prerequisiteClosure_iff_consequence_inter
    {V : Type*} (edge : V → V → Prop) (targets : Set V) (node : V) :
    node ∈ prerequisiteClosure edge targets ↔
      (consequenceClosure edge {node} ∩ targets).Nonempty := by
  constructor
  · rintro ⟨target, targetIn, path⟩
    exact ⟨target, ⟨node, Set.mem_singleton node, path⟩, targetIn⟩
  · rintro ⟨target, ⟨⟨source, sourceSingleton, path⟩, targetIn⟩⟩
    simpa only [Set.mem_singleton_iff] using
      (show node ∈ prerequisiteClosure edge targets from
        ⟨target, targetIn, sourceSingleton ▸ path⟩)

/-- Dually, a target lies in a consequence cone exactly when its prerequisite cone meets the sources. -/
theorem mem_consequenceClosure_iff_prerequisite_inter
    {V : Type*} (edge : V → V → Prop) (sources : Set V) (target : V) :
    target ∈ consequenceClosure edge sources ↔
      (prerequisiteClosure edge {target} ∩ sources).Nonempty := by
  constructor
  · rintro ⟨source, sourceIn, path⟩
    exact ⟨source, ⟨target, Set.mem_singleton target, path⟩, sourceIn⟩
  · rintro ⟨source, ⟨⟨witness, witnessSingleton, path⟩, sourceIn⟩⟩
    exact ⟨source, sourceIn, witnessSingleton ▸ path⟩

#print axioms consequenceClosure_least
#print axioms mem_prerequisiteClosure_iff_consequence_inter

end D5.S3.ConceptDynamics.DagCompletion.ConsequenceClosure
