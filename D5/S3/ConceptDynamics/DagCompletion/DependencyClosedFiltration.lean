/- GID: D5/S3/ConceptDynamics/DagCompletion/DependencyClosedFiltration
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dependency-closed append-only filtrations order prerequisite birth no later than dependent birth. -/

import D5.S3.ConceptDynamics.DagSemantics.BirthStageFiltration
import D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.DependencyClosedFiltration

open D5.S3.ConceptDynamics.DagSemantics.BirthStageFiltration
open D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure

/-- An append-only filtration whose every stage is closed under prerequisites. -/
structure DependencyFiltration (V : Type*) (edge : V → V → Prop) where
  stage : Nat → Set V
  appendOnly : AppendOnly stage
  prerequisiteClosed : ∀ level, PredecessorClosed edge (stage level)

/-- Nodes that occur at some stage of a dependency filtration. -/
def PresentNode {V : Type*} {edge : V → V → Prop}
    (filtration : DependencyFiltration V edge) : Type _ :=
  {node : V // ∃ level, node ∈ filtration.stage level}

/-- The canonical birth time of a present node. -/
noncomputable def DependencyFiltration.birth
    {V : Type*} {edge : V → V → Prop}
    (filtration : DependencyFiltration V edge)
    (node : PresentNode filtration) : Nat :=
  birthStage filtration.stage node.1 node.2

/-- Every direct prerequisite of a present node is itself present. -/
def DependencyFiltration.prerequisiteNode
    {V : Type*} {edge : V → V → Prop}
    (filtration : DependencyFiltration V edge)
    {prerequisite dependent : V}
    (dependency : edge prerequisite dependent)
    (dependentNode : PresentNode filtration) : PresentNode filtration := by
  refine ⟨prerequisite, ?_⟩
  rcases dependentNode.2 with ⟨level, dependentPresent⟩
  exact ⟨level,
    filtration.prerequisiteClosed level dependency dependentPresent⟩

/-- A prerequisite is born no later than its dependent. -/
theorem prerequisite_birth_le
    {V : Type*} {edge : V → V → Prop}
    (filtration : DependencyFiltration V edge)
    {prerequisite dependent : V}
    (dependency : edge prerequisite dependent)
    (dependentNode : PresentNode filtration) :
    filtration.birth
        (filtration.prerequisiteNode dependency dependentNode) ≤
      filtration.birth dependentNode := by
  apply birthStage_le_of_mem
  exact filtration.prerequisiteClosed
    (filtration.birth dependentNode) dependency
    (birthStage_mem filtration.stage dependentNode.1 dependentNode.2)

/-- A strict staging discipline requires some strictly earlier stage for every prerequisite. -/
def StrictlyDependencyStaged
    {V : Type*} {edge : V → V → Prop}
    (filtration : DependencyFiltration V edge) : Prop :=
  ∀ ⦃prerequisite dependent : V⦄,
    edge prerequisite dependent →
      ∀ ⦃level : Nat⦄, dependent ∈ filtration.stage level →
        ∃ earlier, earlier < level ∧ prerequisite ∈ filtration.stage earlier

/-- Under strict staging, prerequisites are born strictly earlier than dependents. -/
theorem prerequisite_birth_lt
    {V : Type*} {edge : V → V → Prop}
    (filtration : DependencyFiltration V edge)
    (strictStaging : StrictlyDependencyStaged filtration)
    {prerequisite dependent : V}
    (dependency : edge prerequisite dependent)
    (dependentNode : PresentNode filtration) :
    filtration.birth
        (filtration.prerequisiteNode dependency dependentNode) <
      filtration.birth dependentNode := by
  obtain ⟨earlier, earlierLt, prerequisitePresent⟩ :=
    strictStaging dependency
      (birthStage_mem filtration.stage dependentNode.1 dependentNode.2)
  exact lt_of_le_of_lt
    (birthStage_le_of_mem filtration.stage prerequisite
      (filtration.prerequisiteNode dependency dependentNode).2
      prerequisitePresent)
    earlierLt

/-- Any dependency path is nondecreasing in birth time. -/
theorem birth_mono_of_reachable
    {V : Type*} {edge : V → V → Prop}
    (filtration : DependencyFiltration V edge)
    {first last : PresentNode filtration}
    (path : Relation.ReflTransGen edge first.1 last.1) :
    filtration.birth first ≤ filtration.birth last := by
  induction path with
  | refl => exact le_rfl
  | @tail firstValue middle lastValue prefix edgeStep inductionHypothesis =>
      let middleNode : PresentNode filtration :=
        filtration.prerequisiteNode edgeStep last
      have firstBirthLeMiddle : filtration.birth first ≤ filtration.birth middleNode := by
        exact inductionHypothesis
      exact firstBirthLeMiddle.trans
        (prerequisite_birth_le filtration edgeStep last)

#print axioms prerequisite_birth_le
#print axioms prerequisite_birth_lt

end D5.S3.ConceptDynamics.DagCompletion.DependencyClosedFiltration
