/- GID: D5/S3/ConceptDynamics/DagCompletion/FrontierAntichain
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An executable frontier over a predecessor-closed completed set is an antichain for strict dependency reachability. -/

import D5.S3.ConceptDynamics.DagSemantics.ExecutableFrontier
import D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.FrontierAntichain

open D5.S3.ConceptDynamics.DagSemantics.ExecutableFrontier
open D5.S3.ConceptDynamics.DagSemantics.PrerequisiteClosure

/-- Membership propagates backward along a nonempty path in a predecessor-closed set. -/
theorem mem_of_transGen_to_predecessorClosed
    {V : Type*} {edge : V → V → Prop} {closed : Set V}
    (closedUnderPrerequisites : PredecessorClosed edge closed)
    {first last : V}
    (path : Relation.TransGen edge first last)
    (lastIn : last ∈ closed) : first ∈ closed := by
  induction path with
  | single dependency =>
      exact closedUnderPrerequisites dependency lastIn
  | tail prefix finalEdge inductionHypothesis =>
      exact inductionHypothesis
        (closedUnderPrerequisites finalEdge lastIn)

/-- No direct dependency edge joins two frontier nodes when completed and pending are disjoint. -/
theorem no_edge_between_frontier_nodes
    {V : Type*} {edge : V → V → Prop}
    {completed pending : Set V}
    (disjoint : Disjoint completed pending)
    {first second : V}
    (firstFrontier : first ∈ executableFrontier edge completed pending)
    (secondFrontier : second ∈ executableFrontier edge completed pending) :
    ¬ edge first second := by
  intro dependency
  have firstCompleted : first ∈ completed := secondFrontier.2 dependency
  exact Set.disjoint_left.1 disjoint firstCompleted firstFrontier.1

/-- Under predecessor closure, no strict dependency path joins two frontier nodes. -/
theorem no_strictReachability_between_frontier_nodes
    {V : Type*} {edge : V → V → Prop}
    {completed pending : Set V}
    (completedClosed : PredecessorClosed edge completed)
    (disjoint : Disjoint completed pending)
    {first second : V}
    (firstFrontier : first ∈ executableFrontier edge completed pending)
    (secondFrontier : second ∈ executableFrontier edge completed pending) :
    ¬ Relation.TransGen edge first second := by
  intro path
  have firstCompleted : first ∈ completed := by
    cases path with
    | single dependency =>
        exact secondFrontier.2 dependency
    | @tail first middle second prefix finalEdge =>
        exact mem_of_transGen_to_predecessorClosed completedClosed prefix
          (secondFrontier.2 finalEdge)
  exact Set.disjoint_left.1 disjoint firstCompleted firstFrontier.1

/-- The complement frontier is a strict-reachability antichain. -/
theorem complement_frontier_strict_antichain
    {V : Type*} {edge : V → V → Prop}
    {pending : Set V}
    {first second : V}
    (firstFrontier : first ∈ executableFrontier edge pendingᶜ pending)
    (secondFrontier : second ∈ executableFrontier edge pendingᶜ pending) :
    ¬ Relation.TransGen edge first second := by
  apply no_strictReachability_between_frontier_nodes
    (completed := pendingᶜ) (pending := pending)
  · intro prerequisite dependent dependency dependentCompleted
    exact fun prerequisitePending => dependentCompleted prerequisitePending
  · exact Set.disjoint_compl_left
  · exact firstFrontier
  · exact secondFrontier

#print axioms no_strictReachability_between_frontier_nodes
#print axioms complement_frontier_strict_antichain

end D5.S3.ConceptDynamics.DagCompletion.FrontierAntichain
