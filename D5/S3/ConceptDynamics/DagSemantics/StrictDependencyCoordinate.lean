/- GID: D5/S3/ConceptDynamics/DagSemantics/StrictDependencyCoordinate
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/StrictDependencyCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A strictly increasing dependency coordinate linearizes paths and forbids cycles. -/

import Mathlib.Logic.Relation
import Mathlib.Order.Defs.PartialOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagSemantics.StrictDependencyCoordinate

/-- A coordinate is strict when every dependency edge increases it. -/
def StrictDependencyCoordinate
    {V Rank : Type*} [Preorder Rank]
    (edge : V → V → Prop) (coordinate : V → Rank) : Prop :=
  ∀ ⦃prerequisite dependent : V⦄,
    edge prerequisite dependent → coordinate prerequisite < coordinate dependent

/-- Strict increase propagates along every nonempty dependency path. -/
theorem strict_of_transGen
    {V Rank : Type*} [Preorder Rank]
    {edge : V → V → Prop} {coordinate : V → Rank}
    (strict : StrictDependencyCoordinate edge coordinate)
    {first last : V} (path : Relation.TransGen edge first last) :
    coordinate first < coordinate last := by
  induction path with
  | single edgeStep => exact strict edgeStep
  | tail _ edgeStep inductionHypothesis =>
      exact lt_trans inductionHypothesis (strict edgeStep)

/-- Reflexive-transitive dependency reachability is nondecreasing in a strict coordinate. -/
theorem monotone_of_reflTransGen
    {V Rank : Type*} [Preorder Rank]
    {edge : V → V → Prop} {coordinate : V → Rank}
    (strict : StrictDependencyCoordinate edge coordinate)
    {first last : V} (path : Relation.ReflTransGen edge first last) :
    coordinate first ≤ coordinate last := by
  induction path with
  | refl => exact le_rfl
  | tail _ edgeStep inductionHypothesis =>
      exact le_trans inductionHypothesis (le_of_lt (strict edgeStep))

/-- A strict dependency coordinate rules out every directed cycle. -/
theorem acyclic_of_strictCoordinate
    {V Rank : Type*} [Preorder Rank]
    {edge : V → V → Prop} {coordinate : V → Rank}
    (strict : StrictDependencyCoordinate edge coordinate) :
    ∀ vertex, ¬ Relation.TransGen edge vertex vertex := by
  intro vertex cycle
  exact (lt_irrefl (coordinate vertex)) (strict_of_transGen strict cycle)

/-- Mutual dependency reachability collapses under every strict coordinate. -/
theorem eq_of_mutual_reflTransGen
    {V Rank : Type*} [PartialOrder Rank]
    {edge : V → V → Prop} {coordinate : V → Rank}
    (strict : StrictDependencyCoordinate edge coordinate)
    {first second : V}
    (forward : Relation.ReflTransGen edge first second)
    (backward : Relation.ReflTransGen edge second first) :
    coordinate first = coordinate second := by
  exact le_antisymm
    (monotone_of_reflTransGen strict forward)
    (monotone_of_reflTransGen strict backward)

#print axioms strict_of_transGen
#print axioms acyclic_of_strictCoordinate

end D5.S3.ConceptDynamics.DagSemantics.StrictDependencyCoordinate
