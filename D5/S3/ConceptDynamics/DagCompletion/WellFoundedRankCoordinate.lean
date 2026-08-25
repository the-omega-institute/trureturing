/- GID: D5/S3/ConceptDynamics/DagCompletion/WellFoundedRankCoordinate
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every well-founded dependency relation has a canonical strict ordinal rank coordinate. -/

import D5.S3.ConceptDynamics.DagSemantics.StrictDependencyCoordinate
import Mathlib.SetTheory.Ordinal.Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.WellFoundedRankCoordinate

open D5.S3.ConceptDynamics.DagSemantics.StrictDependencyCoordinate

/-- The canonical ordinal rank of a node in a well-founded relation. -/
def dependencyRank
    {V : Type*} {edge : V → V → Prop}
    (wellFounded : WellFounded edge) : V → Ordinal :=
  wellFounded.rank

/-- Every dependency edge strictly increases the canonical ordinal rank. -/
theorem dependencyRank_strict
    {V : Type*} {edge : V → V → Prop}
    (wellFounded : WellFounded edge) :
    StrictDependencyCoordinate edge (dependencyRank wellFounded) := by
  intro prerequisite dependent dependency
  exact wellFounded.rank_lt_of_rel dependency

/-- Every nonempty dependency path strictly increases rank. -/
theorem dependencyRank_strict_of_path
    {V : Type*} {edge : V → V → Prop}
    (wellFounded : WellFounded edge)
    {first last : V} (path : Relation.TransGen edge first last) :
    dependencyRank wellFounded first < dependencyRank wellFounded last :=
  strict_of_transGen (dependencyRank_strict wellFounded) path

/-- Mutual reachability collapses canonical rank. -/
theorem dependencyRank_eq_of_mutual_reachable
    {V : Type*} {edge : V → V → Prop}
    (wellFounded : WellFounded edge)
    {first last : V}
    (forward : Relation.ReflTransGen edge first last)
    (backward : Relation.ReflTransGen edge last first) :
    dependencyRank wellFounded first = dependencyRank wellFounded last :=
  eq_of_mutual_reflTransGen
    (dependencyRank_strict wellFounded) forward backward

#print axioms dependencyRank_strict
#print axioms dependencyRank_strict_of_path

end D5.S3.ConceptDynamics.DagCompletion.WellFoundedRankCoordinate
