/- GID: D5/S3/Observer/Naturality/SelfSimilarGeneratingSystem
   generality: G
   mirror-B: D5/B/S3/Observer/Naturality/SelfSimilarGeneratingSystem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observer-compatible branch systems satisfy geometric and generative self-similarity. -/

import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Function.Conjugate

/- Library-search audit trail (2026-09-01):
   * Repository searches for self-similar systems, scaled branches, geometric
     branch covers, and observer intertwinings found no aggregate definition
     containing the source's six components and both self-similarity laws.
   * `GoldenCompatibleIFS` and `GoldenModelSetSelfSimilar` provide concrete
     geometric branch systems, but neither has reflection, positive-cone,
     observation, completion, and scale-covariance data. The nearby
     `OmnicompleteIndifferentState` and `DynamicIrrationalObserver` structures
     likewise have different components and laws.
   * Pinned Mathlib's exact component hit is `Function.Semiconj`, which states
     the observation/branch intertwining law and is reused below. Searches of
     Mathlib and all other pinned Lean packages found no packaged structure
     combining that law with a branch-image cover and the other components. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Naturality.SelfSimilarGeneratingSystem

universe u v w z

/-- A self-similar generating system consists of the source's six components:
the carrier `X`, branches, a reflection or duality, a positive region, an
observation interface, and a completion operation. `scaledBranches` interprets
the scale-dependent branch appearing in the generative law.

The geometric law says that branch images cover the carrier. The generative
law says that observation semiconjugates every branch to its representation at
every scale. The source gives no involutivity, cone algebra, or idempotence laws,
so none are added here. -/
structure System
    (X : Type u) (Branch : Type v) (Scale : Type w)
    (View : Scale -> Type z) where
  branches : Branch -> X -> X
  reflection : X -> X
  positiveCone : Set X
  observation : (scale : Scale) -> X -> View scale
  completion : X -> X
  scaledBranches : (scale : Scale) -> Branch -> View scale -> View scale
  geometric_self_similarity : Set.univ = ⋃ i, Set.range (branches i)
  generative_self_similarity :
    ∀ scale i, Function.Semiconj (observation scale) (branches i) (scaledBranches scale i)

/-- A concrete realization on a two-point carrier. The single branch,
reflection, observation, completion, and represented branch are identities;
the positive region is the whole carrier. -/
def boolSystem : System Bool Unit Unit (fun _ => Bool) where
  branches := fun _ => id
  reflection := id
  positiveCone := Set.univ
  observation := fun _ => id
  completion := id
  scaledBranches := fun _ _ => id
  geometric_self_similarity := by
    apply Set.Subset.antisymm
    · intro x _
      rw [Set.mem_iUnion]
      exact ⟨(), x, rfl⟩
    · exact Set.subset_univ _
  generative_self_similarity := by
    intro scale i x
    rfl

/-- The definition is nonempty and realizable with all six components filled
on `Bool`; the displayed identities also expose the scale-dependent branch
used by the generative law. -/
theorem exists_bool_self_similar_generating_system :
    ∃ system : System Bool Unit Unit (fun _ => Bool),
      system.branches () = id ∧
        system.reflection = id ∧
        system.positiveCone = Set.univ ∧
        system.observation () = id ∧
        system.completion = id ∧
        system.scaledBranches () () = id := by
  exact ⟨boolSystem, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms exists_bool_self_similar_generating_system

end D5.S3.Observer.Naturality.SelfSimilarGeneratingSystem
