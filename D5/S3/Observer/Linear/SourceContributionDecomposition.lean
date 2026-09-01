/- GID: D5/S3/Observer/Linear/SourceContributionDecomposition
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/SourceContributionDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Source contributions decompose uniquely exactly when their submodules are disjoint. -/

import Mathlib.LinearAlgebra.Projection

/- Library-search audit trail (2026-09-01):
   * The target atom remains residual-open with empty `coverage_gids` and no
     formalization receipt. Repository searches by contribution, unique
     decomposition, sums, intersections, `Disjoint`, and addition-map kernels
     found no equivalent D5 theorem. Same-section atoms 39.1 and 41.1 concern
     pseudoinverse energy and zero capacity; atom 64 assumes disjointness to
     compute singular values, so none covers this iff.
   * Pinned Mathlib has no declaration packaging the full iff. Exact component
     hits `LinearMap.coprod`, `LinearMap.ker_coprod_of_disjoint_range`,
     `Submodule.sup_eq_range`, and `Submodule.disjoint_def` supply the algebra.
     Loogle additionally found the exact uniqueness bridge
     `Function.Injective.existsUnique_of_mem_range`.
   * The pinned package manifest contains no additional domain library beyond
     Mathlib's standard toolchain dependencies. The LeanSearch HTTP endpoint
     returned status 405, so no LeanSearch result is claimed. No new definition
     or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.SourceContributionDecomposition

open LinearMap

universe u v

/-- Every element of the sum of two source submodules has a unique ordered
decomposition exactly when the source submodules have zero intersection. -/
theorem source_contribution_unique_decomposition_iff_disjoint
    {R : Type u} {Y : Type v} [Ring R] [AddCommGroup Y] [Module R Y]
    (observer external : Submodule R Y) :
    (∀ y : Y, y ∈ observer ⊔ external →
      ∃! decomposition : observer × external,
        (decomposition.1 : Y) + (decomposition.2 : Y) = y) ↔
      Disjoint observer external := by
  constructor
  · intro uniqueDecomposition
    have sourceSumInjective :
        Function.Injective (observer.subtype.coprod external.subtype) := by
      intro left right equalSums
      have leftInSum :
          observer.subtype.coprod external.subtype left ∈ observer ⊔ external := by
        rw [Submodule.sup_eq_range]
        exact ⟨left, rfl⟩
      obtain ⟨decomposition, _, decompositionUnique⟩ :=
        uniqueDecomposition _ leftInSum
      have leftEq : left = decomposition := decompositionUnique left (by simp)
      have rightEq : right = decomposition := decompositionUnique right (by
        simpa using equalSums.symm)
      exact leftEq.trans rightEq.symm
    rw [Submodule.disjoint_def]
    intro y yObserver yExternal
    let overlapDecomposition : observer × external :=
      (⟨y, yObserver⟩, ⟨-y, external.neg_mem yExternal⟩)
    have sameSourceSum :
        observer.subtype.coprod external.subtype overlapDecomposition =
          observer.subtype.coprod external.subtype 0 := by
      simp [overlapDecomposition]
    have decompositionZero := sourceSumInjective sameSourceSum
    have observerPartZero :=
      congrArg (fun decomposition : observer × external => (decomposition.1 : Y))
        decompositionZero
    simpa [overlapDecomposition] using observerPartZero
  · intro sourceDisjoint
    have sourceSumInjective :
        Function.Injective (observer.subtype.coprod external.subtype) := by
      rw [← ker_eq_bot, ker_coprod_of_disjoint_range,
        Submodule.ker_subtype, Submodule.ker_subtype, Submodule.prod_bot]
      simpa using sourceDisjoint
    intro y yInSum
    have yInRange :
        y ∈ Set.range (observer.subtype.coprod external.subtype) := by
      rw [Submodule.sup_eq_range] at yInSum
      exact yInSum
    simpa using sourceSumInjective.existsUnique_of_mem_range yInRange

#print axioms source_contribution_unique_decomposition_iff_disjoint

end D5.S3.Observer.Linear.SourceContributionDecomposition
