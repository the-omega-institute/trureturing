/- GID: D5/S3/ConceptDynamics/Sufficiency/PermissionIntersectionLeast
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/PermissionIntersectionLeast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A sufficient intersection is the unique least sufficient permission bundle. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-23):
   * Repository searches for `sInter`, `IsLeast`, `Sufficient`, and least-set
     patterns found no exact theorem or equivalent permission-bundle primitive.
   * Pinned Mathlib provides the exact supporting result
     `Set.sInter_subset_of_mem` in `Mathlib.Data.Set.Lattice`; it is directly
     applied below. `Set.subset_sInter` is also present but is not needed.
   * No full theorem combining the canonical intersection, leastness, and
     uniqueness was found. The `loogle` and `leansearch` executables are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.PermissionIntersectionLeast

/-- If the intersection of all sufficient permission bundles is itself
sufficient, that canonical intersection is least, and it is the unique least
sufficient bundle. -/
theorem sufficient_intersection_is_unique_least {K : Type*}
    (Sufficient : Set K -> Prop)
    (hInter : Sufficient (⋂₀ {P : Set K | Sufficient P})) :
    IsLeast {P : Set K | Sufficient P}
        (⋂₀ {P : Set K | Sufficient P}) ∧
      ∃! P : Set K, IsLeast {Q : Set K | Sufficient Q} P := by
  have hleast :
      IsLeast {P : Set K | Sufficient P}
        (⋂₀ {P : Set K | Sufficient P}) := by
    refine ⟨hInter, ?_⟩
    intro P hP
    exact Set.sInter_subset_of_mem hP
  refine ⟨hleast, ?_⟩
  refine ⟨_, hleast, ?_⟩
  intro Q hQ
  apply Set.Subset.antisymm
  · exact hQ.2 hleast.1
  · exact hleast.2 hQ.1

example :
    IsLeast (Set.univ : Set (Set Bool))
        (⋂₀ (Set.univ : Set (Set Bool))) ∧
      ∃! P : Set Bool, IsLeast (Set.univ : Set (Set Bool)) P := by
  exact sufficient_intersection_is_unique_least (fun _ => True) trivial

example : Bool := false

#print axioms sufficient_intersection_is_unique_least

end D5.S3.ConceptDynamics.Sufficiency.PermissionIntersectionLeast
