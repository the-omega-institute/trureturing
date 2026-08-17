/- GID: D5/S3/Zeros/Symmetry/RightHalfReflectionCriterion
   generality: G
   mirror-B: D5/B/S3/Zeros/Symmetry/RightHalfReflectionCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reflection symmetry reduces a fixed-point claim to the right half. -/

/- Library-search audit trail (2026-08-17):
   * D5 searches found reflection fixed-point, zero-orbit, and count-halving results,
     but no right-half criterion equivalent to the global fixed-point claim.
   * Pinned Mathlib source searches and `smart_search.sh` queries for reflection-invariant
     predicates and right-half fixed points found no exact theorem.
-/

import Mathlib.Tactic

namespace D5.S3.Zeros.Symmetry.RightHalfReflectionCriterion

/-- For a predicate invariant under reflection about one half, proving that all points are fixed
is equivalent to checking only the points in the right half. -/
theorem reflection_symmetric_right_half_iff
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (P : α → Prop)
    (hreflect : ∀ x, P (1 - x) ↔ P x) :
    (∀ x, P x → x = 1 / 2) ↔ ∀ x, P x → 1 / 2 ≤ x → x = 1 / 2 := by
  constructor
  · intro hall x hx _
    exact hall x hx
  · intro hright x hx
    by_cases hxright : 1 / 2 ≤ x
    · exact hright x hx hxright
    · have hreflected : P (1 - x) := (hreflect x).2 hx
      have hright_reflected : 1 / 2 ≤ 1 - x := by linarith
      have hfixed : 1 - x = 1 / 2 := hright (1 - x) hreflected hright_reflected
      linarith

#print axioms reflection_symmetric_right_half_iff

end D5.S3.Zeros.Symmetry.RightHalfReflectionCriterion
