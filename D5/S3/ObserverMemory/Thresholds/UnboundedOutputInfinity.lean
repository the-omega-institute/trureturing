/- GID: D5/S3/ObserverMemory/Thresholds/UnboundedOutputInfinity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Thresholds/UnboundedOutputInfinity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An unbounded natural-valued output forces its carrier to be infinite. -/

import Mathlib.Data.Fintype.Order

/-! Library-search audit trail (2026-08-17):
* Repository searches for unbounded outputs and infinite carriers found no equivalent declaration.
* Pinned Mathlib provides `Finite.bddAbove_range`, which is applied directly below.
* Pinned Mathlib also has `Set.infinite_of_forall_exists_gt`; two local `smart_search.sh`
  declaration-name queries returned no more direct theorem for the carrier-level conclusion.
-/

namespace D5.S3.ObserverMemory.Thresholds.UnboundedOutputInfinity

/-- A natural-valued output that exceeds every bound can only live on an infinite carrier. -/
theorem unbounded_output_implies_infinite {α : Type*} (output : α → ℕ)
    (hunbounded : ∀ bound, ∃ object, bound < output object) : Infinite α := by
  rw [← not_finite_iff_infinite]
  intro hfinite
  letI : Finite α := hfinite
  obtain ⟨bound, hbound⟩ := Finite.bddAbove_range output
  obtain ⟨object, hobject⟩ := hunbounded bound
  exact (not_lt_of_ge (hbound ⟨object, rfl⟩)) hobject

#print axioms unbounded_output_implies_infinite

end D5.S3.ObserverMemory.Thresholds.UnboundedOutputInfinity
