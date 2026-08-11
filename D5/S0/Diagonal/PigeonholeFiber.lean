/- GID: D5/S0/Diagonal/PigeonholeFiber
   generality: G
   mirror-B: D5/B/S0/Diagonal/PigeonholeFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A smaller reading space forces two distinct objects to share a reading. -/

import Mathlib.SetTheory.Cardinal.Order

universe u

namespace D5.S0.Diagonal.PigeonholeFiber

/-- If the reading space has smaller cardinality than the object space, two distinct objects
produce the same reading. The finite-reading case is an immediate specialization. -/
theorem finite_reading_has_fiber
    {Objects Readings : Type u}
    (read : Objects → Readings)
    (hcard : Cardinal.mk Readings < Cardinal.mk Objects) :
    ∃ x y, x ≠ y ∧ read x = read y := by
  have hnot : ¬Function.Injective read := by
    intro hinj
    exact (not_le_of_gt hcard) (Cardinal.mk_le_of_injective hinj)
  obtain ⟨x, y, hEq, hNe⟩ := Function.not_injective_iff.mp hnot
  exact ⟨x, y, hNe, hEq⟩

end D5.S0.Diagonal.PigeonholeFiber
