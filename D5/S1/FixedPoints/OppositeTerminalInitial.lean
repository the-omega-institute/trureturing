/- GID: D5/S1/FixedPoints/OppositeTerminalInitial
   generality: G
   mirror-B: D5/B/S1/FixedPoints/OppositeTerminalInitial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Terminal objects become initial objects in the opposite category. -/

import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/- Library-search audit trail (2026-08-17):
   * Local D5 searches for terminal and initial objects in opposite categories
     found no equivalent repository declaration.
   * The pinned-Mathlib source and `smart_search.sh` found the exact directions
     `CategoryTheory.Limits.IsTerminal.op` and `IsInitial.unop`, composed below. -/

namespace D5.S1.FixedPoints.OppositeTerminalInitial

open CategoryTheory CategoryTheory.Limits

universe u v

/-- An object is terminal exactly when its opposite is initial in the opposite category. -/
theorem terminal_iff_initial_op {C : Type u} [Category.{v} C] (X : C) :
    Nonempty (IsTerminal X) ↔ Nonempty (IsInitial (Opposite.op X)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.op⟩
  · rintro ⟨h⟩
    exact ⟨by simpa using h.unop⟩

#print axioms terminal_iff_initial_op

end D5.S1.FixedPoints.OppositeTerminalInitial
