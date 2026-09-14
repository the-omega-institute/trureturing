/- GID: D5/S1/Digit/Infinite/InfiniteSuccessorFibres
   generality: G
   mirror-B: D5/B/S1/Digit/Infinite/InfiniteSuccessorFibres
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The legal infinite digit successor is surjective with two alternating predecessors of zero and unique predecessors elsewhere. -/

import D5.S1.Digit.Infinite.SuccessorContinuity

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.InfiniteSuccessorFibres

open D5.S1.Digit.Infinite.SuccessorContinuity

/-- The successor preserves legality and is surjective. The zero sequence has precisely the
predecessors with ones at even positions and at odd positions; every nonzero sequence has a unique
predecessor. -/
theorem next_fibres :
    (∀ x : LegalDigits, ∀ j, ¬ (next x.val j = true ∧ next x.val (j + 1) = true)) ∧
    (∀ y : LegalDigits, ∃ x : LegalDigits, next x.val = y.val) ∧
    (∀ x : LegalDigits, next x.val = (fun _ => false) ↔
      (x.val = fun i => decide (i % 2 = 0)) ∨ (x.val = fun i => decide (i % 2 = 1))) ∧
    (∀ y : LegalDigits, y.val ≠ (fun _ => false) →
      ∃! x : LegalDigits, next x.val = y.val) := by
  sorry

end D5.S1.Digit.Infinite.InfiniteSuccessorFibres
