/- GID: D5/S3/PrimeGaps/WindowOffsetParityProbe
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A doubled window offset always spans an even number of positions. -/

import Mathlib.Tactic

/-! # Trigger payload for the SL-034 observation

This module exists only to exercise the module-to-frozen-state rule on a real
pull request. It is never merged. The statement is deliberately elementary so
that the Lean report is green and the only outstanding obligation is the
missing frozen state slice.
-/

namespace D5.S3.PrimeGaps.WindowOffsetParityProbe

/-- Doubling a window offset always lands on an even span. -/
theorem window_offset_span_even (n : Nat) : (2 * n) % 2 = 0 := by
  omega

end D5.S3.PrimeGaps.WindowOffsetParityProbe
