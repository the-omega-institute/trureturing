/- GID: D5/S3/PrimeGaps/WindowOffsetParityProbe
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An admissible window of width at least two has an even offset span. -/

import Mathlib.Data.Nat.Defs

/-! # Trigger payload for the SL-034 gate

This module exists only to exercise the `module` to frozen-state gate on a real
pull request. It is never merged. The statement is deliberately elementary so
that the Lean report is green and the only outstanding obligation is the
missing frozen state slice.
-/

namespace D5.S3.PrimeGaps.WindowOffsetParityProbe

/-- Doubling a window offset always lands on an even span. -/
theorem window_offset_span_even (n : Nat) : (2 * n) % 2 = 0 := by
  omega

end D5.S3.PrimeGaps.WindowOffsetParityProbe
