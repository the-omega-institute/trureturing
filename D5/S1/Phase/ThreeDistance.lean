/- GID: D5/S1/Phase/ThreeDistance
   generality: G
   mirror-B: none(waiver:classical-result-tail-is-documented-at-the-formal-site)
   mirror-E: none(waiver:classical-theorem-carried-by-registered-axiom-debt)
   anchors: []
   digest: Golden rotation points have at most three distinct cyclic adjacent gaps. -/

import D5.X_Assumptions.AxiomDebt
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Phase

open D5.X_Assumptions

/-- The representative `{n * phi}` of `goldenPhase n` in `[0, 1)`. -/
noncomputable def goldenFractionalPart (n : ℕ) : ℝ :=
  Int.fract ((n : ℝ) * Real.goldenRatio)

/-- The `N` points `{n * phi}` for `0 ≤ n < N`. -/
noncomputable def goldenOrbit (N : ℕ) : Finset ℝ :=
  AxiomDebt.fractionalOrbit Real.goldenRatio N

/-- The golden orbit representatives sorted increasingly in `[0, 1)`. -/
noncomputable def sortedGoldenOrbit (N : ℕ) : List ℝ :=
  (goldenOrbit N).sort

/-- Adjacent gaps of the sorted orbit, including the last-to-first circle gap. -/
noncomputable def goldenGapValues (N : ℕ) : Finset ℝ :=
  (AxiomDebt.cyclicGaps (sortedGoldenOrbit N)).toFinset

/-
FROZEN TAIL D5-T0019: the three-gap theorem is a classical result (Steinhaus
conjecture, Sós 1957), but pinned mathlib has no implementation. Its single
registered axiom is in D5/X_Assumptions/AxiomDebt; the same case tracks the
librarian's upstream formalization issue.
-/

/--
Three-gap theorem for the golden rotation: after sorting `{n * phi}` for
`0 ≤ n < N` around the unit circle, the adjacent cyclic gaps have at most three
distinct lengths.
-/
theorem three_gap (N : ℕ) : (goldenGapValues N).card ≤ 3 := by
  simpa [goldenGapValues, sortedGoldenOrbit, goldenOrbit, goldenFractionalPart,
    AxiomDebt.fractionalGapValues, AxiomDebt.sortedFractionalOrbit,
    AxiomDebt.fractionalOrbit] using
    AxiomDebt.three_gap_classic Real.goldenRatio
      Real.goldenRatio_irrational N

end D5.S1.Phase
