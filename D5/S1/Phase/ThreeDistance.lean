/- GID: D5/S1/Phase/ThreeDistance
   generality: G
   mirror-B: none(waiver:classical-result-tail-is-documented-at-the-formal-site)
   mirror-E: none(waiver:upstream-mit-formalization-is-the-proof-source)
   anchors: []
   digest: Golden rotation points have at most three distinct cyclic adjacent gaps. -/

import D5.S1.Phase.ThreeGap.Main

namespace D5.S1.Phase

/-- The `N` points `{n * phi}` for `0 ≤ n < N`. -/
noncomputable def goldenOrbit (N : ℕ) : Finset ℝ :=
  ThreeGap.orbit Real.goldenRatio N

/-- Adjacent gaps of the sorted orbit, including the last-to-first circle gap. -/
noncomputable def goldenGapValues (N : ℕ) : Finset ℝ :=
  (ThreeGap.gaps Real.goldenRatio N).toFinset

/--
Three-gap theorem for the golden rotation: after sorting `{n * phi}` for
`0 ≤ n < N` around the unit circle, the adjacent cyclic gaps have at most three
distinct lengths.
-/
theorem three_gap (N : ℕ) : (goldenGapValues N).card ≤ 3 := by
  exact ThreeGap.three_gap_card_le_three Real.goldenRatio N

end D5.S1.Phase
