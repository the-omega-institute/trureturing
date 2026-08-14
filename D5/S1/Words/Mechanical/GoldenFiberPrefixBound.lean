/- GID: D5/S1/Words/Mechanical/GoldenFiberPrefixBound
   generality: I
   mirror-B: D5/B/S1/Words/Mechanical/GoldenFiberPrefixBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound each finite golden-fiber prefix by its elementary linear majorant. -/

import D5.S1.Words.Mechanical.GoldenFiberPrefixCount

namespace D5.S1.Words.Mechanical.GoldenFiberPrefixBound

open GoldenFiberPrefixCount

/-- The positive-indexed golden-fiber prefix sum has the elementary linear bound
from the leading clause of the source bundle. -/
theorem golden_fiber_prefix_sum_le (T : Nat) :
    ((∑ k ∈ Finset.range T, goldenFiberLetter (k + 1) : Int) : Real) ≤
      Real.goldenRatio * (T : Real) + 2 := by
  rw [golden_fiber_prefix_count]
  have hfloor := Int.floor_le (Real.goldenRatio * ((T + 1 : Nat) : Real))
  have hphi := Real.goldenRatio_lt_two
  push_cast at hfloor ⊢
  nlinarith

example : ∃ T : Nat, T = 0 := ⟨0, rfl⟩

#print axioms golden_fiber_prefix_sum_le

end D5.S1.Words.Mechanical.GoldenFiberPrefixBound
