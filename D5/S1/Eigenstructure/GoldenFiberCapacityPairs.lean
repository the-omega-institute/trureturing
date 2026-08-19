/- GID: D5/S1/Eigenstructure/GoldenFiberCapacityPairs
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/GoldenFiberCapacityPairs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden fiber capacities use adjacent floor and ceiling pairs. -/

import D5.S1.Depth.GoldenPowerRounding

namespace D5.S1.Eigenstructure.GoldenFiberCapacityPairs

open D5.S1.Depth.GoldenPowerRounding

/- The residual's explicit capacity clause is the finite-set form of the
   already proved individual floor and ceiling values. -/
theorem golden_fiber_capacity_pairs :
    ({⌊Real.goldenRatio ^ 3⌋, ⌈Real.goldenRatio ^ 3⌉} : Finset ℤ) = {4, 5} ∧
      ({⌊Real.goldenRatio ^ 2⌋, ⌈Real.goldenRatio ^ 2⌉} : Finset ℤ) = {2, 3} := by
  rcases golden_power_floor_ceil_pairs with ⟨h3f, h3c, h2f, h2c⟩
  rw [h3f, h3c, h2f, h2c]
  constructor <;> rfl

end D5.S1.Eigenstructure.GoldenFiberCapacityPairs
