/- GID: D5/S0/Carrier/Powers/GoldenMidlineFactorization
   generality: I
   mirror-B: D5/B/S0/Carrier/Powers/GoldenMidlineFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor the golden midline marker into half and reciprocal-square components. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S0.Carrier.Powers.GoldenMidlineFactorization

/-- The golden midline marker factors as one half times the reciprocal square. -/
theorem golden_midline_factorization :
    1 / (2 * Real.goldenRatio ^ 2) =
      (1 / 2) * (1 / Real.goldenRatio ^ 2) := by
  exact
    (one_div_mul_one_div
      (a := (2 : Real)) (b := Real.goldenRatio ^ 2)).symm

example : Nonempty Real := inferInstance

#print axioms golden_midline_factorization

end D5.S0.Carrier.Powers.GoldenMidlineFactorization
