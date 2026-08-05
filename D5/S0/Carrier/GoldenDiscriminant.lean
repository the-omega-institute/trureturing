/- GID: D5/S0/Carrier/GoldenDiscriminant
   generality: I
   mirror-B: D5/B/S0/Carrier/GoldenDiscriminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden polynomial has discriminant five and the golden ratio satisfies it. -/

import D5.S0.Carrier.GoldenRatio

namespace D5.S0.Carrier

/-- The discriminant of `x^2 - x - 1` is five, alongside its golden fixed point. -/
theorem golden_discriminant_spec :
    ((-1 : ℤ) ^ 2 - 4 * 1 * (-1) = 5) ∧
      Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := by
  refine ⟨by norm_num, ?_⟩
  exact golden_ratio_spec.2.1

end D5.S0.Carrier
