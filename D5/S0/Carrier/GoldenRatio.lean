/- GID: D5/S0/Carrier/GoldenRatio
   generality: I
   mirror-B: D5/B/S0/Carrier/GoldenRatio
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The real golden ratio satisfies its radical, fixed-point, and conjugate identities. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S0.Carrier

/-- The three identities that characterize the real golden ratio in the source claim. -/
theorem golden_ratio_spec :
    Real.goldenRatio = (1 + Real.sqrt 5) / 2 ∧
      Real.goldenRatio ^ 2 = Real.goldenRatio + 1 ∧
      1 - Real.goldenRatio = -(1 / Real.goldenRatio) := by
  refine ⟨rfl, Real.goldenRatio_sq, ?_⟩
  rw [Real.one_sub_goldenConj, one_div, Real.inv_goldenRatio]
  simp

end D5.S0.Carrier
