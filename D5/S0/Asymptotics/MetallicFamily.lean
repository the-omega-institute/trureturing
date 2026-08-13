/- GID: D5/S0/Asymptotics/MetallicFamily
   generality: G
   mirror-B: D5/B/S0/Asymptotics/MetallicFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The explicit quadratic-family value has reciprocal equal to its shift by the integer parameter; this closes only that elementary clause of source theorem 5.7. -/

import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S0.Asymptotics.MetallicFamily

noncomputable def metallicValue (n : ℕ) : ℝ :=
  ((n : ℝ) + Real.sqrt (n ^ 2 + 4)) / 2

/- The radical is positive, so the quadratic relation can be used without a
   hidden sign choice when clearing the reciprocal. -/
theorem metallic_family_value (n : ℕ) :
    metallicValue n = ((n : ℝ) + Real.sqrt (n ^ 2 + 4)) / 2 ∧
      1 / metallicValue n = metallicValue n - n := by
  dsimp [metallicValue]
  constructor
  · rfl
  · let r : ℝ := Real.sqrt (n ^ 2 + 4)
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      exact Real.sqrt_nonneg _
    have hrad : r ^ 2 = (n : ℝ) ^ 2 + 4 := by
      dsimp [r]
      rw [Real.sq_sqrt]
      positivity
    have hpos : 0 < (n : ℝ) + r := by
      nlinarith
    dsimp [r] at hrad hpos ⊢
    field_simp [hpos.ne']
    nlinarith

end D5.S0.Asymptotics.MetallicFamily
