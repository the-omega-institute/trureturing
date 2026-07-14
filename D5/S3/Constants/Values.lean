/- GID: D5/S3/Constants/Values
   generality: I
   mirror-B: none(waiver:canonical-values-live-in-evidence-projection)
   mirror-E: D5/E/values--json
   anchors: []
   digest: Define the exact content referenced by the canonical values projection. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace D5.S3.Constants.Values

/-- The golden ratio is the positive quadratic root used by the values catalog. -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- The exact h-side constant is `(5 * sqrt 5 - 3) / 24`. -/
noncomputable def ah : ℝ := (5 * Real.sqrt 5 - 3) / 24

/-- The registered-open Bh reference center is the exact rational `-0.14076`. -/
noncomputable def bh : ℝ := -3519 / 25000

/-- The exact net-value coefficient is one half of the golden ratio. -/
noncomputable def c0 : ℝ := goldenRatio / 2

/-- The twisted cotangent constant is defined by its exact infinite series. -/
noncomputable def cPhi : ℝ :=
  -(1 / (2 * Real.pi)) *
    ∑' k : ℕ,
      let n : ℝ := k + 1
      Real.cos (4 * Real.pi * n * goldenRatio) *
        (Real.cos (Real.pi * n * goldenRatio) / Real.sin (Real.pi * n * goldenRatio)) / n

/-- The exact elementary shell is `(137 - 61 * sqrt 5) / 24`. -/
noncomputable def e : ℝ := (137 - 61 * Real.sqrt 5) / 24

/-- The registered-open T0 reference center is the exact rational `-0.0862145`. -/
noncomputable def t0 : ℝ := -172429 / 2000000

/-- The registered-open T1 reference center is the exact rational `0.03182`. -/
noncomputable def t1 : ℝ := 1591 / 50000

/-- The c1 relation is evaluated at the registered T0 reference center. -/
noncomputable def c1 : ℝ := 2 * Real.sqrt 5 * t0 + e

/-- The c2 relation is evaluated at the registered Bh, T0, and T1 reference centers. -/
noncomputable def c2 : ℝ :=
  (Real.sqrt 5 - 1) * bh / 2 +
    (3 - 7 * Real.sqrt 5 / 2) * t0 +
    3 * Real.sqrt 5 * t1 + (269 * Real.sqrt 5 - 623) / 48

/-- The exact correction scale is `sqrt 5` times the golden ratio. -/
noncomputable def cStar : ℝ := Real.sqrt 5 * goldenRatio

/-- The registered-open exchange-loss mean reference center is `-0.00000717`. -/
noncomputable def deltaMean : ℝ := -717 / 100000000

/-- The exact correction-fiber mean is negative one half. -/
noncomputable def hBar : ℝ := -1 / 2

/-- The exact slope constant is the reciprocal of twice the golden ratio. -/
noncomputable def kappa : ℝ := 1 / (2 * goldenRatio)

/-- The exact dimension-reduction coefficient is `(1 + sqrt 5) / 12`. -/
noncomputable def s1 : ℝ := (1 + Real.sqrt 5) / 12

private theorem sqrt_five_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_five_sq : (Real.sqrt 5) ^ 2 = 5 := by norm_num

private theorem sqrt_five_lt_three : Real.sqrt 5 < 3 := by
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

/-- The exact h-side constant is positive. -/
theorem ah_pos : 0 < ah := by
  rw [ah]
  nlinarith [sqrt_five_sq, sqrt_five_pos]

/-- The Bh reference center is negative. -/
theorem bh_neg : bh < 0 := by norm_num [bh]

/-- The net-value coefficient lies strictly between zero and one. -/
theorem c0_mem_unit : 0 < c0 ∧ c0 < 1 := by
  constructor
  · simp only [c0, goldenRatio]
    positivity
  · simp only [c0, goldenRatio]
    nlinarith [sqrt_five_lt_three]

/-- The exact elementary shell is positive. -/
theorem e_pos : 0 < e := by
  simp only [e]
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

/-- The T0 reference center is negative. -/
theorem t0_neg : t0 < 0 := by norm_num [t0]

/-- The T1 reference center is positive. -/
theorem t1_pos : 0 < t1 := by norm_num [t1]

/-- The c1 relation at the registered centers is negative. -/
theorem c1_neg : c1 < 0 := by
  simp only [c1, t0, e]
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

/-- The c2 relation at the registered centers is positive. -/
theorem c2_pos : 0 < c2 := by
  simp only [c2, bh, t0, t1]
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

/-- The exact correction scale is positive. -/
theorem cStar_pos : 0 < cStar := by
  simp only [cStar, goldenRatio]
  positivity

/-- The exchange-loss mean reference center is negative. -/
theorem deltaMean_neg : deltaMean < 0 := by norm_num [deltaMean]

/-- The correction-fiber mean is negative. -/
theorem hBar_neg : hBar < 0 := by norm_num [hBar]

/-- The exact slope constant is positive. -/
theorem kappa_pos : 0 < kappa := by
  simp only [kappa, goldenRatio]
  positivity

/-- The exact dimension-reduction coefficient is positive. -/
theorem s1_pos : 0 < s1 := by
  simp only [s1]
  positivity

end D5.S3.Constants.Values
