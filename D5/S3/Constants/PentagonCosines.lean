/- GID: D5/S3/Constants/PentagonCosines
   generality: I
   mirror-B: D5/B/S3/Constants/PentagonCosines
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The doubled pentagon cosines read the golden ratio, its inverse, and root five. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

/- Provenance: Native proof over pinned mathlib. -/

namespace D5.S3.Constants.PentagonCosines

/-- The obtuse pentagon cosine: `cos (2π/5) = (√5 - 1) / 4`, by the
double-angle formula applied to the closed form of `cos (π/5)`. -/
private theorem cos_two_pi_div_five_eq :
    Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  have harg : (2 : ℝ) * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [harg, Real.cos_two_mul, Real.cos_pi_div_five]
  linear_combination h5 / 8

/-- Doubling the acute pentagon cosine yields the golden ratio itself. -/
private theorem two_cos_pi_div_five :
    2 * Real.cos (Real.pi / 5) = Real.goldenRatio := by
  rw [Real.cos_pi_div_five]
  change 2 * ((1 + Real.sqrt 5) / 4) = (1 + Real.sqrt 5) / 2
  ring

/-- Doubling the obtuse pentagon cosine yields the inverse golden ratio. -/
private theorem two_cos_two_pi_div_five :
    2 * Real.cos (2 * Real.pi / 5) = Real.goldenRatio⁻¹ := by
  rw [cos_two_pi_div_five_eq, Real.inv_goldenRatio]
  change 2 * ((Real.sqrt 5 - 1) / 4) = -((1 - Real.sqrt 5) / 2)
  ring

/--
The regular pentagon reads the golden ratio exactly: doubling the cosine at
the acute pentagon angle `π/5` gives `φ`, doubling it at the obtuse angle
`2π/5` gives `φ⁻¹`, the two doubles sum to `√5` — the square root of the
discriminant five shared by both readings — and the obtuse double is
irrational, so no rational lattice register accommodates the five-fold turn.
-/
theorem pentagon_golden_cosines :
    2 * Real.cos (Real.pi / 5) = Real.goldenRatio ∧
      2 * Real.cos (2 * Real.pi / 5) = Real.goldenRatio⁻¹ ∧
      2 * Real.cos (Real.pi / 5) + 2 * Real.cos (2 * Real.pi / 5) =
        Real.sqrt 5 ∧
      Irrational (2 * Real.cos (2 * Real.pi / 5)) := by
  refine ⟨two_cos_pi_div_five, two_cos_two_pi_div_five, ?_, ?_⟩
  · rw [two_cos_pi_div_five, two_cos_two_pi_div_five, Real.inv_goldenRatio,
      ← sub_eq_add_neg]
    exact Real.goldenRatio_sub_goldenConj
  · rw [two_cos_two_pi_div_five]
    exact Real.goldenRatio_irrational.inv

end D5.S3.Constants.PentagonCosines
