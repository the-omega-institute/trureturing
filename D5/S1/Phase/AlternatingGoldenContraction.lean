/- GID: D5/S1/Phase/AlternatingGoldenContraction
   generality: I
   mirror-B: D5/B/S1/Phase/AlternatingGoldenContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden negative-axis steps alternate and contract toward the center minus one. -/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Ring

open Filter Topology

namespace D5.S1.Phase.AlternatingGoldenContraction

/-- The affine step centered at `-1` whose displacement reverses sign and
shrinks by the reciprocal cube of the golden ratio. -/
noncomputable def alternatingGoldenStep (x : ℝ) : ℝ :=
  -1 + (-(Real.goldenRatio ^ 3)⁻¹) * (x + 1)

private theorem alternatingGoldenStep_iterate (n : ℕ) (x : ℝ) :
    (alternatingGoldenStep^[n]) x =
      -1 + (-(Real.goldenRatio ^ 3)⁻¹) ^ n * (x + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [alternatingGoldenStep, pow_succ]
      ring

/-- Every orbit of the sign-reversing golden contraction tends to its fixed
center `-1`. -/
theorem alternating_golden_contraction_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => (alternatingGoldenStep^[n]) x) atTop (𝓝 (-1)) := by
  have hpow : 1 < Real.goldenRatio ^ 3 :=
    one_lt_pow₀ Real.one_lt_goldenRatio (by norm_num)
  have hratio : |-(Real.goldenRatio ^ 3)⁻¹| < 1 := by
    rw [abs_neg, abs_inv, abs_of_pos (pow_pos Real.goldenRatio_pos 3)]
    exact inv_lt_one_of_one_lt₀ hpow
  have hzero := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio
  have hscaled := hzero.mul_const (x + 1)
  convert tendsto_const_nhds.add hscaled using 1
  · funext n
    exact alternatingGoldenStep_iterate n x
  · norm_num

end D5.S1.Phase.AlternatingGoldenContraction
