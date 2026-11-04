/- GID: D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive-axis Stieltjes transform of the power Poisson density. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The positive-axis transform used by the logarithmic Renyi representation. -/

namespace D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight

open Real Set MeasureTheory

noncomputable section

/-- The power Poisson density after the substitution `p = q ^ α`. -/
def density (α q : ℝ) : ℝ :=
  α * q ^ (α - 1) * (-Real.sin (Real.pi * α)) /
    (Real.pi * (α - 1) * (1 - 2 * q ^ α * Real.cos (Real.pi * α) + (q ^ α) ^ 2))

/-- Reciprocal reflection preserves the density with its change-of-variables factor. -/
theorem density_reflection {α q : ℝ} (hq : 0 < q)
    (ha1 : α ≠ 1) (hc : Real.cos (Real.pi * α) < 1) :
    density α q⁻¹ / q ^ 2 = density α q := by
  have hp := Real.rpow_pos_of_pos hq α
  have hD : 0 < 1 - 2 * q ^ α * Real.cos (Real.pi * α) + (q ^ α) ^ 2 := by
    nlinarith [mul_pos hp (sub_pos.mpr hc), sq_nonneg (q ^ α - 1)]
  dsimp only [density]
  rw [Real.inv_rpow hq.le, Real.inv_rpow hq.le, Real.rpow_sub_one hq.ne']
  field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr ha1 |
    nlinarith [hD])
  ring

/-- Stieltjes transform on the positive axis, with its pole at `r = 1` subtracted. -/
theorem stieltjes_integral {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    IntegrableOn (fun q => density α q / (r + q)) (Ioi 0) ∧
      (∫ q in Ioi (0 : ℝ), density α q / (r + q)) =
        1 / ((α - 1) * (1 - r)) -
          α * r ^ (α - 1) / ((α - 1) * (1 - r ^ α)) := by
  sorry

end

end D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
