/- GID: D5/S3/Analytic/PowerSeries/DottieInverseSeries
   generality: I
   mirror-B: D5/B/S3/Analytic/PowerSeries/DottieInverseSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The prescribed rational arcsine series and its formal compositional inverse. -/

import D5.S3.Analytic.PowerSeries.ScalarComposition
import D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis

/-! The literal rational coefficients and compositional inverse. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter
open scoped Topology PowerSeries

namespace D5.S3.Analytic.PowerSeries.DottieInverseSeries

def alpha (n : ℕ) : ℚ :=
  let k : ℕ := n / 2
  if n % 2 = 0 then 0 else
    (Nat.choose (2 * k) k : ℚ) / ((4 : ℚ) ^ k * ((2 * k + 1 : ℕ) : ℚ))

def arcsine : ℚ⟦X⟧ := PowerSeries.mk alpha

def forward : ℚ⟦X⟧ := 2 * PowerSeries.X + 2 * arcsine

def inverse : ℚ⟦X⟧ := forward.substInvOfIsUnit (by
  have h : PowerSeries.coeff 1 forward = 4 := by
    norm_num [forward, arcsine, alpha]
  rw [h]
  exact isUnit_iff_ne_zero.mpr (by norm_num))

end D5.S3.Analytic.PowerSeries.DottieInverseSeries
