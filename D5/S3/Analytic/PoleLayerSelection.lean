/- GID: D5/S3/Analytic/PoleLayerSelection
   generality: I
   mirror-B: D5/B/S3/Analytic/PoleLayerSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A shifted inverse power series selects coefficients by index subtraction. -/

import Mathlib.RingTheory.PowerSeries.Inverse

/- Provenance: thin honest assembly over pinned mathlib's power-series
   coefficient shift (`PowerSeries.coeff_X_pow_mul'`) and constant-scaling
   (`PowerSeries.coeff_C_mul`) declarations. -/

namespace D5.S3.Analytic.PoleLayerSelection

open PowerSeries

/-- Multiplication by the fourth-order pole layer shifts coefficient extraction
from row `a` to row `a - 4k`; the signed order and residue factors remain scalar. -/
theorem pole_layer_coefficient
    (regular : ℚ⟦X⟧) (residue : ℚ) (a : ℕ) (k : ℕ+)
    (hka : 4 * k.1 ≤ a) :
    coeff a
        (C (((-1 : ℚ) ^ (k.1 - 1) / k.1) * residue) *
          X ^ (4 * k.1) * (regular⁻¹) ^ k.1) =
      ((-1 : ℚ) ^ (k.1 - 1) / k.1) *
        coeff (a - 4 * k.1) ((regular⁻¹) ^ k.1) * residue := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos hka]
  ring

end D5.S3.Analytic.PoleLayerSelection
