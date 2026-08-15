/- GID: D5/S3/ResourceOrder/NominalDebtScale
   generality: G
   mirror-B: D5/B/S3/ResourceOrder/NominalDebtScale
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed nominal debt burden scales inversely under uniform price scaling. -/

/- Library-search audit trail (2026-08-16):
   * Pinned Mathlib and Loogle both return `div_mul_eq_div_mul_one_div` as the
     exact division-by-a-product identity.
   * D5 contains no theorem about fixed nominal debt burden under price scaling.
   * The proof below applies the Mathlib identity and only reorders commutative factors.
-/

import Mathlib.Data.Real.Basic

namespace D5.S3.ResourceOrder.NominalDebtScale

/-- Uniformly scaling a positive price while holding positive nominal debt fixed scales
its real burden by the reciprocal factor. -/
theorem fixed_nominal_debt_burden_scales_inversely
    (D price scale : Real) (_hD : 0 < D) (_hprice : 0 < price) (_hscale : 0 < scale) :
    D / (scale * price) = (1 / scale) * (D / price) := by
  calc
    D / (scale * price) = D / scale * (1 / price) :=
      div_mul_eq_div_mul_one_div D scale price
    _ = (1 / scale) * (D / price) := by
      simp only [div_eq_mul_inv, one_mul]
      ac_rfl

#print axioms fixed_nominal_debt_burden_scales_inversely

end D5.S3.ResourceOrder.NominalDebtScale
