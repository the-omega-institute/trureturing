/- GID: D5/S3/Arith/Robin/ForwardKernel/AveragingBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/AveragingBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise square bounds and pairing identities for forward window averages. -/

import D5.S3.Arith.Robin.ForwardKernel.CrossExponentDefs
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer

/-! Fubini identities for forward averages. -/

namespace D5.S3.Arith.Robin.ForwardKernel.AveragingBounds

open Set MeasureTheory Filter
open VarianceTransferDefs VarianceTransfer CrossExponentDefs

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Averaging and pairing commute when the translated product is jointly integrable. -/
theorem windowAverage_pairing_eq {f z : ℝ → ℝ} {M l r : ℝ}
    (hM : 0 ≤ M) (hlr : l ≤ r)
    (hF : Integrable (fun p : ℝ × ℝ => f (p.1 + p.2) * z p.1)
      ((volume.restrict (Ioc l r)).prod (volume.restrict (Ioc (0 : ℝ) M)))) :
    (∫ x in l..r, windowAverage M f x * z x) =
      (1 / M) * ∫ t in (0 : ℝ)..M, ∫ x in l..r, f (x + t) * z x := by
  simp_rw [windowAverage, div_mul_eq_mul_div, ← intervalIntegral.integral_mul_const,
    intervalIntegral.integral_div]
  simp_rw [intervalIntegral.integral_of_le hlr, intervalIntegral.integral_of_le hM]
  rw [integral_integral_swap hF]
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.AveragingBounds
