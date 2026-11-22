/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite two-term midpoint limsup for original signed shrinking prime windows. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootMidpointAverage
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMidpointWindowTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

/-- The original normalized signed prime window, corrected at its midpoint, has a finite
limsup with the two logarithmic terms of the exponential root average. -/
theorem signed_window_even_cutoff_midpoint_limsup (hRH : RiemannHypothesis)
    (m r : ℕ) (hm : 2 ≤ m) (heven : m + 1 = 2 * r) :
    let s := orderRate m
    let cm := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
    let V := fun L u : ℝ =>
      |signedWindowResidual m (Real.exp u) (Real.exp (u + L)) /
        powerGap s (Real.exp u) (Real.exp (u + L)) + cm + (μ r : ℝ) * rootSignal r (u + L / 2)|
    ∃ C > 0, ∀ L : ℝ, 0 < L → L ≤ 1 / 4 →
      (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (V L) ∧
      |limsup (V L) atTop -
        |(μ r : ℝ)| * ((L / (8 * s)) * (Real.log (1 / L) + Real.log (2 * r) - 2 * c + 1 / 2))| ≤
        |(μ r : ℝ)| * C * L ^ 2 * (1 + Real.log (1 / L)) ^ 2 := by
  have hr : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  simpa only [mul_assoc] using signed_window_midpoint_transfer hRH m r hm heven
    (fun L => L ^ 2 * (1 + Real.log (1 / L)) ^ 2)
    (by simpa only [mul_assoc] using root_signal_exponential_midpoint hRH hr)

#print axioms signed_window_even_cutoff_midpoint_limsup

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
