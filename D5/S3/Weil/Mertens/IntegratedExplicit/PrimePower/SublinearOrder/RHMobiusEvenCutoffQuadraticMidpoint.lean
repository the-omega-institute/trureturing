/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffQuadraticMidpoint
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffQuadraticMidpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A quadratic midpoint limsup remainder for the original signed prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoffMidpoint
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootQuadraticMidpoint
import Batteries.Tactic.OpenPrivate

/-! Transfer the quadratic root-average estimate to the full signed prime window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open private signed_window_midpoint_transfer from
  D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoffMidpoint

/-- The original normalized signed prime window, corrected at its midpoint, has a finite
limsup with a quadratic remainder at every width up to one quarter. -/
theorem signed_window_even_cutoff_midpoint_limsup_quadratic (hRH : RiemannHypothesis)
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
        |(μ r : ℝ)| * C * L ^ 2 := by
  have hr : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  simpa only [mul_assoc] using signed_window_midpoint_transfer hRH m r hm heven
    (fun L => L ^ 2) (root_signal_exponential_midpoint_quadratic hRH hr)

#print axioms signed_window_even_cutoff_midpoint_limsup_quadratic

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
