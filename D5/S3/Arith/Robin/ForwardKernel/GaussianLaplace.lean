/- GID: D5/S3/Arith/Robin/ForwardKernel/GaussianLaplace
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/GaussianLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The forward paired Laplace regular part has quadratic growth throughout the Gaussian inversion strip. -/

import D5.S3.Analytic.Laplace.GaussianStripControl
import D5.S3.Arith.Robin.ForwardKernel.PairedLaplace

/-! Wider strip bounds for the regular part of the forward response transform. -/

namespace D5.S3.Arith.Robin.ForwardKernel

open D5.S3.Analytic.Laplace.PairedPoleRegularity
open D5.S3.Arith.Robin.ForwardKernel.MellinPolynomialGrowth
open D5.S3.Weil.ZeroData.PairedXiExpansion (PairedXiExpansion)
open ConjectureMachines.Semantics.Riemann.DigammaBinet

noncomputable section
set_option autoImplicit false

theorem forwardPairedLaplaceData_gaussianStrip
    (hRH : RiemannHypothesis) (hVK : VonKochBound) (hXi : PairedXiExpansion hRH) :
    GaussianStripControl
      (forwardPairedLaplaceData hRH hVK hXi (x0 := 3) (by norm_num)).J := by
  let hRem := forward_kernel_mellin_polynomial_remainder hVK (x0 := 3) (by norm_num)
  let R : ℂ → ℂ := Classical.choose hRem
  change GaussianStripControl (forwardRegularPart R)
  exact ⟨(forwardRegularPart_holomorphic (Classical.choose_spec hRem).1).mono
    (fun _ hs => hs.1),
    forwardRegularPart_gaussian_growth (Classical.choose_spec hRem).2.2⟩

end
end D5.S3.Arith.Robin.ForwardKernel
