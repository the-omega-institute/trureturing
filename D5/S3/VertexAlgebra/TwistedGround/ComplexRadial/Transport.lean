/- GID: D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Transport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/ComplexRadial/Transport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Identity theorem transport from positive real radii on the original source disk. -/


import D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Candidate
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalRadialSums
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected

/-! The identity theorem transfers the actual positive-real suppliers to the full complex disk. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianComplexRadialContinuation
open OriginalGaussianExternalGeneratedSource

/-- The ONLY equality input of transport: literal original kernel equality at
positive REAL r, with the original complex source variables and sqrt-r bounds. -/
def RealRadialSupplier (square e f : Bool) (u v : ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    ‖u‖ + Real.sqrt r < 1 → ‖v‖ + Real.sqrt r < 1 →
    kernelMode square e f u v (Real.sqrt r : ℂ) =
      signedCandidate square e f u v (r : ℂ)

private lemma kernel_amplitude_analyticOnNhd (square e f : Bool) (u v : ℂ) :
    AnalyticOnNhd ℂ (fun z => kernelMode square e f u v z)
      (Metric.ball 0 (sourceRadius u v)) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro z hz
  have hzR : ‖z‖ < sourceRadius u v := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hd := (norm_lt_sourceRadius_iff u v z).1 hzR
  exact (OriginalGaussianExternalRadialSums.kernel_complex_derivative
    square e f hd.1 hd.2).2.differentiableWithinAt

/-- Genuine identity-theorem transport for the actual literal kernel and actual
signed formula. Every regularity and denominator fact is derived internally
from the source domain. Zero, axes and diagonal are included without limits
of a divided identity. -/
theorem kernelMode_eq_candidate_complex_of_real (square e f : Bool) {u v z : ℂ}
    (realSupplier : RealRadialSupplier square e f u v)
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    kernelMode square e f u v z = signedCandidate square e f u v (z ^ 2) := by
  have hu1 : ‖u‖ < 1 := by linarith [norm_nonneg z]
  have hv1 : ‖v‖ < 1 := by linarith [norm_nonneg z]
  have hR := sourceRadius_pos hu1 hv1
  have hR1 := sourceRadius_le_one u v
  have hzR := (norm_lt_sourceRadius_iff u v z).2 ⟨hu, hv⟩
  have hK := kernel_amplitude_analyticOnNhd square e f u v
  have hC := candidate_square_analyticOnNhd square e f u v
  have h₀ : (0 : ℂ) ∈ Metric.ball 0 (sourceRadius u v) := by
    simpa only [Metric.mem_ball, dist_self] using hR
  -- Arbitrarily small positive t give real r=t². This closure argument is
  -- equivalent to a positive sequence and avoids a gratuitous sequence API.
  have hacc : (0 : ℂ) ∈ closure
      ({w : ℂ | kernelMode square e f u v w =
        signedCandidate square e f u v (w ^ 2)} \ {0}) := by
    apply Metric.mem_closure_iff.2
    intro ε hε
    obtain ⟨t, ht0, ht⟩ := exists_between (lt_min hR hε)
    have htR : t < sourceRadius u v := lt_of_lt_of_le ht (min_le_left _ _)
    have htε : t < ε := lt_of_lt_of_le ht (min_le_right _ _)
    have ht1 : t < 1 := htR.trans_le hR1
    have hr0 : 0 < t ^ 2 := sq_pos_of_pos ht0
    have hr1 : t ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr ht1) (show 0 < 1 + t by linarith)]
    have hnorm : ‖(t : ℂ)‖ = t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hsource := (norm_lt_sourceRadius_iff u v (t : ℂ)).1
      (by simpa only [hnorm] using htR)
    have hsu : ‖u‖ + Real.sqrt (t ^ 2) < 1 := by
      simpa only [Real.sqrt_sq ht0.le, hnorm] using hsource.1
    have hsv : ‖v‖ + Real.sqrt (t ^ 2) < 1 := by
      simpa only [Real.sqrt_sq ht0.le, hnorm] using hsource.2
    have heq := realSupplier (t ^ 2) hr0 hr1 hsu hsv
    rw [Real.sqrt_sq ht0.le] at heq
    refine ⟨(t : ℂ), ⟨?_, ?_⟩, ?_⟩
    · simpa only [Set.mem_setOf_eq, Complex.ofReal_pow] using heq
    · simpa only [Set.mem_singleton_iff, Complex.ofReal_eq_zero] using ht0.ne'
    · simpa only [dist_zero_left, hnorm] using htε
  have heq := hK.eqOn_of_preconnected_of_mem_closure hC
    Metric.isPreconnected_ball h₀ hacc
  exact heq (by simpa only [Metric.mem_ball, dist_zero_right] using hzR)

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianComplexRadialContinuation
