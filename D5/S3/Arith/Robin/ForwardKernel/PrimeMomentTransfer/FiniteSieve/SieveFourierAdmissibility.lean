/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFourierAdmissibility
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFourierAdmissibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: SmoothPositiveWeight compactly supported interval weights have quadratic Fourier decay. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveSmoothKernel
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveKuperbergDefs
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Fourier admissibility of the positively shifted smooth interval averages. -/

open Set MeasureTheory
open scoped Topology FourierTransform Convolution

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem schwartz_fourier_decay (g : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, 1 ≤ |ξ| →
      ‖FourierTransform.fourier (g : ℝ → ℂ) ξ‖ ≤ C / ξ ^ 2 := by
  let C := SchwartzMap.seminorm ℝ 2 0 (FourierTransform.fourier g)
  refine ⟨C, apply_nonneg _ _, ?_⟩
  intro ξ hξ
  have hpos : 0 < ξ ^ 2 := by
    have : ξ ≠ 0 := by intro he; norm_num [he] at hξ
    exact sq_pos_of_ne_zero this
  apply (le_div_iff₀ hpos).mpr
  simpa only [C, SchwartzMap.fourier_coe, Real.norm_eq_abs, sq_abs, mul_comm] using
    SchwartzMap.norm_pow_mul_le_seminorm ℝ (FourierTransform.fourier g) 2 ξ

private theorem smoothed_interval_eq_convolution (δ : ℝ) (hδ : 0 < δ) (a b : ℝ) :
    smoothedInterval δ hδ a b =
      convolution (smoothingKernel δ hδ) ((Ioc a b).indicator (fun _ : ℝ => (1 : ℝ)))
        (ContinuousLinearMap.mul ℝ ℝ) volume := by
  classical
  funext x
  unfold smoothedInterval convolution
  apply integral_congr_ae
  filter_upwards [] with r
  have hmem : x ∈ Ioc (a + r) (b + r) ↔ x - r ∈ Ioc a b := by
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [ContinuousLinearMap.mul_apply', indicator_apply, hmem]


private theorem smoothed_interval_contDiff (δ : ℝ) (hδ : 0 < δ) (a b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothedInterval δ hδ a b) := by
  rw [smoothed_interval_eq_convolution]
  apply (sieveSmoothingBump δ hδ).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ) (sieveSmoothingBump δ hδ).contDiff_normed
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr
    (integrableOn_const (by simp))).locallyIntegrable

private theorem fourier_identification (f : ℝ → ℝ) (ξ : ℝ) :
    fourierAt f ξ = FourierTransform.fourier (fun x => (f x : ℂ)) ξ := by
  rw [fourierAt, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  have he : -(2 * (Real.pi : ℂ) * (x : ℂ) * (ξ : ℂ)) * Complex.I =
      ((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, smul_eq_mul, mul_comm]

private theorem fourier_decay_of_smooth_compact (f : ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) : QuadraticFourierDecay f := by
  let g : SchwartzMap ℝ ℂ :=
    (hc.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hf)
  obtain ⟨C, hC, hbound⟩ := schwartz_fourier_decay g
  refine ⟨C, hC, ?_⟩
  intro ξ hξ
  rw [fourier_identification]
  exact hbound ξ hξ

private theorem smoothed_interval_support_positive (δ : ℝ) (hδ : 0 < δ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    tsupport (smoothedInterval δ hδ a b) ⊆ Ioi 0 := by
  intro x hx
  have hlower := ((smooth_interval_support δ hδ a b ha hab).2 hx).1
  change 0 < x
  linarith

/-- Positively shifted smooth interval averages satisfy the real smooth-weight
and quadratic Fourier-decay conditions. -/
theorem smooth_interval_admissible (δ : ℝ) (hδ : 0 < δ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    SmoothPositiveWeight (smoothedInterval δ hδ a b) ∧ QuadraticFourierDecay (smoothedInterval δ hδ a b) := by
  have hs := smoothed_interval_contDiff δ hδ a b
  have hc := (smooth_interval_support δ hδ a b ha hab).1
  exact ⟨⟨hs, hc, smoothed_interval_support_positive δ hδ a b ha hab⟩,
    fourier_decay_of_smooth_compact _ hs hc⟩


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
