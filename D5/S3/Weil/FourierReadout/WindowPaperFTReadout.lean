/- GID: D5/S3/Weil/FourierReadout/WindowPaperFTReadout
   generality: G
   mirror-B: D5/B/S3/Weil/FourierReadout/WindowPaperFTReadout
   mirror-E: none(waiver:analytic-integral-identification)
   anchors: []
   digest: Identify the existing plus-sign paperFT on zero-extended L2 windows with its actual Hilbert representer. -/

import D5.S3.Weil.ZetaCore.PaperFT
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Library-first: `Zeta23.paperFT`, its real-frequency Mathlib dictionary, and
`norm_cexp_I_mul_le` remain the Fourier owners. This file constructs an L2
representer for that same integral. It uses Mathlib's existing L2 space,
inner product and a.e. quotient, not a new Fourier transform or Plancherel law.
The window has ordinary Lebesgue measure, not probability-normalized measure.
The positive-exponential convention is important: the representer is
conj(exp(I*z*x)), equivalently exp(-I*conj(z)*x).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.FourierReadout.WindowPaperFTReadout

open MeasureTheory Set Complex
open scoped ComplexConjugate ComplexInnerProductSpace

/-- An abbreviation for Mathlib's ordinary complex L2 space on the window. -/
abbrev WindowL2 (a : ℝ) := Lp ℂ 2 (volume.restrict (Icc (-a) a))

private theorem finite_window (a : ℝ) :
    IsFiniteMeasure (volume.restrict (Icc (-a) a)) := by
  constructor
  simp [Real.volume_Icc]

private theorem kernel_memLp (a : ℝ) (z : ℂ) :
    MemLp (fun x : ℝ => conj (Complex.exp (I * z * x))) 2
      (volume.restrict (Icc (-a) a)) := by
  letI := finite_window a
  apply MemLp.of_bound (by fun_prop) (Real.exp (|z.im| * |a|))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [norm_conj]
  exact Zeta23.norm_cexp_I_mul_le
    ((abs_le.mpr hx).trans (le_abs_self a))

/-- The actual representing vector. Its construction proves square integrability. -/
def windowKernel (a : ℝ) (z : ℂ) : WindowL2 a :=
  (kernel_memLp a z).toLp (fun x : ℝ => conj (Complex.exp (I * z * x)))

private theorem kernel_coe (a : ℝ) (z : ℂ) :
    windowKernel a z =ᵐ[volume.restrict (Icc (-a) a)]
      (fun x : ℝ => conj (Complex.exp (I * z * x))) :=
  (kernel_memLp a z).coeFn_toLp

private theorem inner_integrand (a : ℝ) (z : ℂ) (f : WindowL2 a) :
    (fun x : ℝ => ⟪windowKernel a z x, f x⟫_ℂ) =ᵐ[volume.restrict (Icc (-a) a)]
      (fun x : ℝ => f x * Complex.exp (I * z * x)) := by
  filter_upwards [kernel_coe a z] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

/-- The complex Fourier integrand is integrable for every L2 window vector,
including discontinuous zero extensions. -/
theorem window_fourier_integrable (a : ℝ) (z : ℂ) (f : WindowL2 a) :
    Integrable (fun x : ℝ => (Icc (-a) a).indicator (f : ℝ → ℂ) x *
      Complex.exp (I * z * x)) := by
  have hi : Integrable (fun x : ℝ => f x * Complex.exp (I * z * x))
      (volume.restrict (Icc (-a) a)) :=
    (L2.integrable_inner (𝕜 := ℂ) (windowKernel a z) f).congr (inner_integrand a z f)
  have he : (fun x : ℝ => (Icc (-a) a).indicator (f : ℝ → ℂ) x *
      Complex.exp (I * z * x)) =
      (Icc (-a) a).indicator (fun x : ℝ => f x * Complex.exp (I * z * x)) := by
    funext x
    by_cases hx : x ∈ Icc (-a) a <;> simp [hx]
  rw [he, integrable_indicator_iff measurableSet_Icc]
  exact hi

/-- Exact identification with the existing paperFT integral. No evenness,
smoothness, Fourier-series expansion or identification premise is required. -/
theorem paperFT_window_eq_inner (a : ℝ) (z : ℂ) (f : WindowL2 a) :
    Zeta23.paperFT ((Icc (-a) a).indicator (f : ℝ → ℂ)) z =
      ⟪windowKernel a z, f⟫_ℂ := by
  rw [Zeta23.paperFT_def, L2.inner_def]
  have he : (fun x : ℝ => (Icc (-a) a).indicator (f : ℝ → ℂ) x *
      Complex.exp (I * z * x)) =
      (Icc (-a) a).indicator (fun x : ℝ => f x * Complex.exp (I * z * x)) := by
    funext x
    by_cases hx : x ∈ Icc (-a) a <;> simp [hx]
  rw [he, integral_indicator measurableSet_Icc]
  exact integral_congr_ae (inner_integrand a z f).symm

/-- The same identity for a supplied representative supported in the window.
The a.e. quotient is eliminated, so existing compactly supported functions
can use the result without a new transform definition. -/
theorem paperFT_eq_inner_toLp (a : ℝ) (z : ℂ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Icc (-a) a)))
    (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) :
    Zeta23.paperFT f z = ⟪windowKernel a z, hf.toLp f⟫_ℂ := by
  rw [Zeta23.paperFT_def, L2.inner_def]
  have he : (fun x : ℝ => f x * Complex.exp (I * z * x)) =
      (Icc (-a) a).indicator (fun x : ℝ => f x * Complex.exp (I * z * x)) := by
    funext x
    by_cases hx : x ∈ Icc (-a) a
    · simp [hx]
    · simp [hx, hsupp x hx]
  rw [he, integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [kernel_coe a z, hf.coeFn_toLp] with x hx hxf
  simp [hx, hxf, RCLike.inner_apply, mul_comm]

private theorem l2_norm_sq_integral {μ : Measure ℝ} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = (⟪f, f⟫_ℂ).re := (inner_self_eq_norm_sq (𝕜 := ℂ) f).symm
    _ = ∫ x : ℝ, (⟪f x, f x⟫_ℂ).re ∂μ :=
      (integral_re (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = _ := by simp only [inner_self_eq_norm_sq]

/-- The kernel norm is computed from its actual integral; the sign agrees
with paperFT's positive exponential. -/
theorem windowKernel_norm_sq (a : ℝ) (z : ℂ) :
    ‖windowKernel a z‖ ^ 2 =
      ∫ x in Icc (-a) a, Real.exp (-(2 * z.im * x)) := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [kernel_coe a z] with x hx
  rw [hx, norm_conj, Zeta23.norm_cexp_I_mul, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- At a real frequency the ordinary, unnormalized window measure gives
exactly 2*a for the squared readout norm. -/
theorem windowKernel_norm_sq_real {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    ‖windowKernel a (t : ℂ)‖ ^ 2 = 2 * a := by
  rw [windowKernel_norm_sq]
  simp only [Complex.ofReal_im, mul_zero, zero_mul, neg_zero, Real.exp_zero]
  rw [setIntegral_const, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ a - -a), smul_eq_mul, mul_one]
  ring

/-- A uniform complex-strip kernel bound in the ordinary L2 norm. This
includes the zero-length window and does not require a real frequency. -/
theorem windowKernel_norm_le {a b : ℝ} (ha : 0 ≤ a) (z : ℂ) (hz : |z.im| ≤ b) :
    ‖windowKernel a z‖ ≤ Real.sqrt (2 * a) * Real.exp (b * a) := by
  letI := finite_window a
  have hraw : ∀ᵐ x ∂volume.restrict (Icc (-a) a),
      ‖conj (Complex.exp (I * z * x))‖ ≤ Real.exp (b * a) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_conj]
    exact (Zeta23.norm_cexp_I_mul_le (abs_le.mpr hx)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz ha))
  have hbound : ‖windowKernel a z‖ ^ 2 ≤ (2 * a) * (Real.exp (b * a)) ^ 2 := by
    rw [l2_norm_sq_integral]
    calc
      _ ≤ ∫ _x in Icc (-a) a, (Real.exp (b * a)) ^ 2 := by
        apply integral_mono_ae
          (((windowKernel a z).memLp.norm).integrable_sq) (integrable_const _)
        filter_upwards [kernel_coe a z, hraw] with x hx hb
        rw [hx]
        exact pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = _ := by
        rw [setIntegral_const, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ a - -a), smul_eq_mul]
        ring
  have hs : (Real.sqrt (2 * a) * Real.exp (b * a)) ^ 2 =
      (2 * a) * (Real.exp (b * a)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hp : 0 ≤ Real.sqrt (2 * a) * Real.exp (b * a) := by positivity
  nlinarith [norm_nonneg (windowKernel a z)]

/-- Finite-window L2 errors give actual paperFT errors, uniformly in the
horizontal coordinate. Existing Cauchy--Schwarz is applied to the identified
Fourier representer; no new Fourier inequality is postulated. -/
theorem paperFT_window_sub_le {a b : ℝ} (ha : 0 ≤ a) (f g : WindowL2 a)
    (z : ℂ) (hz : |z.im| ≤ b) :
    ‖Zeta23.paperFT ((Icc (-a) a).indicator (f : ℝ → ℂ)) z -
      Zeta23.paperFT ((Icc (-a) a).indicator (g : ℝ → ℂ)) z‖ ≤
        (Real.sqrt (2 * a) * Real.exp (b * a)) * ‖f - g‖ := by
  rw [paperFT_window_eq_inner, paperFT_window_eq_inner, ← inner_sub_right]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_right (windowKernel_norm_le ha z hz) (norm_nonneg _))

#print axioms paperFT_window_eq_inner
#print axioms paperFT_window_sub_le

end D5.S3.Weil.FourierReadout.WindowPaperFTReadout
