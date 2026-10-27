/- GID: D5/S3/Weil/ZetaExplicit/ExponentialStripSampling
   generality: I
   mirror-B: none(waiver:noncompact-exponential-reproduction)
   mirror-E: none(waiver:infinite-complex-zero-sampling)
   anchors: []
   utility: none
   digest: Noncompact exponential reproduction supplies uniform closed-strip zero sampling. -/

import D5.S3.Weil.ZetaExplicit.WeightedZeroSampling
import D5.S3.Weil.ZetaExplicit.RvM
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

/-!
Candidate mathematical content fixed before compilation: the tilted damping
exp(-a|x|-beta*x), a>1/2, has its literal complex Cauchy Fourier kernel.
The positive real part of its denominator pays a uniform inverse-square
bound on the entire closed half-strip. Existing noncompact Fubini,
Cauchy--Schwarz and actual zero counting are reused, not re-proved.
The future sampling consumer must retain the logarithmic energy of the
exponentially weighted input; original H6 alone does not supply that premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Zeta23.WeilEF.ExponentialStripSampling

open Real Complex Set MeasureTheory Filter
open scoped Topology ComplexConjugate FourierTransform

open private convolution_inversion convolution_norm_sq_le
  weighted_zero_sampling_two_families from
  Zeta23.WeilEF.WeightedZeroSampling

private def damping (a beta x : ℝ) : ℂ :=
  Complex.exp ((-a * |x| - beta * x : ℝ) : ℂ)

private def cauchyKernel (a : ℝ) (z : ℂ) : ℂ :=
  ((a / Real.pi : ℝ) : ℂ) / ((a : ℂ) ^ 2 + z ^ 2)

private def margin (a : ℝ) : ℝ := min 1 (a ^ 2 - 1 / 4)

private def envelope (a : ℝ) : ℝ := a / (Real.pi * margin a)

private theorem margin_pos {a : ℝ} (ha : 1 / 2 < a) : 0 < margin a := by
  apply lt_min (by norm_num)
  nlinarith

private theorem denominator_bound {a : ℝ} (ha : 1 / 2 < a)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    margin a * (1 + z.re ^ 2) ≤ ‖(a : ℂ) ^ 2 + z ^ 2‖ := by
  have hm1 : margin a ≤ 1 := min_le_left _ _
  have hmd : margin a ≤ a ^ 2 - 1 / 4 := min_le_right _ _
  have hzsq : z.im ^ 2 ≤ 1 / 4 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hz
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hm1 (sq_nonneg z.re)
  have hre : ((a : ℂ) ^ 2 + z ^ 2).re = a ^ 2 + z.re ^ 2 - z.im ^ 2 := by
    simp only [pow_two, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hreal : margin a * (1 + z.re ^ 2) ≤ ((a : ℂ) ^ 2 + z ^ 2).re := by
    rw [hre]
    nlinarith only [hmd, hzsq, hmul]
  exact hreal.trans (Complex.re_le_norm _)

private theorem cauchyKernel_bound {a : ℝ} (ha : 1 / 2 < a)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖cauchyKernel a z‖ ≤ envelope a / (1 + z.re ^ 2) := by
  have ha0 : 0 < a := by linarith
  have hm := margin_pos ha
  have hd := denominator_bound ha hz
  rw [cauchyKernel, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos ha0 Real.pi_pos)]
  calc
    _ ≤ (a / Real.pi) / (margin a * (1 + z.re ^ 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = envelope a / (1 + z.re ^ 2) := by
      dsimp only [envelope]
      ring

private theorem tilted_exp_fourier {a beta : ℝ} (ha : 1 / 2 < a)
    (hb : |beta| ≤ 1 / 2) (t : ℝ) :
    Integrable (fun x : ℝ => damping a beta x *
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) ∧
    Zeta23.paperFT (damping a beta) t =
      (2 * (a : ℂ)) / ((a : ℂ) ^ 2 + ((t : ℂ) + Complex.I * (beta : ℂ)) ^ 2) := by
  let cp : ℂ := ((-a - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let cm : ℂ := ((a - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  have hpr : cp.re < 0 := by
    dsimp only [cp]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
    linarith [(abs_le.mp hb).1]
  have hmr : 0 < cm.re := by
    dsimp only [cm]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
    linarith [(abs_le.mp hb).2]
  have hiP := integrableOn_exp_mul_complex_Ioi hpr 0
  have hiM := integrableOn_exp_mul_complex_Iic hmr 0
  let f : ℝ → ℂ := fun x => damping a beta x *
    Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
  have eP : EqOn f (fun x : ℝ => Complex.exp (cp * (x : ℂ))) (Ioi 0) := by
    intro x hx
    dsimp only [f, damping]
    rw [← Complex.exp_add, abs_of_pos hx]
    congr 1
    dsimp only [cp]
    push_cast
    ring
  have eM : EqOn f (fun x : ℝ => Complex.exp (cm * (x : ℂ))) (Iic 0) := by
    intro x hx
    dsimp only [f, damping]
    rw [← Complex.exp_add, abs_of_nonpos hx]
    congr 1
    dsimp only [cm]
    push_cast
    ring
  have hfiP := hiP.congr_fun eP.symm measurableSet_Ioi
  have hfiM := hiM.congr_fun eM.symm measurableSet_Iic
  have hfi : Integrable f := by
    have h := hfiM.union hfiP
    simpa only [Iic_union_Ioi, integrableOn_univ] using h
  refine ⟨hfi, ?_⟩
  change (∫ x : ℝ, f x) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi hfiM hfiP,
    setIntegral_congr_fun measurableSet_Iic eM,
    setIntegral_congr_fun measurableSet_Ioi eP,
    integral_exp_mul_complex_Iic hmr 0, integral_exp_mul_complex_Ioi hpr 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hcp : cp ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.zero_re] at he
    linarith
  have hcm : cm ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.zero_re] at he
    linarith
  have hd : (a : ℂ) ^ 2 + ((t : ℂ) + Complex.I * (beta : ℂ)) ^ 2 ≠ 0 := by
    intro h
    have hp := denominator_bound ha (z := ((t : ℂ) + Complex.I * (beta : ℂ)))
      (by simpa using hb)
    rw [h, norm_zero] at hp
    have hm := margin_pos ha
    have hx : 0 < margin a * (1 + (((t : ℂ) + Complex.I * (beta : ℂ)).re) ^ 2) :=
      mul_pos hm (by positivity)
    linarith
  field_simp [hcp, hcm, hd]
  dsimp only [cp, cm]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

end Zeta23.WeilEF.ExponentialStripSampling
