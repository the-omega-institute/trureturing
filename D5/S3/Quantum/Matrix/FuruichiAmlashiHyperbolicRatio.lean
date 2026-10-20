/- GID: D5/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/FuruichiAmlashiHyperbolicRatio
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.RemovableSingularity, mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Continuity]
   utility: none
   digest: The Furuichi–Eghbali Amlashi hyperbolic ratio is not positive definite below one. -/

import D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! An analytic extension and its vanishing imaginary boundary value. -/

noncomputable section
open Complex Filter Set
open scoped Topology

namespace D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio

/-- The continuously extended ratio of the geometric-arithmetic bridge mean
to the logarithmic mean. -/
def phi (r t : ℝ) : ℝ :=
  if t = 0 then 1 else t * Real.cosh t ^ (1 - r) / Real.sinh t

/-- The hyperbolic-ratio conjecture with all real parameters below one. -/
def claim : Prop := ∀ r : ℝ, r < 1 →
  ¬ D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite
    (fun t => (phi r t : ℂ))

private def extension (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (a * Complex.log (Complex.cosh z)) / dslope Complex.sinh 0 z

private lemma sinh_coordinates (z : ℂ) :
    Complex.sinh z = (Real.sinh z.re * Real.cos z.im : ℝ) +
      (Real.cosh z.re * Real.sin z.im : ℝ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp only [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.ofReal_mul]
  ring

private lemma cosh_re (z : ℂ) :
    (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.mul_re, Complex.mul_im]

private lemma cosh_re_pos {z : ℂ} (hz : ‖z‖ < Real.pi / 2) :
    0 < (Complex.cosh z).re := by
  rw [cosh_re]
  exact mul_pos (Real.cosh_pos _) (Real.cos_pos_of_mem_Ioo
    (abs_lt.mp ((Complex.abs_im_le_norm z).trans_lt hz)))

private lemma sinh_ne_zero {z : ℂ} (hz : ‖z‖ < Real.pi / 2) (hz0 : z ≠ 0) :
    Complex.sinh z ≠ 0 := by
  intro hs
  have him := congrArg Complex.im hs
  rw [sinh_coordinates] at him
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.zero_im] at him
  have hsini : Real.sin z.im = 0 := (mul_eq_zero.mp him).resolve_left (Real.cosh_pos _).ne'
  have hzi : |z.im| < Real.pi / 2 := (Complex.abs_im_le_norm z).trans_lt hz
  have him0 : z.im = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [(abs_lt.mp hzi).1, Real.pi_pos])
    (by linarith [(abs_lt.mp hzi).2, Real.pi_pos])).mp hsini
  have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him0)
  rw [hzr, ← Complex.ofReal_sinh] at hs
  have hre0 : z.re = 0 := Real.sinh_eq_zero.mp (Complex.ofReal_eq_zero.mp hs)
  exact hz0 (Complex.ext hre0 him0)

private lemma dslope_sinh_ne_zero {z : ℂ} (hz : ‖z‖ < Real.pi / 2) :
    dslope Complex.sinh 0 z ≠ 0 := by
  by_cases hz0 : z = 0
  · subst z
    simp [dslope_same, Complex.deriv_sinh]
  · rw [dslope_of_ne _ hz0, slope_def_field]
    simpa using div_ne_zero (sinh_ne_zero hz hz0) hz0

private lemma extension_differentiable (a : ℝ) :
    DifferentiableOn ℂ (extension a) (Metric.ball 0 (Real.pi / 2)) := by
  have hd : DifferentiableOn ℂ (dslope Complex.sinh 0)
      (Metric.ball 0 (Real.pi / 2)) :=
    (Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 (by positivity))).mpr
      Complex.differentiable_sinh.differentiableOn
  intro z hz
  have hzn : ‖z‖ < Real.pi / 2 := by simpa [Metric.mem_ball] using hz
  apply DifferentiableWithinAt.div
  · apply DifferentiableAt.differentiableWithinAt
    exact Complex.differentiable_exp.differentiableAt.comp z
      (((Complex.differentiableAt_log
        (Or.inl (cosh_re_pos hzn))).comp z
          Complex.differentiable_cosh.differentiableAt).const_mul (a : ℂ))
  · exact hd z hz
  · exact dslope_sinh_ne_zero hzn

private lemma exp_log_real (a b : ℝ) (hb : 0 < b) :
    Complex.exp ((a : ℂ) * Complex.log (b : ℂ)) = (b ^ a : ℝ) := by
  rw [← Complex.ofReal_log hb.le, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
    Real.rpow_def_of_pos hb]
  congr 2
  ring

private lemma extension_real (r x : ℝ) : extension (1 - r) x = (phi r x : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp [extension, phi, dslope_same, Complex.deriv_sinh]
  · have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    rw [extension, ← Complex.ofReal_cosh, exp_log_real _ _ (Real.cosh_pos x),
      dslope_of_ne _ hxc, slope_def_field]
    simp only [Complex.sinh_zero, sub_zero, ← Complex.ofReal_sinh]
    rw [phi, if_neg hx]
    push_cast
    field_simp

private lemma extension_imaginary (a y : ℝ) (hy0 : 0 < y) (hy : y < Real.pi / 2) :
    extension a ((y : ℂ) * Complex.I) =
      (y * Real.cos y ^ a / Real.sin y : ℝ) := by
  have hcos : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hy⟩
  have hyc : (y : ℂ) * Complex.I ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr hy0.ne') Complex.I_ne_zero
  rw [extension, Complex.cosh_mul_I, ← Complex.ofReal_cos, exp_log_real _ _ hcos,
    dslope_of_ne _ hyc, slope_def_field, Complex.sinh_mul_I]
  simp only [Complex.sinh_zero, sub_zero, ← Complex.ofReal_sin]
  push_cast
  field_simp

/-- Every real parameter below one violates positive definiteness. -/
theorem result : claim := by
  intro r hr hf
  have ha : 0 < 1 - r := sub_pos.mpr hr
  let g : ℝ → ℝ := fun y => y * Real.cos y ^ (1 - r) / Real.sin y
  have hc : ContinuousAt g (Real.pi / 2) := by
    apply ContinuousAt.div
    · exact continuousAt_id.mul (Real.continuous_cos.continuousAt.rpow_const (Or.inr ha.le))
    · exact Real.continuous_sin.continuousAt
    · simp
  have hg0 : g (Real.pi / 2) = 0 := by simp [g, Real.zero_rpow ha.ne']
  have hlim : Tendsto g (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa only [hg0] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hge : ∀ᶠ y in 𝓝[<] (Real.pi / 2), 1 ≤ g y := by
    filter_upwards [Ioo_mem_nhdsLT (by positivity : (0 : ℝ) < Real.pi / 2)] with y hy
    have H := D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis.le_re_of_positiveDefinite
      hf (fun _ => Complex.ofReal_im _) (extension_differentiable (1 - r))
      (fun x _ => extension_real r x) hy.1.le hy.2
    rw [extension_imaginary _ _ hy.1 hy.2] at H
    simpa only [phi, ite_true, if_pos rfl, Complex.ofReal_re, g] using H
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim hge
  norm_num at hbad

end D5.S3.Quantum.Matrix.FuruichiAmlashiHyperbolicRatio
