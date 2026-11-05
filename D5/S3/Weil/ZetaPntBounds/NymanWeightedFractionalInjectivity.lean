/- GID: D5/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaPntBounds/NymanWeightedFractionalInjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Injectivity of the actual fractional transform on its weighted domain. -/

/-
The transform and all convergence hypotheses below concern the literal
positive-half-line Bochner integral.

The whole-positive Mellin calculation reuses the actual unit-interval result in
NymanFractionalMellin and its shared fractionalMellin_tail_integrand_eq_cpow
helper. The paired source extraction moves that existing pointwise proof out
of private mellin_tail_real; both old and new consumers call the same helper.
This source refactor is not a new mathematical result or proto-Muentz proof.
That module's source port is jrgochan/prime, commit
ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2 (Jason Robert Gochanour, Apache-2.0).

Domain: -1/2 < r < 1/2; gamma is any real number. Only the single
absolute weight norm(w(u))*u^(r-1) is needed. Boundedness of the logarithmic
kernel pays every actual H integral. No zeta zero, multiplier or injection
principle is assumed.
-/

import D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Compactness.Lindelof

/-! Injectivity of the literal fractional reciprocal transform on its weighted domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaPntBounds.NymanWeightedFractionalInjectivity

open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform Convolution
open D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin

/-- The literal positive-half-line fractional reciprocal coefficient. -/
private def fractionalBase (x : ℝ) : ℂ := (Int.fract (1 / x) : ℝ)

/-- The literal complex integrand; no quotient or abstract operator is substituted. -/
def actualIntegrand (w : ℝ → ℂ) (gamma y u : ℝ) : ℂ :=
  w u * (u : ℂ) ^ ((-1 / 2 : ℂ) + (gamma : ℂ) * I) *
    ((Int.fract (1 / (u * y)) : ℝ) : ℂ)

def actualTransform (w : ℝ → ℂ) (gamma y : ℝ) : ℂ :=
  ∫ u in Ioi 0, actualIntegrand w gamma y u

/-- Absolute weighted integrability, stated with a real nonnegative integrand. -/
def WeightedIntegrable (w : ℝ → ℂ) (r : ℝ) : Prop :=
  IntegrableOn (fun u : ℝ => ‖w u‖ * u ^ (r - 1)) (Ioi 0)

private def logProfile (w : ℝ → ℂ) (r gamma v : ℝ) : ℂ :=
  w (Real.exp v) * Complex.exp (((r : ℂ) + (gamma : ℂ) * I) * (v : ℂ))

private def logKernel (kappa z : ℝ) : ℂ :=
  (Real.exp (-kappa * z) : ℂ) * ((Int.fract (Real.exp z) : ℝ) : ℂ)

private def stripFrequency (kappa xi : ℝ) : ℂ :=
  (kappa : ℂ) + ((2 * Real.pi * xi : ℝ) : ℂ) * I

private lemma cpow_exp_real (v : ℝ) (s : ℂ) :
    ((Real.exp v : ℝ) : ℂ) ^ s = Complex.exp (s * (v : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]
  congr 1
  ring

private lemma fractional_integrable (s : ℂ) (hs : 0 < s.re) (hs1 : s.re < 1) :
    IntegrableOn (fun x : ℝ => fractionalBase x * (x : ℂ) ^ (s - 1)) (Ioi 0) := by
  have hnear : IntegrableOn
      (fun x : ℝ => fractionalBase x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact fractionalMellin_integrableOn 1 s hs
  have hfar : IntegrableOn
      (fun x : ℝ => fractionalBase x * (x : ℂ) ^ (s - 1)) (Ioi 1) := by
    refine (integrableOn_Ioi_cpow_of_lt (a := s - 2) ?_ zero_lt_one).congr_fun
      (fun x hx => (fractionalMellin_tail_integrand_eq_cpow s hx).symm) measurableSet_Ioi
    simpa [Complex.sub_re] using (show s.re - 2 < -1 by linarith)
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  exact ⟨hnear, hfar⟩

/-- The complete Mellin multiplier, paying the reciprocal tail rather than assuming it. -/
private lemma mellin_fractionalBase (s : ℂ) (hs : 0 < s.re) (hs1 : s.re < 1) :
    mellin fractionalBase s = -riemannZeta s / s := by
  have hsn : s ≠ 1 := by
    intro h
    simp [h] at hs1
  have hint := fractional_integrable s hs hs1
  have hnear : IntegrableOn
      (fun x : ℝ => fractionalBase x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) :=
    hint.mono_set Ioc_subset_Ioi_self
  have hfar : IntegrableOn
      (fun x : ℝ => fractionalBase x * (x : ℂ) ^ (s - 1)) (Ioi 1) :=
    hint.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  unfold mellin
  simp only [smul_eq_mul]
  calc
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * fractionalBase x)
        = ∫ x in Ioi (0 : ℝ), fractionalBase x * (x : ℂ) ^ (s - 1) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x _
            exact mul_comm _ _
    _ = (∫ x in Ioc (0 : ℝ) 1, fractionalBase x * (x : ℂ) ^ (s - 1)) +
        ∫ x in Ioi (1 : ℝ), fractionalBase x * (x : ℂ) ^ (s - 1) := by
          rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
          exact setIntegral_union hdisj measurableSet_Ioi hnear hfar
    _ = (1 / (s - 1) - riemannZeta s / s) +
        (-(1 : ℂ) ^ (s - 2 + 1) / (s - 2 + 1)) := by
          rw [integral_Ioc_eq_integral_Ioo]
          rw [show (∫ x in Ioo (0 : ℝ) 1,
              fractionalBase x * (x : ℂ) ^ (s - 1)) =
              1 / (s - 1) - riemannZeta s / s from
            bd_mellin_base_case_proved s hs hsn]
          congr 1
          calc
            (∫ x in Ioi (1 : ℝ), fractionalBase x * (x : ℂ) ^ (s - 1)) =
                ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 2) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x hx
              exact fractionalMellin_tail_integrand_eq_cpow s hx
            _ = _ := integral_Ioi_cpow_of_lt (a := s - 2)
              (by simpa [Complex.sub_re] using (show s.re - 2 < -1 by linarith)) zero_lt_one
    _ = -riemannZeta s / s := by
          rw [show (s - 2 + 1 : ℂ) = s - 1 from by ring, one_cpow]
          ring

private lemma measurable_logKernel (kappa : ℝ) : Measurable (logKernel kappa) := by
  exact (Complex.continuous_ofReal.measurable.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).mul
    (Complex.continuous_ofReal.measurable.comp Real.continuous_exp.measurable.fract)

private lemma norm_logKernel (kappa z : ℝ) :
    ‖logKernel kappa z‖ = Real.exp (-kappa * z) * Int.fract (Real.exp z) := by
  simp only [logKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (Real.exp_pos _), abs_of_nonneg (Int.fract_nonneg (Real.exp z))]

private lemma fract_exp_le_exp (z : ℝ) : Int.fract (Real.exp z) ≤ Real.exp z := by
  rw [Int.fract]
  apply sub_le_self
  exact_mod_cast Int.floor_nonneg.mpr (Real.exp_pos z).le

private lemma norm_logKernel_le_right (kappa z : ℝ) :
    ‖logKernel kappa z‖ ≤ Real.exp (-kappa * z) := by
  rw [norm_logKernel]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Int.fract_lt_one _).le

private lemma norm_logKernel_le_left (kappa z : ℝ) :
    ‖logKernel kappa z‖ ≤ Real.exp ((1 - kappa) * z) := by
  calc
    ‖logKernel kappa z‖ ≤ Real.exp (-kappa * z) * Real.exp z := by
      rw [norm_logKernel]
      exact mul_le_mul_of_nonneg_left (fract_exp_le_exp z) (Real.exp_pos _).le
    _ = Real.exp ((1 - kappa) * z) := by
      rw [← Real.exp_add]
      congr 1
      ring

private lemma norm_logKernel_le_one (kappa : ℝ) (hk : 0 < kappa)
    (hk1 : kappa < 1) (z : ℝ) : ‖logKernel kappa z‖ ≤ 1 := by
  rcases le_or_gt 0 z with hz | hz
  · exact (norm_logKernel_le_right kappa z).trans
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) hz))
  · exact (norm_logKernel_le_left kappa z).trans
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith) hz.le))

private lemma integrable_logKernel (kappa : ℝ) (hk : 0 < kappa) (hk1 : kappa < 1) :
    Integrable (logKernel kappa) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · refine (integrableOn_exp_mul_Iic (a := 1 - kappa) (by linarith) 0).mono'
      (measurable_logKernel kappa).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with z _
    exact norm_logKernel_le_left kappa z
  · refine (integrableOn_exp_mul_Ioi (a := -kappa) (by linarith) 0).mono'
      (measurable_logKernel kappa).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z _
    exact norm_logKernel_le_right kappa z

private lemma fourier_logKernel (kappa : ℝ) (hk : 0 < kappa) (hk1 : kappa < 1)
    (xi : ℝ) : 𝓕 (logKernel kappa) xi =
      -riemannZeta (stripFrequency kappa xi) / stripFrequency kappa xi := by
  have hsre : (stripFrequency kappa xi).re = kappa := by simp [stripFrequency]
  have hsim : (stripFrequency kappa xi).im / (2 * Real.pi) = xi := by
    simp only [stripFrequency, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero,
      zero_add, add_zero]
    field_simp [Real.pi_ne_zero]
  have hshape : (fun z : ℝ => Real.exp (-(stripFrequency kappa xi).re * z) •
      fractionalBase (Real.exp (-z))) = logKernel kappa := by
    funext z
    rw [hsre]
    change (Real.exp (-kappa * z) : ℂ) *
      ((Int.fract (1 / Real.exp (-z)) : ℝ) : ℂ) = _
    simp only [Real.exp_neg, one_div, inv_inv, logKernel]
  have hm := mellin_eq_fourier fractionalBase (s := stripFrequency kappa xi)
  rw [hshape, hsim] at hm
  rw [← hm, mellin_fractionalBase _ (by simpa [hsre] using hk)
    (by simpa [hsre] using hk1)]

private lemma stripFrequency_injective (kappa : ℝ) : Function.Injective (stripFrequency kappa) := by
  intro x y h
  have hi := congrArg Complex.im h
  simp only [stripFrequency, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero,
    zero_add, add_zero] at hi
  exact mul_left_cancel₀ (show (2 * Real.pi : ℝ) ≠ 0 by positivity) hi

private lemma dense_zeta_nonzero_vertical (kappa : ℝ) :
    Dense {xi : ℝ | riemannZeta (stripFrequency kappa xi) ≠ 0} := by
  have hz : (riemannZetaZeros : Set ℂ).Countable :=
    isClosed_riemannZetaZeros.isLindelof.countable_of_isDiscrete isDiscrete_riemannZetaZeros
  have hp := hz.preimage (stripFrequency_injective kappa)
  have heq : (stripFrequency kappa ⁻¹' riemannZetaZeros)ᶜ =
      {xi : ℝ | riemannZeta (stripFrequency kappa xi) ≠ 0} := by
    ext xi
    simp [riemannZetaZeros]
  rw [← heq]
  exact hp.dense_compl ℝ

private lemma continuous_logProfile (w : ℝ → ℂ) (r gamma : ℝ)
    (hw : ContinuousOn w (Ioi 0)) : Continuous (logProfile w r gamma) := by
  have hwexp : Continuous (fun v : ℝ => w (Real.exp v)) :=
    hw.comp_continuous Real.continuous_exp (fun v => Real.exp_pos v)
  exact hwexp.mul (by fun_prop)

private lemma norm_logProfile (w : ℝ → ℂ) (r gamma v : ℝ) :
    ‖logProfile w r gamma v‖ = ‖w (Real.exp v)‖ * Real.exp (r * v) := by
  simp [logProfile, Complex.norm_exp, Complex.mul_re, Complex.add_re]

private lemma integrable_logProfile (w : ℝ → ℂ) (r gamma : ℝ)
    (hw : ContinuousOn w (Ioi 0)) (hwr : WeightedIntegrable w r) :
    Integrable (logProfile w r gamma) := by
  have hlog : Integrable (fun v : ℝ =>
      Real.exp v • (‖w (Real.exp v)‖ * Real.exp v ^ (r - 1))) :=
    (integrable_comp_exp (fun u : ℝ => ‖w u‖ * u ^ (r - 1))).mpr hwr
  apply (integrable_norm_iff (continuous_logProfile w r gamma hw).aestronglyMeasurable).mp
  refine hlog.congr (ae_of_all _ (fun v => ?_))
  change Real.exp v * (‖w (Real.exp v)‖ * Real.exp v ^ (r - 1)) =
    ‖logProfile w r gamma v‖
  rw [norm_logProfile, ← Real.exp_mul]
  calc
    _ = ‖w (Real.exp v)‖ * (Real.exp v * Real.exp (v * (r - 1))) := by ring
    _ = ‖w (Real.exp v)‖ * Real.exp (r * v) := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- The genuine Jacobian identity, with the actual fractional part retained. -/
private lemma exp_jacobian_actual (w : ℝ → ℂ) (r gamma z v : ℝ) :
    Real.exp v • actualIntegrand w gamma (Real.exp (-z)) (Real.exp v) =
      (Real.exp ((1 / 2 - r) * z) : ℂ) *
        (logProfile w r gamma v * logKernel (1 / 2 - r) (z - v)) := by
  have hfrac : 1 / (Real.exp v * Real.exp (-z)) = Real.exp (z - v) := by
    rw [← Real.exp_add, one_div, ← Real.exp_neg]
    congr 1
    ring
  have he : Complex.exp (v : ℂ) *
        Complex.exp (((-1 / 2 : ℂ) + (gamma : ℂ) * I) * (v : ℂ)) =
      Complex.exp (((1 / 2 - r) * z : ℝ) : ℂ) *
        Complex.exp (((r : ℂ) + (gamma : ℂ) * I) * (v : ℂ)) *
        Complex.exp ((-(1 / 2 - r) * (z - v) : ℝ) : ℂ) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  change (Real.exp v : ℂ) *
    (w (Real.exp v) * (Real.exp v : ℂ) ^
      ((-1 / 2 : ℂ) + (gamma : ℂ) * I) *
        ((Int.fract (1 / (Real.exp v * Real.exp (-z))) : ℝ) : ℂ)) = _
  rw [hfrac, cpow_exp_real]
  dsimp [logProfile, logKernel]
  simp only [Complex.ofReal_exp]
  calc
    _ = w (Real.exp v) * (Complex.exp (v : ℂ) *
        Complex.exp (((-1 / 2 : ℂ) + (gamma : ℂ) * I) * (v : ℂ))) *
          ((Int.fract (Real.exp (z - v)) : ℝ) : ℂ) := by ring
    _ = _ := by rw [he]; ring

private lemma exp_jacobian_actual_scaled (w : ℝ → ℂ) (r gamma z v : ℝ) :
    (Real.exp (-(1 / 2 - r) * z) : ℂ) *
      (Real.exp v • actualIntegrand w gamma (Real.exp (-z)) (Real.exp v)) =
        logProfile w r gamma v * logKernel (1 / 2 - r) (z - v) := by
  rw [exp_jacobian_actual w r gamma z v, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add]
  simp only [neg_mul, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

private lemma actualTransform_integrable (w : ℝ → ℂ) (r gamma : ℝ)
    (hr : -1 / 2 < r) (hr1 : r < 1 / 2) (hw : ContinuousOn w (Ioi 0))
    (hwr : WeightedIntegrable w r) (y : ℝ) (hy : 0 < y) :
    IntegrableOn (actualIntegrand w gamma y) (Ioi 0) := by
  let z : ℝ := -Real.log y
  have hyexp : Real.exp (-z) = y := by simp [z, Real.exp_log hy]
  have hf := integrable_logProfile w r gamma hw hwr
  have hk : 0 < 1 / 2 - r := by linarith
  have hk1 : 1 / 2 - r < 1 := by linarith
  have hkm : AEStronglyMeasurable (fun v : ℝ => logKernel (1 / 2 - r) (z - v)) :=
    ((measurable_logKernel _).comp
      (continuous_const.sub continuous_id).measurable).aestronglyMeasurable
  have hprod : Integrable (fun v : ℝ =>
      logProfile w r gamma v * logKernel (1 / 2 - r) (z - v)) :=
    hf.mul_bdd hkm (ae_of_all _ (fun v => norm_logKernel_le_one _ hk hk1 (z - v)))
  apply (integrable_comp_exp (actualIntegrand w gamma y)).mp
  refine (hprod.const_mul (Real.exp ((1 / 2 - r) * z) : ℂ)).congr
    (ae_of_all _ (fun v => ?_))
  change (Real.exp ((1 / 2 - r) * z) : ℂ) *
    (logProfile w r gamma v * logKernel (1 / 2 - r) (z - v)) =
      Real.exp v • actualIntegrand w gamma y (Real.exp v)
  rw [← exp_jacobian_actual w r gamma z v, hyexp]

private lemma actual_convolution (w : ℝ → ℂ) (r gamma : ℝ)
    (hr : -1 / 2 < r) (hr1 : r < 1 / 2) (hw : ContinuousOn w (Ioi 0))
    (hwr : WeightedIntegrable w r) (z : ℝ) :
    (Real.exp (-(1 / 2 - r) * z) : ℂ) * actualTransform w gamma (Real.exp (-z)) =
      (logProfile w r gamma ⋆[ContinuousLinearMap.mul ℂ ℂ] logKernel (1 / 2 - r)) z := by
  let c : ℂ := Real.exp (-(1 / 2 - r) * z)
  let g : ℝ → ℂ := actualIntegrand w gamma (Real.exp (-z))
  have hg : IntegrableOn g (Ioi 0) :=
    actualTransform_integrable w r gamma hr hr1 hw hwr _ (Real.exp_pos _)
  change c * (∫ u in Ioi 0, g u) = ∫ v : ℝ,
    logProfile w r gamma v * logKernel (1 / 2 - r) (z - v)
  calc
    _ = ∫ u in Ioi 0, c * g u := by
      simpa only [smul_eq_mul] using (hg.integral_smul c).symm
    _ = ∫ v : ℝ, Real.exp v • (c * g (Real.exp v)) :=
      (integral_comp_exp (fun u : ℝ => c * g u)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with v
      change (Real.exp v : ℂ) * (c * g (Real.exp v)) = _
      rw [mul_left_comm]
      exact exp_jacobian_actual_scaled w r gamma z v

/-- The literal fractional-kernel transform is injective on its weighted continuous domain.
The logarithmic kernel is in L1 and bounded, so all the displayed integrals are genuine
absolutely convergent Bochner integrals. The parameter gamma is arbitrary. -/
theorem weighted_fractional_transform_injective (w : ℝ → ℂ) (r gamma : ℝ)
    (hr : -1 / 2 < r) (hr1 : r < 1 / 2) (hw : ContinuousOn w (Ioi 0))
    (hwr : WeightedIntegrable w r)
    (hzero : ∀ y : ℝ, 0 < y → actualTransform w gamma y = 0) :
    EqOn w 0 (Ioi 0) := by
  let f := logProfile w r gamma
  let kappa : ℝ := 1 / 2 - r
  have hk : 0 < kappa := by dsimp [kappa]; linarith
  have hk1 : kappa < 1 := by dsimp [kappa]; linarith
  have hf : Integrable f := integrable_logProfile w r gamma hw hwr
  have hfc : Continuous f := continuous_logProfile w r gamma hw
  have hkc : Integrable (logKernel kappa) := integrable_logKernel kappa hk hk1
  have hconv : (f ⋆[ContinuousLinearMap.mul ℂ ℂ] logKernel kappa) = 0 := by
    funext z
    rw [← actual_convolution w r gamma hr hr1 hw hwr z,
      hzero _ (Real.exp_pos _), mul_zero]
    rfl
  have hprod : ∀ xi : ℝ, 𝓕 f xi * 𝓕 (logKernel kappa) xi = 0 := by
    intro xi
    rw [← Real.fourier_mul_convolution_eq hf hkc xi, hconv]
    simp [Real.fourier_eq]
  have hFcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have hFzero : 𝓕 f = 0 := by
    have hclosed : IsClosed {xi : ℝ | 𝓕 f xi = 0} :=
      isClosed_eq hFcont continuous_const
    have hsubset : {xi : ℝ | riemannZeta (stripFrequency kappa xi) ≠ 0} ⊆
        {xi : ℝ | 𝓕 f xi = 0} := by
      intro xi hxi
      have hs0 : stripFrequency kappa xi ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp [stripFrequency] at hre
        linarith
      have hmult : 𝓕 (logKernel kappa) xi ≠ 0 := by
        rw [fourier_logKernel kappa hk hk1 xi]
        exact div_ne_zero (neg_ne_zero.mpr hxi) hs0
      exact (mul_eq_zero.mp (hprod xi)).resolve_right hmult
    have hcl := hclosed.closure_subset_iff.mpr hsubset
    funext xi
    exact hcl (dense_zeta_nonzero_vertical kappa xi)
  have hFint : Integrable (𝓕 f) := by
    rw [hFzero]
    exact integrable_zero ℝ ℂ volume
  have hfzero : f = 0 := by
    have hinv := hfc.fourierInv_fourier_eq hf hFint
    rw [hFzero] at hinv
    have hi0 : 𝓕⁻ (0 : ℝ → ℂ) = 0 := by
      funext x
      simp [Real.fourierInv_eq]
    simpa only [hi0] using hinv.symm
  intro u hu
  have h := congrFun hfzero (Real.log u)
  change logProfile w r gamma (Real.log u) = 0 at h
  rw [logProfile, Real.exp_log hu] at h
  exact (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _)


end D5.S3.Weil.ZetaPntBounds.NymanWeightedFractionalInjectivity
