/- GID: D5/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/BosonicRenyiStieltjes/PoissonWeight
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive-axis Stieltjes transform of the power Poisson density. -/

import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import D5.S3.TotalVariation.IndependentConvolutionL1Minimum

/-! The positive-axis transform used by the logarithmic Renyi representation. -/

namespace D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight

open Real Set MeasureTheory
open scoped Topology ComplexConjugate

noncomputable section

/-- Positivity throughout the nonintegral Renyi order range. -/
theorem power_poisson_denominator_pos {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) : 0 < 1 - 2 * r * Real.cos (Real.pi * α) + r ^ 2 := by
  rcases lt_or_gt_of_ne ha1 with ha | ha
  · exact D5.S3.TotalVariation.IndependentConvolutionL1Minimum.poisson_denominator_pos_of_sin_pos
      (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ha0)
        (by nlinarith [Real.pi_pos]))
  · have hs : 0 < Real.sin (-(Real.pi * α)) := by
      rw [Real.sin_neg]
      have h := Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [Real.pi_pos] : 0 < Real.pi * α - Real.pi)
        (by nlinarith [Real.pi_pos] : Real.pi * α - Real.pi < Real.pi)
      rwa [Real.sin_sub_pi] at h
    simpa only [Real.cos_neg] using
      (D5.S3.TotalVariation.IndependentConvolutionL1Minimum.poisson_denominator_pos_of_sin_pos
        (r := r) hs)

/-- Positivity of the signed trigonometric factor on the required order range. -/
theorem sine_factor_pos {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    0 < -Real.sin (Real.pi * α) / (α - 1) := by
  rcases lt_or_gt_of_ne ha1 with ha | ha
  · have hs : 0 < Real.sin (Real.pi * α) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ha0)
        (by nlinarith [Real.pi_pos])
    exact div_pos_of_neg_of_neg (neg_neg_of_pos hs) (sub_neg.mpr ha)
  · have hs : 0 < Real.sin (Real.pi * α - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    rw [Real.sin_sub_pi] at hs
    exact div_pos hs (sub_pos.mpr ha)

/-- The Poisson angle is nondegenerate on the required order range. -/
theorem cosine_lt_one {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    Real.cos (Real.pi * α) < 1 := by
  have hs := sine_factor_pos ha0 ha2 ha1
  have hsin : Real.sin (Real.pi * α) ≠ 0 := by
    intro hz
    rw [hz, neg_zero, zero_div] at hs
    exact lt_irrefl 0 hs
  refine lt_of_le_of_ne (Real.cos_le_one _) ?_
  intro he
  exact hsin (Real.sin_eq_zero_iff_cos_eq.mpr (Or.inl he))

/-- The power Poisson density after the substitution `p = q ^ α`. -/
def density (α q : ℝ) : ℝ :=
  α * q ^ (α - 1) * (-Real.sin (Real.pi * α)) /
    (Real.pi * (α - 1) * (1 - 2 * q ^ α * Real.cos (Real.pi * α) + (q ^ α) ^ 2))

/-- Reciprocal reflection preserves the density with its change-of-variables factor. -/
theorem density_reflection {α q : ℝ} (hq : 0 < q)
    (ha1 : α ≠ 1) (hc : Real.cos (Real.pi * α) < 1) :
    density α q⁻¹ / q ^ 2 = density α q := by
  have hp := Real.rpow_pos_of_pos hq α
  have hD : 0 < 1 - 2 * q ^ α * Real.cos (Real.pi * α) + (q ^ α) ^ 2 := by
    nlinarith [mul_pos hp (sub_pos.mpr hc), sq_nonneg (q ^ α - 1)]
  dsimp only [density]
  rw [Real.inv_rpow hq.le, Real.inv_rpow hq.le, Real.rpow_sub_one hq.ne']
  field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr ha1 |
    nlinarith [hD])
  ring

/-- Reciprocal reflection of the density with the resolvent Jacobian. -/
theorem density_resolvent_reflection {α r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (ha1 : α ≠ 1) (hc : Real.cos (Real.pi * α) < 1) :
    |-(q ^ 2)⁻¹| • (density α q⁻¹ / (r + q⁻¹)) =
      density α q * q / (1 + r * q) := by
  rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg q)), smul_eq_mul]
  calc
    _ = (density α q⁻¹ / q ^ 2) / (r + q⁻¹) := by ring
    _ = density α q / (r + q⁻¹) := by rw [density_reflection hq ha1 hc]
    _ = _ := by
      field_simp (disch := positivity)
      ring

private lemma density_integrable_unit {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) : IntegrableOn (density α) (Ioo 0 1) := by
  let f := fun q : ℝ => α * (-Real.sin (Real.pi * α)) /
    (Real.pi * (α - 1) * (1 - 2 * q ^ α * Real.cos (Real.pi * α) + (q ^ α) ^ 2))
  have hc : ContinuousOn f (Icc 0 1) := by
    intro q hq
    have hD :=
      power_poisson_denominator_pos
        (r := q ^ α) ha0 ha2 ha1
    have hpow : ContinuousAt (fun y : ℝ => y ^ α) q :=
      (Real.continuous_rpow_const ha0.le).continuousAt
    have hden : ContinuousAt (fun y : ℝ =>
        1 - 2 * y ^ α * Real.cos (Real.pi * α) + (y ^ α) ^ 2) q :=
      (continuousAt_const.sub ((hpow.const_mul 2).mul_const
        (Real.cos (Real.pi * α)))).add (hpow.pow 2)
    exact (continuousAt_const.div (hden.const_mul (Real.pi * (α - 1)))
      (mul_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr ha1)) hD.ne')).continuousWithinAt
  have hi : IntegrableOn (fun q : ℝ => q ^ (α - 1)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  apply (hi.mul_continuousOn_of_subset hc measurableSet_Ioo
    isCompact_Icc Ioo_subset_Icc_self).congr_fun _ measurableSet_Ioo
  intro q _
  dsimp only [density, f]
  ring

private lemma density_resolvent_integrable {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) :
    IntegrableOn (fun q => density α q / (r + q)) (Ioi 0) := by
  let g := fun q => density α q / (r + q)
  have hi := density_integrable_unit ha0 ha2 ha1
  have hhead : IntegrableOn g (Ioo 0 1) := by
    have hc : ContinuousOn (fun q : ℝ => 1 / (r + q)) (Icc 0 1) := by
      intro q hq
      exact (continuousAt_const.div (continuousAt_const.add continuousAt_id)
        (add_pos_of_pos_of_nonneg hr0 hq.1).ne').continuousWithinAt
    simpa only [g, div_eq_mul_inv, one_mul] using
      hi.mul_continuousOn_of_subset hc measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have hreflect : IntegrableOn (fun q => density α q * q / (1 + r * q)) (Ioo 0 1) := by
    have hc : ContinuousOn (fun q : ℝ => q / (1 + r * q)) (Icc 0 1) := by
      intro q hq
      exact (continuousAt_id.div
        (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
        (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hr0.le hq.1)).ne').continuousWithinAt
    simpa only [mul_div_assoc] using
      hi.mul_continuousOn_of_subset hc measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have him : (fun q : ℝ => q⁻¹) '' Ioo (0 : ℝ) 1 = Ioi 1 := by
    simpa only [image_inv_eq_inv, inv_one] using
      (inv_Ioo_0_left (zero_lt_one : (0 : ℝ) < 1))
  have hinj : InjOn (fun q : ℝ => q⁻¹) (Ioo 0 1) :=
    fun _ _ _ _ h => inv_injective h
  have hd : ∀ q ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun q : ℝ => q⁻¹) (-(q ^ 2)⁻¹) (Ioo 0 1) q :=
    fun q hq => (hasDerivAt_inv hq.1.ne').hasDerivWithinAt
  have htail : IntegrableOn g (Ioi 1) := by
    rw [← him]
    apply (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioo hd hinj g).mpr
    apply hreflect.congr_fun _ measurableSet_Ioo
    intro q hq
    exact (density_resolvent_reflection hr0 hq.1 ha1
      (cosine_lt_one ha0 ha2 ha1)).symm
  have hsets : Ioo (0 : ℝ) 1 ∪ Ici 1 = Ioi 0 :=
    Ioo_union_Ici_eq_Ioi zero_lt_one
  have hu := hhead.union ((integrableOn_Ici_iff_integrableOn_Ioi).mpr htail)
  simpa only [hsets] using hu

private def complexTransform (α : ℝ) (z : ℂ) : ℂ :=
  (1 / (1 - z) - (α : ℂ) * z ^ (α : ℂ) / (z * (1 - z ^ (α : ℂ)))) /
    ((α - 1 : ℝ) : ℂ)

private lemma exp_eq_one_strip {w : ℂ} (hlo : -(2 * Real.pi) < w.im)
    (hhi : w.im < 2 * Real.pi) (he : Complex.exp w = 1) : w = 0 := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  have hi := congrArg Complex.im hn
  norm_num [Complex.mul_im, Complex.mul_re] at hi
  have hnlo : (-1 : ℝ) < n := by nlinarith [Real.pi_pos]
  have hnhi : (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have hn0 : n = 0 := by
    have hlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
    have hhi' : n < (1 : ℤ) := by exact_mod_cast hnhi
    omega
  simpa [hn0] using hn


private lemma power_eq_one {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) {z : ℂ}
    (hz0 : z ≠ 0) (hz : z ^ (α : ℂ) = 1) : z = 1 := by
  rw [Complex.cpow_def_of_ne_zero hz0] at hz
  have him : (Complex.log z * (α : ℂ)).im = Complex.arg z * α := by
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      Complex.log_im, mul_zero, zero_add]
  have hzero : Complex.log z * (α : ℂ) = 0 := exp_eq_one_strip
    (by rw [him]; nlinarith [mul_lt_mul_of_pos_right (Complex.neg_pi_lt_arg z) ha0,
      Real.pi_pos])
    (by rw [him]; nlinarith [mul_le_mul_of_nonneg_right (Complex.arg_le_pi z) ha0.le,
      Real.pi_pos]) hz
  have hlog : Complex.log z = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (Complex.ofReal_ne_zero.mpr ha0.ne')
  simpa [hlog] using (Complex.exp_log hz0).symm

private def powerSlope (α : ℝ) : ℂ → ℂ := dslope (fun z => z ^ (α : ℂ)) 1

private lemma powerSlope_one (α : ℝ) : powerSlope α 1 = (α : ℂ) := by
  simp only [powerSlope, dslope_same, Complex.deriv_cpow_const Complex.one_mem_slitPlane,
    Complex.one_cpow, mul_one]

private lemma powerSlope_ne_zero {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) : powerSlope α z ≠ 0 := by
  by_cases hz1 : z = 1
  · subst z
    rw [powerSlope_one]
    exact Complex.ofReal_ne_zero.mpr ha0.ne'
  · rw [powerSlope, dslope_of_ne _ hz1]
    simp only [slope, smul_eq_mul, Complex.one_cpow]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hz1))
      (sub_ne_zero.mpr (fun h => hz1 (power_eq_one ha0 ha2
        (Complex.slitPlane_ne_zero hz) h)))

private lemma powerSlope_differentiable (α : ℝ) :
    DifferentiableOn ℂ (powerSlope α) Complex.slitPlane := by
  apply (Complex.differentiableOn_dslope
    (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)).mpr
  exact differentiableOn_id.cpow_const (fun _ hz => hz)

private def regularTransform (α : ℝ) (z : ℂ) : ℂ :=
  dslope (fun w => (α : ℂ) * w ^ (α : ℂ) / (w * powerSlope α w)) 1 z /
    ((α - 1 : ℝ) : ℂ)

private lemma regularTransform_differentiable {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) :
    DifferentiableOn ℂ (regularTransform α) Complex.slitPlane := by
  apply DifferentiableOn.div_const
  apply (Complex.differentiableOn_dslope
    (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)).mpr
  exact ((differentiableOn_id.cpow_const (fun _ hz => hz)).const_mul _).div
    (differentiableOn_id.mul (powerSlope_differentiable α))
    (fun z hz => mul_ne_zero (Complex.slitPlane_ne_zero hz)
      (powerSlope_ne_zero ha0 ha2 hz))

private lemma regularTransform_eq {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    regularTransform α z = complexTransform α z := by
  have hpow : z ^ (α : ℂ) ≠ 1 := fun h => hz1 (power_eq_one ha0 ha2 hz0 h)
  dsimp only [regularTransform]
  rw [dslope_of_ne _ hz1, slope_def_field]
  simp only [Complex.one_cpow, powerSlope_one, one_mul]
  rw [powerSlope, dslope_of_ne _ hz1, slope_def_field, Complex.one_cpow]
  rw [complexTransform.eq_1]
  congr 1
  field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr hz1 |
    exact sub_ne_zero.mpr hpow | exact Complex.ofReal_ne_zero.mpr ha0.ne')
  ring


private def logTransform (α : ℝ) (w : ℂ) : ℂ :=
  if w = 0 then regularTransform α 1 else
    (1 / (1 - Complex.exp w) - (α : ℂ) * Complex.exp ((α : ℂ) * w) /
      (Complex.exp w * (1 - Complex.exp ((α : ℂ) * w)))) / ((α - 1 : ℝ) : ℂ)

private lemma logTransform_eq_regular {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    {w : ℂ} (hlo : -Real.pi < w.im) (hhi : w.im < Real.pi) :
    logTransform α w = regularTransform α (Complex.exp w) := by
  by_cases hw : w = 0
  · simp [logTransform, hw]
  have he1 : Complex.exp w ≠ 1 := fun h => hw (exp_eq_one_strip
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) h)
  rw [logTransform, ite_eq_right hw,
    regularTransform_eq ha0 ha2 (Complex.exp_ne_zero _) he1]
  simp only [complexTransform, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp hlo hhi.le, mul_comm w (α : ℂ)]

private lemma logTransform_differentiable {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    {w : ℂ} (hw : -Real.pi ≤ w.im ∧ w.im ≤ Real.pi) :
    DifferentiableAt ℂ (logTransform α) w := by
  by_cases hw0 : w = 0
  · subst w
    have hd := (regularTransform_differentiable ha0 ha2).differentiableAt
      (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
    have he : Complex.exp 0 = (1 : ℂ) := Complex.exp_zero
    have hcomp : DifferentiableAt ℂ
        (fun z => regularTransform α (Complex.exp z)) 0 :=
      (he ▸ hd).comp 0 Complex.differentiableAt_exp
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [show ∀ᶠ z : ℂ in 𝓝 0, -Real.pi < z.im ∧ z.im < Real.pi from
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)).mem_nhds
        (by simpa using And.intro (neg_neg_of_pos Real.pi_pos) Real.pi_pos)] with z hz
    exact logTransform_eq_regular ha0 ha2 hz.1 hz.2
  have he1 : 1 - Complex.exp w ≠ 0 := by
    intro h
    exact hw0 (exp_eq_one_strip (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) (sub_eq_zero.mp h).symm)
  have hea : 1 - Complex.exp ((α : ℂ) * w) ≠ 0 := by
    intro h
    have hi : ((α : ℂ) * w).im = α * w.im := by simp
    have hz := exp_eq_one_strip (w := (α : ℂ) * w)
      (by rw [hi]; nlinarith [mul_le_mul_of_nonneg_left hw.1 ha0.le, Real.pi_pos])
      (by rw [hi]; nlinarith [mul_le_mul_of_nonneg_left hw.2 ha0.le, Real.pi_pos])
      (sub_eq_zero.mp h).symm
    exact hw0 ((mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr ha0.ne'))
  have hd : DifferentiableAt ℂ (fun z : ℂ =>
      (1 / (1 - Complex.exp z) - (α : ℂ) * Complex.exp ((α : ℂ) * z) /
        (Complex.exp z * (1 - Complex.exp ((α : ℂ) * z)))) /
          ((α - 1 : ℝ) : ℂ)) w := by
    have he : DifferentiableAt ℂ Complex.exp w := Complex.differentiableAt_exp
    have ha : DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((α : ℂ) * z)) w :=
      ((differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) w).const_mul
        (α : ℂ)).cexp
    have h1 : DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) w := differentiableAt_const _
    exact ((h1.div (h1.sub he) he1).sub
      ((ha.const_mul _).div (he.mul (h1.sub ha))
        (mul_ne_zero (Complex.exp_ne_zero _) hea))).div_const _
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hw0] with z hz
  exact ite_eq_right hz

private def contourKernel (α r : ℝ) (w : ℂ) : ℂ :=
  Complex.exp w * dslope (logTransform α) (Real.log r : ℂ) w /
    dslope Complex.exp (Real.log r : ℂ) w

private lemma expSlope_ne_zero {c : ℝ} {w : ℂ}
    (hw : -Real.pi ≤ w.im ∧ w.im ≤ Real.pi) :
    dslope Complex.exp (c : ℂ) w ≠ 0 := by
  by_cases heq : w = (c : ℂ)
  · subst w
    simpa only [dslope_same, Complex.deriv_exp] using Complex.exp_ne_zero (c : ℂ)
  rw [dslope_of_ne _ heq, slope_def_field]
  refine div_ne_zero ?_ (sub_ne_zero.mpr heq)
  intro he
  have hexp : Complex.exp (w - c) = 1 :=
    Complex.exp_eq_exp_iff_exp_sub_eq_one.mp (sub_eq_zero.mp he)
  have hz := exp_eq_one_strip (w := w - c)
    (by simpa using (show -(2 * Real.pi) < w.im by linarith [Real.pi_pos]))
    (by simpa using (show w.im < 2 * Real.pi by linarith [Real.pi_pos])) hexp
  exact heq (sub_eq_zero.mp hz)

private lemma contourKernel_differentiable {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2) :
    DifferentiableOn ℂ (contourKernel α r)
      {w : ℂ | -Real.pi ≤ w.im ∧ w.im ≤ Real.pi} := by
  have hn : {w : ℂ | -Real.pi ≤ w.im ∧ w.im ≤ Real.pi} ∈ 𝓝 (Real.log r : ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)).mem_nhds
        (show -Real.pi < (Real.log r : ℂ).im ∧ (Real.log r : ℂ).im < Real.pi by
          simpa using And.intro (neg_neg_of_pos Real.pi_pos) Real.pi_pos))
    exact fun _ hw => ⟨hw.1.le, hw.2.le⟩
  have hf : DifferentiableOn ℂ (logTransform α)
      {w : ℂ | -Real.pi ≤ w.im ∧ w.im ≤ Real.pi} :=
    fun _ hw => (logTransform_differentiable ha0 ha2 hw).differentiableWithinAt
  exact (Complex.differentiable_exp.differentiableOn.mul
    ((Complex.differentiableOn_dslope hn).mpr hf)).div
      ((Complex.differentiableOn_dslope hn).mpr
        Complex.differentiable_exp.differentiableOn) (fun _ hw => expSlope_ne_zero hw)

private lemma contourKernel_eq {α r : ℝ} (hr0 : 0 < r) {w : ℂ}
    (hw : w ≠ (Real.log r : ℂ)) :
    contourKernel α r w = Complex.exp w *
      (logTransform α w - logTransform α (Real.log r : ℂ)) / (Complex.exp w - r) := by
  rw [contourKernel.eq_1]
  simp only [dslope_of_ne _ hw, slope_def_field,
    ← Complex.ofReal_exp, Real.exp_log hr0]
  field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr hw)

private lemma contour_rectangle {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (T : ℝ) :
    (∫ x in (-T)..T, contourKernel α r (x - Real.pi * Complex.I)) -
      (∫ x in (-T)..T, contourKernel α r (x + Real.pi * Complex.I)) +
      Complex.I * (∫ y in (-Real.pi)..Real.pi, contourKernel α r (T + y * Complex.I)) -
      Complex.I * (∫ y in (-Real.pi)..Real.pi, contourKernel α r (-T + y * Complex.I)) = 0 := by
  have hd := contourKernel_differentiable (r := r) ha0 ha2
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (contourKernel α r) ⟨-T, -Real.pi⟩ ⟨T, Real.pi⟩ (hd.mono (by
      intro w hw
      have hy : w.im ∈ Set.uIcc (-Real.pi) Real.pi := hw.2
      change -Real.pi ≤ w.im ∧ w.im ≤ Real.pi
      simpa only [Set.uIcc_of_le (neg_le_self Real.pi_pos.le), Set.mem_Icc] using hy))
  simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg, smul_eq_mul] using h

private lemma transform_boundary {α q : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hq : 0 < q) :
    -(complexTransform α (-(q : ℂ))).im / Real.pi = density α q := by
  have hD :=
    power_poisson_denominator_pos
      (r := q ^ α) ha0 ha2 ha1
  have hpow := Complex.cpow_ofReal (-(q : ℂ)) α
  have harg := Complex.arg_ofReal_of_neg (neg_neg_of_pos hq)
  rw [Complex.ofReal_neg] at harg
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, harg] at hpow
  dsimp only [complexTransform, density]
  rw [hpow, Complex.div_ofReal_im]
  simp only [Complex.div_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.normSq_apply, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, zero_sub, mul_one, zero_div, neg_zero, ← pow_two,
    zero_pow (by decide : (2 : ℕ) ≠ 0)]
  rw [Real.rpow_sub_one hq.ne']
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * α)
  have hnorm : (-q * (1 - q ^ α * Real.cos (Real.pi * α))) ^ 2 +
      (-q * -(q ^ α * Real.sin (Real.pi * α))) ^ 2 =
      q ^ 2 * (1 - 2 * q ^ α * Real.cos (Real.pi * α) + (q ^ α) ^ 2) := by
    nlinarith [congrArg (fun t : ℝ => q ^ 2 * (q ^ α) ^ 2 * t) htrig]
  rw [hnorm]
  field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr ha1)
  ring

private lemma transform_positive {α r : ℝ} (ha0 : 0 < α) (ha1 : α ≠ 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    (complexTransform α (r : ℂ)).re =
      1 / ((α - 1) * (1 - r)) - α * r ^ (α - 1) / ((α - 1) * (1 - r ^ α)) := by
  have he : complexTransform α (r : ℂ) =
      (((1 / (1 - r) - α * r ^ α / (r * (1 - r ^ α))) / (α - 1) : ℝ) : ℂ) := by
    dsimp only [complexTransform]
    rw [← Complex.ofReal_cpow hr0.le α]
    push_cast
    rfl
  rw [he, Complex.ofReal_re, Real.rpow_sub_one hr0.ne']
  have hden : 0 < 1 - r ^ α := sub_pos.mpr (Real.rpow_lt_one hr0.le hr1 ha0)
  field_simp (disch := first | positivity | assumption | exact sub_ne_zero.mpr ha1)

private lemma logTransform_boundary (α x : ℝ) :
    logTransform α (x + Real.pi * Complex.I) =
      complexTransform α (-(Real.exp x : ℂ)) := by
  have hw : (x : ℂ) + Real.pi * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have he : Complex.exp ((x : ℂ) + Real.pi * Complex.I) = -(Real.exp x : ℂ) := by
    simpa only [← Complex.ofReal_exp] using Complex.exp_add_pi_mul_I (x : ℂ)
  have hp : (Complex.exp ((x : ℂ) + Real.pi * Complex.I)) ^ (α : ℂ) =
      Complex.exp ((α : ℂ) * ((x : ℂ) + Real.pi * Complex.I)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp)]
    congr 1
    ring
  rw [logTransform, ite_eq_right hw, ← he]
  simp only [complexTransform, hp]

private lemma logTransform_conj (α : ℝ) {w : ℂ} (hw : w ≠ 0) :
    logTransform α (conj w) = conj (logTransform α w) := by
  have hc : conj w ≠ 0 := by simpa using hw
  simp only [logTransform, ite_eq_right hw, ite_eq_right hc]
  simp [← Complex.exp_conj]

private lemma logTransform_log {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (hr0 : 0 < r) (hr1 : r < 1) :
    logTransform α (Real.log r : ℂ) = complexTransform α (r : ℂ) := by
  rw [logTransform_eq_regular ha0 ha2 (by simp [Real.pi_pos]) (by simp [Real.pi_pos]),
    ← Complex.ofReal_exp, Real.exp_log hr0]
  exact regularTransform_eq ha0 ha2 (Complex.ofReal_ne_zero.mpr hr0.ne')
    (by exact_mod_cast hr1.ne)

private lemma transform_im_zero {α r : ℝ} (hr0 : 0 < r) :
    (complexTransform α (r : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  dsimp only [complexTransform]
  rw [← Complex.ofReal_cpow hr0.le]
  simp

private lemma contourKernel_top {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) :
    contourKernel α r (x + Real.pi * Complex.I) =
      ((Real.exp x / (r + Real.exp x) : ℝ) : ℂ) *
        (complexTransform α (-(Real.exp x : ℂ)) - complexTransform α (r : ℂ)) := by
  have hw : (x : ℂ) + Real.pi * Complex.I ≠ (Real.log r : ℂ) := by
    intro h
    have := congrArg Complex.im h
    simp at this
  rw [contourKernel_eq hr0 hw, logTransform_boundary,
    logTransform_log ha0 ha2 hr0 hr1, Complex.exp_add_pi_mul_I, ← Complex.ofReal_exp]
  push_cast
  field_simp (disch := first | positivity | assumption)
  rw [show -Complex.exp (x : ℂ) - (r : ℂ) =
    -(Complex.exp (x : ℂ) + (r : ℂ)) by ring, div_neg, neg_neg, add_comm]

private lemma contourKernel_top_im {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) :
    (contourKernel α r (x + Real.pi * Complex.I)).im =
      -Real.pi * (Real.exp x * (density α (Real.exp x) / (r + Real.exp x))) := by
  rw [contourKernel_top ha0 ha2 hr0 hr1, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_im, transform_im_zero hr0]
  have hb := transform_boundary ha0 ha2 ha1 (Real.exp_pos x)
  have hi := (div_eq_iff Real.pi_ne_zero).mp hb
  simp only [zero_mul, add_zero, sub_zero]
  field_simp (disch := first | positivity | assumption)
  nlinarith [hi]

private lemma contourKernel_bottom {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (hr0 : 0 < r) (hr1 : r < 1) (x : ℝ) :
    contourKernel α r (x - Real.pi * Complex.I) =
      conj (contourKernel α r (x + Real.pi * Complex.I)) := by
  have hw : (x : ℂ) - Real.pi * Complex.I ≠ (Real.log r : ℂ) := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hw0 : (x : ℂ) + Real.pi * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hc : (x : ℂ) - Real.pi * Complex.I = conj ((x : ℂ) + Real.pi * Complex.I) := by
    simp [sub_eq_add_neg]
  rw [contourKernel_eq hr0 hw, hc, logTransform_conj α hw0,
    logTransform_log ha0 ha2 hr0 hr1, contourKernel_top ha0 ha2 hr0 hr1,
    logTransform_boundary]
  have hf := Complex.conj_eq_iff_im.mpr (transform_im_zero (α := α) hr0)
  rw [Complex.exp_conj, Complex.exp_add_pi_mul_I, ← Complex.ofReal_exp]
  simp only [map_neg, Complex.conj_ofReal, map_mul, map_sub, hf]
  push_cast
  field_simp (disch := first | positivity | assumption)
  rw [show -Complex.exp (x : ℂ) - (r : ℂ) =
    -(Complex.exp (x : ℂ) + (r : ℂ)) by ring, div_neg, neg_neg, add_comm]

private lemma contourKernel_line_continuous {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    {y : ℝ} (hy : -Real.pi ≤ y ∧ y ≤ Real.pi) :
    Continuous (fun x : ℝ => contourKernel α r (x + y * Complex.I)) := by
  apply continuousOn_univ.mp
  apply (contourKernel_differentiable (r := r) ha0 ha2).continuousOn.comp
    (show ContinuousOn (fun x : ℝ => (x : ℂ) + y * Complex.I) univ by fun_prop)
  intro x _
  simpa only [Set.mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
    zero_add] using hy

private lemma contour_balance {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) (T : ℝ) :
    2 * Real.pi * (∫ x in (-T)..T,
      Real.exp x * (density α (Real.exp x) / (r + Real.exp x))) =
      (∫ y in (-Real.pi)..Real.pi, contourKernel α r (-T + y * Complex.I)).re -
      (∫ y in (-Real.pi)..Real.pi, contourKernel α r (T + y * Complex.I)).re := by
  have hi : IntervalIntegrable (fun x : ℝ =>
      contourKernel α r (x + Real.pi * Complex.I)) volume (-T) T :=
    (contourKernel_line_continuous ha0 ha2
      ⟨by linarith [Real.pi_pos], le_rfl⟩).intervalIntegrable _ _
  have ht : (∫ x in (-T)..T, contourKernel α r (x + Real.pi * Complex.I)).im =
      -Real.pi * (∫ x in (-T)..T,
        Real.exp x * (density α (Real.exp x) / (r + Real.exp x))) := by
    rw [← show (∫ x in (-T)..T,
      (contourKernel α r (x + Real.pi * Complex.I)).im) =
        (∫ x in (-T)..T, contourKernel α r (x + Real.pi * Complex.I)).im from
          Complex.imCLM.intervalIntegral_comp_comm hi,
      ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr
      (fun x _ => contourKernel_top_im ha0 ha2 ha1 hr0 hr1 x)
  have hb : (∫ x in (-T)..T, contourKernel α r (x - Real.pi * Complex.I)).im =
      -(∫ x in (-T)..T, contourKernel α r (x + Real.pi * Complex.I)).im := by
    have he : (∫ x in (-T)..T, contourKernel α r (x - Real.pi * Complex.I)) =
        conj (∫ x in (-T)..T, contourKernel α r (x + Real.pi * Complex.I)) := by
      rw [← intervalIntegral.intervalIntegral_conj]
      exact intervalIntegral.integral_congr
        (fun x _ => contourKernel_bottom ha0 ha2 hr0 hr1 x)
    rw [he, Complex.conj_im]
  have h := congrArg Complex.im (contour_rectangle (r := r) ha0 ha2 T)
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im] at h
  rw [hb, ht] at h
  nlinarith

private lemma logTransform_weighted (α : ℝ) {w : ℂ} (hw : w ≠ 0) :
    Complex.exp w * logTransform α w =
      (Complex.exp w / (1 - Complex.exp w) - (α : ℂ) *
        (Complex.exp ((α : ℂ) * w) / (1 - Complex.exp ((α : ℂ) * w)))) /
          ((α - 1 : ℝ) : ℂ) := by
  rw [logTransform, ite_eq_right hw]
  field_simp (disch := exact Complex.exp_ne_zero _)

private lemma norm_ratio_large {z : ℂ} (hz : 2 ≤ ‖z‖) : ‖z / (1 - z)‖ ≤ 2 := by
  have hd : ‖z‖ - 1 ≤ ‖1 - z‖ := by
    simpa only [norm_one, norm_sub_rev] using norm_sub_norm_le z (1 : ℂ)
  rw [norm_div]
  apply (div_le_iff₀ (show 0 < ‖1 - z‖ by linarith)).mpr
  linarith

private lemma norm_ratio_small {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖z / (1 - z)‖ ≤ 2 * ‖z‖ := by
  have hd : 1 - ‖z‖ ≤ ‖1 - z‖ := by
    simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) z
  rw [norm_div]
  apply (div_le_iff₀ (show 0 < ‖1 - z‖ by linarith)).mpr
  have hm := mul_le_mul_of_nonneg_left (show 1 / 2 ≤ ‖1 - z‖ by linarith)
    (norm_nonneg z)
  nlinarith

private lemma logTransform_weighted_bound {α : ℝ} (ha0 : 0 < α) {w : ℂ} (hw : w ≠ 0) :
    ‖Complex.exp w * logTransform α w‖ ≤
      (‖Complex.exp w / (1 - Complex.exp w)‖ +
        α * ‖Complex.exp ((α : ℂ) * w) / (1 - Complex.exp ((α : ℂ) * w))‖) /
          |α - 1| := by
  rw [logTransform_weighted α hw, norm_div, Complex.norm_real, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0] using
    norm_sub_le (Complex.exp w / (1 - Complex.exp w))
      ((α : ℂ) * (Complex.exp ((α : ℂ) * w) / (1 - Complex.exp ((α : ℂ) * w))))

private lemma vertical_integrable {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (x : ℝ) :
    IntervalIntegrable (fun y : ℝ => contourKernel α r (x + y * Complex.I))
      volume (-Real.pi) Real.pi := by
  apply ContinuousOn.intervalIntegrable
  apply (contourKernel_differentiable (r := r) ha0 ha2).continuousOn.comp
    (show ContinuousOn (fun y : ℝ => (x : ℂ) + y * Complex.I)
      (Set.uIcc (-Real.pi) Real.pi) by fun_prop)
  intro y hy
  have hy' : -Real.pi ≤ y ∧ y ≤ Real.pi := by
    simpa only [Set.uIcc_of_le (neg_le_self Real.pi_pos.le), Set.mem_Icc] using hy
  simpa using hy'

private lemma vertical_integral_limit {f : ℝ → ℝ → ℂ} {L : ℂ} {b : ℝ → ℝ}
    (hi : ∀ T, IntervalIntegrable (f T) volume (-Real.pi) Real.pi)
    (hb : Filter.Tendsto b Filter.atTop (𝓝 0))
    (hf : ∀ᶠ T in Filter.atTop, ∀ y ∈ Set.uIoc (-Real.pi) Real.pi,
      ‖f T y - L‖ ≤ b T) :
    Filter.Tendsto (fun T => ∫ y in (-Real.pi)..Real.pi, f T y) Filter.atTop
      (𝓝 ((Real.pi - -Real.pi) • L)) := by
  have hz : Filter.Tendsto (fun T => ∫ y in (-Real.pi)..Real.pi, f T y - L)
      Filter.atTop (𝓝 (0 : ℂ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (hf.mono (fun T hT => intervalIntegral.norm_integral_le_of_norm_le_const hT))
    simpa using hb.mul_const |Real.pi - -Real.pi|
  have he : ∀ T, (∫ y in (-Real.pi)..Real.pi, f T y - L) =
      (∫ y in (-Real.pi)..Real.pi, f T y) - (Real.pi - -Real.pi) • L := by
    intro T
    rw [intervalIntegral.integral_sub (hi T) intervalIntegrable_const,
      intervalIntegral.integral_const]
  simpa only [he, sub_add_cancel, zero_add] using hz.add_const ((Real.pi - -Real.pi) • L)

private lemma contour_right_limit {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    Filter.Tendsto (fun T : ℝ =>
      ∫ y in (-Real.pi)..Real.pi, contourKernel α r (T + y * Complex.I)) Filter.atTop
        (𝓝 ((Real.pi - -Real.pi) • (-complexTransform α (r : ℂ)))) := by
  let c := complexTransform α (r : ℂ)
  let C := (2 + α * 2) / |α - 1|
  let b := fun T : ℝ => 2 * (C + r * ‖c‖) * Real.exp (-T)
  apply vertical_integral_limit (fun T => vertical_integrable ha0 ha2 T) (b := b)
  · simpa [b] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (2 * (C + r * ‖c‖))
  have hat : Filter.Tendsto (fun T : ℝ => Real.exp (α * T)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop ha0)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    Real.tendsto_exp_atTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hat.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    Real.tendsto_exp_atTop.eventually (Filter.eventually_ge_atTop (2 * r))]
    with T ht hT haT hrT
  intro y _
  let w : ℂ := T + y * Complex.I
  have he : ‖Complex.exp w‖ = Real.exp T := by simp [w, Complex.norm_exp]
  have hea : ‖Complex.exp ((α : ℂ) * w)‖ = Real.exp (α * T) := by
    simp [w, Complex.norm_exp, Complex.mul_re]
  have hw : w ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp [w] at hh
    linarith
  have hwl : w ≠ (Real.log r : ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    simp [w] at hh
    linarith [Real.log_neg hr0 hr1]
  have hP : ‖Complex.exp w * logTransform α w‖ ≤ C := by
    apply (logTransform_weighted_bound ha0 hw).trans
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    exact add_le_add (norm_ratio_large (by rwa [he]))
      (mul_le_mul_of_nonneg_left (norm_ratio_large (by rwa [hea])) ha0.le)
  have hd : Real.exp T - r ≤ ‖Complex.exp w - (r : ℂ)‖ := by
    simpa only [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using
      norm_sub_norm_le (Complex.exp w) (r : ℂ)
  have hd0 : 0 < ‖Complex.exp w - (r : ℂ)‖ := by linarith [Real.exp_pos T]
  have hdne := norm_ne_zero_iff.mp hd0.ne'
  have hk : contourKernel α r w - -c =
      (Complex.exp w * logTransform α w - (r : ℂ) * c) / (Complex.exp w - r) := by
    rw [contourKernel_eq hr0 hwl, logTransform_log ha0 ha2 hr0 hr1]
    change Complex.exp w * (logTransform α w - c) / (Complex.exp w - r) - -c = _
    field_simp (disch := assumption)
    ring
  rw [hk, norm_div]
  apply (div_le_iff₀ hd0).mpr
  calc
    _ ≤ C + r * ‖c‖ := by
      exact (norm_sub_le _ _).trans (add_le_add hP (by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, le_rfl]))
    _ = b T * (Real.exp T / 2) := by
      dsimp only [b]
      rw [Real.exp_neg]
      field_simp (disch := positivity)
    _ ≤ b T * ‖Complex.exp w - (r : ℂ)‖ := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      dsimp only [b, C]
      positivity

private lemma contour_left_limit {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    Filter.Tendsto (fun T : ℝ =>
      ∫ y in (-Real.pi)..Real.pi, contourKernel α r (-T + y * Complex.I)) Filter.atTop
        (𝓝 (0 : ℂ)) := by
  let c := complexTransform α (r : ℂ)
  let A := fun T : ℝ =>
    (2 * Real.exp (-T) + α * (2 * Real.exp (-(α * T)))) / |α - 1|
  let b := fun T : ℝ => (2 / r) * (A T + Real.exp (-T) * ‖c‖)
  have he0 := Real.tendsto_exp_neg_atTop_nhds_zero
  have hea0 := he0.comp (Filter.tendsto_id.const_mul_atTop ha0)
  have hA : Filter.Tendsto A Filter.atTop (𝓝 0) := by
    simpa [A] using ((he0.const_mul 2).add ((hea0.const_mul 2).const_mul α)).div_const |α - 1|
  have hb : Filter.Tendsto b Filter.atTop (𝓝 0) := by
    simpa [b] using (hA.add (he0.mul_const ‖c‖)).const_mul (2 / r)
  have hz := vertical_integral_limit (L := (0 : ℂ))
    (fun T => vertical_integrable (r := r) ha0 ha2 (-T)) hb
  simp only [smul_zero, Complex.ofReal_neg] at hz
  apply hz
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    he0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hea0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    he0.eventually (gt_mem_nhds (half_pos hr0))] with T ht hT haT hrT
  intro y _
  let w : ℂ := -T + y * Complex.I
  have he : ‖Complex.exp w‖ = Real.exp (-T) := by simp [w, Complex.norm_exp]
  have hea : ‖Complex.exp ((α : ℂ) * w)‖ = Real.exp (-(α * T)) := by
    simp [w, Complex.norm_exp, Complex.mul_re, mul_neg]
  have hw : w ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp [w] at hh
    linarith
  have hwl : w ≠ (Real.log r : ℂ) := by
    intro h
    have hh : ‖Complex.exp w‖ = r := by
      rw [h, ← Complex.ofReal_exp, Real.exp_log hr0]
      simp [abs_of_pos hr0]
    rw [he] at hh
    linarith
  have hP : ‖Complex.exp w * logTransform α w‖ ≤ A T := by
    apply (logTransform_weighted_bound ha0 hw).trans
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    have h1 := norm_ratio_small (z := Complex.exp w) (by rw [he]; exact hT.le)
    have h2 := norm_ratio_small (z := Complex.exp ((α : ℂ) * w))
      (by rw [hea]; exact haT.le)
    simpa only [he, hea] using add_le_add h1 (mul_le_mul_of_nonneg_left h2 ha0.le)
  have hd : r - Real.exp (-T) ≤ ‖Complex.exp w - (r : ℂ)‖ := by
    simpa only [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, norm_sub_rev] using
      norm_sub_norm_le (r : ℂ) (Complex.exp w)
  have hd0 : 0 < ‖Complex.exp w - (r : ℂ)‖ := by linarith
  rw [sub_zero, contourKernel_eq hr0 hwl, logTransform_log ha0 ha2 hr0 hr1]
  change ‖Complex.exp w * (logTransform α w - c) / (Complex.exp w - r)‖ ≤ b T
  rw [mul_sub, norm_div]
  apply (div_le_iff₀ hd0).mpr
  calc
    _ ≤ A T + Real.exp (-T) * ‖c‖ :=
      (norm_sub_le _ _).trans (add_le_add hP (by simp only [norm_mul, he, le_rfl]))
    _ = b T * (r / 2) := by dsimp only [b]; field_simp (disch := positivity)
    _ ≤ b T * ‖Complex.exp w - (r : ℂ)‖ := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      dsimp only [b, A]
      positivity

private lemma slit_transform_integral {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    (∫ q in Ioi (0 : ℝ), -(complexTransform α (-(q : ℂ))).im /
      (Real.pi * (r + q))) = (complexTransform α (r : ℂ)).re := by
  let g := fun x : ℝ => Real.exp x * (density α (Real.exp x) / (r + Real.exp x))
  have hi : Integrable g := by
    simpa only [g, smul_eq_mul] using
      (integrable_comp_exp (fun q => density α q / (r + q))).mpr
        (density_resolvent_integrable ha0 ha2 ha1 hr0)
  have htr := intervalIntegral_tendsto_integral hi
    Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hleft := (Complex.continuous_re.tendsto (0 : ℂ)).comp
    (contour_left_limit ha0 ha2 ha1 hr0 hr1)
  have hright := (Complex.continuous_re.tendsto
    ((Real.pi - -Real.pi) • (-complexTransform α (r : ℂ)))).comp
      (contour_right_limit ha0 ha2 ha1 hr0 hr1)
  have hlim : Filter.Tendsto (fun T : ℝ => 2 * Real.pi * (∫ x in (-T)..T, g x))
      Filter.atTop (𝓝 (2 * Real.pi * (complexTransform α (r : ℂ)).re)) := by
    convert hleft.sub hright using 1
    · funext T
      exact contour_balance ha0 ha2 ha1 hr0 hr1 T
    · simp only [Complex.zero_re, Complex.smul_re, Complex.neg_re]
      dsimp only [smul_eq_mul]
      ring
  have he : (∫ x, g x) = (complexTransform α (r : ℂ)).re := by
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    exact tendsto_nhds_unique (htr.const_mul (2 * Real.pi)) hlim
  calc
    _ = ∫ q in Ioi (0 : ℝ), density α q / (r + q) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro q hq
      dsimp only
      rw [← div_div, transform_boundary ha0 ha2 ha1 hq]
    _ = ∫ x, g x := by
      simpa only [g, smul_eq_mul] using
        (integral_comp_exp (fun q => density α q / (r + q))).symm
    _ = _ := he

private lemma stieltjes_value {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    (∫ q in Ioi (0 : ℝ), density α q / (r + q)) =
      1 / ((α - 1) * (1 - r)) -
        α * r ^ (α - 1) / ((α - 1) * (1 - r ^ α)) := by
  rw [← transform_positive ha0 ha1 hr0 hr1,
    ← slit_transform_integral ha0 ha2 ha1 hr0 hr1]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro q hq
  dsimp only
  rw [← transform_boundary ha0 ha2 ha1 hq, div_div]

/-- Stieltjes transform on the positive axis, with its pole at `r = 1` subtracted. -/
theorem stieltjes_integral {α r : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    IntegrableOn (fun q => density α q / (r + q)) (Ioi 0) ∧
      (∫ q in Ioi (0 : ℝ), density α q / (r + q)) =
        1 / ((α - 1) * (1 - r)) -
          α * r ^ (α - 1) / ((α - 1) * (1 - r ^ α)) := by
  exact ⟨density_resolvent_integrable ha0 ha2 ha1 hr0, stieltjes_value ha0 ha2 ha1 hr0 hr1⟩

end

end D5.S3.Quantum.Analysis.BosonicRenyiStieltjes.PoissonWeight
