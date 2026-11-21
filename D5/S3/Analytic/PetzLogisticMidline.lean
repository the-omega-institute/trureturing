/- GID: D5/S3/Analytic/PetzLogisticMidline
   generality: G
   mirror-B: D5/B/S3/Analytic/PetzLogisticMidline
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The reflected Hilbert strip gives the exact logistic boundary difference estimate. -/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The logistic contour on the closed Yang strip. The left edge is included by
Cauchy–Goursat for continuous boundary values. Only the horizontal edges go to infinity. -/

namespace PetzLogisticMidline

open Complex Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section

def line (x t : ℝ) : ℂ := x + t * I

@[simp] theorem line_re (x t : ℝ) : (line x t).re = x := by simp [line]
@[simp] theorem line_im (x t : ℝ) : (line x t).im = t := by simp [line]

theorem continuous_line (x : ℝ) : Continuous (line x) := by unfold line; fun_prop

def closedStrip : Set ℂ := re ⁻¹' Icc 0 (1 / 2)

def openStrip : Set ℂ := re ⁻¹' Ioo 0 (1 / 2)

def upperWeight (t : ℝ) : ℝ := Real.pi / (Real.cosh (2 * Real.pi * t) + 1)

def lowerWeight (t : ℝ) : ℝ := Real.pi / (Real.cosh (2 * Real.pi * t) - 1)

def midlineWeight (t : ℝ) : ℝ := Real.pi / Real.cosh (2 * Real.pi * t) ^ 2

def kernelDen (z : ℂ) : ℂ := 1 + Complex.cos (2 * (Real.pi : ℂ) * z)

def kernel (z : ℂ) : ℂ := (Real.pi : ℂ) / kernelDen z

private theorem kernelDen_line (x t : ℝ) :
    kernelDen (line x t) =
      (1 + (Real.cos (2 * Real.pi * x) * Real.cosh (2 * Real.pi * t) : ℝ)) -
        (Real.sin (2 * Real.pi * x) * Real.sinh (2 * Real.pi * t) : ℝ) * I := by
  unfold kernelDen line
  rw [show 2 * (Real.pi : ℂ) * ((x : ℂ) + (t : ℂ) * I) =
    ((2 * Real.pi * x : ℝ) : ℂ) + ((2 * Real.pi * t : ℝ) : ℂ) * I by push_cast; ring]
  rw [Complex.cos_add_mul_I]
  push_cast
  ring

private theorem cos_nonneg_strip {x : ℝ} (hx : x ∈ Icc 0 (1 / 4 : ℝ)) :
    0 ≤ Real.cos (2 * Real.pi * x) := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> nlinarith [Real.pi_pos, hx.1, hx.2]

private theorem norm_kernelDen_line {x : ℝ} (hx : x ∈ Icc 0 (1 / 4 : ℝ)) (t : ℝ) :
    ‖kernelDen (line x t)‖ = Real.cosh (2 * Real.pi * t) + Real.cos (2 * Real.pi * x) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (add_nonneg (Real.cosh_pos _).le (cos_nonneg_strip hx))).mp
  rw [Complex.sq_norm, kernelDen_line, Complex.normSq_apply]
  simp only [sub_re, add_re, one_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, sub_zero,
    sub_im, add_im, one_im, add_zero, mul_I_im, zero_sub]
  let c := Real.cos (2 * Real.pi * x)
  let s := Real.sin (2 * Real.pi * x)
  let ch := Real.cosh (2 * Real.pi * t)
  let sh := Real.sinh (2 * Real.pi * t)
  change (1 + c * ch) * (1 + c * ch) + (- (s * sh)) * (- (s * sh)) = (ch + c) ^ 2
  have hcs : s ^ 2 = 1 - c ^ 2 := by linarith [Real.sin_sq_add_cos_sq (2 * Real.pi * x)]
  have hh : sh ^ 2 = ch ^ 2 - 1 := by linarith [Real.cosh_sq_sub_sinh_sq (2 * Real.pi * t)]
  calc
    _ = (1 + c * ch) ^ 2 + s ^ 2 * sh ^ 2 := by ring
    _ = _ := by rw [hcs, hh]; ring

private theorem kernelDen_ne_zero {z : ℂ} (hz : z.re ∈ Icc 0 (1 / 4 : ℝ)) :
    kernelDen z ≠ 0 := by
  have hz' : line z.re z.im = z := by apply Complex.ext <;> simp
  rw [← hz', ← norm_ne_zero_iff, norm_kernelDen_line hz]
  exact (add_pos_of_pos_of_nonneg (Real.cosh_pos _) (cos_nonneg_strip hz)).ne'

private theorem continuousOn_kernel : ContinuousOn kernel (re ⁻¹' Icc 0 (1 / 4 : ℝ)) := by
  unfold kernel
  exact continuousOn_const.div (by unfold kernelDen; fun_prop) (fun _ h => kernelDen_ne_zero h)

private theorem differentiableAt_kernel {z : ℂ} (hz : z.re ∈ Icc 0 (1 / 4 : ℝ)) :
    DifferentiableAt ℂ kernel z := by
  unfold kernel
  refine DifferentiableAt.div (by fun_prop) ?_ (kernelDen_ne_zero hz)
  unfold kernelDen
  fun_prop

private theorem cosh_lower (u : ℝ) : Real.exp |u| / 2 ≤ Real.cosh u := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  linarith [Real.exp_pos (-|u|)]

private theorem norm_kernel_le {x : ℝ} (hx : x ∈ Icc 0 (1 / 4 : ℝ)) (t : ℝ) :
    ‖kernel (line x t)‖ ≤ (2 * Real.pi) * Real.exp (-(2 * Real.pi * |t|)) := by
  rw [kernel, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    norm_kernelDen_line hx]
  have hcosh := cosh_lower (2 * Real.pi * t)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)] at hcosh
  calc
    _ ≤ Real.pi / (Real.exp (2 * Real.pi * |t|) / 2) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
        (hcosh.trans (le_add_of_nonneg_right (cos_nonneg_strip hx)))
    _ = _ := by rw [Real.exp_neg, div_div_eq_mul_div, div_eq_mul_inv]; ring

private theorem integrable_decay :
    Integrable (fun t : ℝ => Real.exp (-(2 * Real.pi * |t|))) := by
  have ha : 0 < 2 * Real.pi := by positivity
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  apply IntegrableOn.union
  · refine (integrableOn_exp_mul_Iic ha 0).congr_fun ?_ measurableSet_Iic
    intro t ht
    dsimp only
    rw [abs_of_nonpos (mem_Iic.mp ht)]
    congr 1
    ring
  · refine (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [abs_of_pos (mem_Ioi.mp ht)]
    congr 1
    ring

private theorem kernel_zero (t : ℝ) : kernel (line 0 t) = (upperWeight t : ℂ) := by
  rw [kernel, kernelDen_line]
  simp [upperWeight, add_comm]

private theorem kernel_midline_re (t : ℝ) : (kernel (line (1 / 4) t)).re = midlineWeight t := by
  have h : 2 * Real.pi * (1 / 4) = Real.pi / 2 := by ring
  rw [kernel, kernelDen_line, h, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp only [zero_mul, ofReal_zero, add_zero, one_mul, Complex.div_re, ofReal_re,
    ofReal_im, zero_mul, zero_div, sub_re, sub_im, one_re, one_im, mul_I_re, mul_I_im,
    neg_zero, sub_zero, zero_sub, Complex.normSq_apply]
  unfold midlineWeight
  have hh := Real.cosh_sq_sub_sinh_sq (2 * Real.pi * t)
  have he : 1 + -Real.sinh (2 * Real.pi * t) * -Real.sinh (2 * Real.pi * t) =
      Real.cosh (2 * Real.pi * t) ^ 2 := by
    rw [neg_mul_neg, ← sq]
    linarith
  rw [he, mul_one]

/-- Vertical contour shift with continuity on the closed strip and holomorphy in
its interior. The real majorant bounds every vertical section, including the edges. -/
theorem vertical_integrals_eq {a b : ℝ} (hab : a ≤ b) {g : ℂ → ℂ}
    (hc : ContinuousOn g (re ⁻¹' Icc a b))
    (hd : ∀ z : ℂ, z.re ∈ Ioo a b → DifferentiableAt ℂ g z)
    {m : ℝ → ℝ} (hm : Integrable m)
    (hbound : ∀ x ∈ Icc a b, ∀ t, ‖g (line x t)‖ ≤ m t)
    (htop : Tendsto m atTop (𝓝 0)) (hbot : Tendsto m atBot (𝓝 0)) :
    (∀ x ∈ Icc a b, Integrable (fun t => g (line x t))) ∧
      (∫ t : ℝ, g (line a t)) = ∫ t : ℝ, g (line b t) := by
  have hi (x : ℝ) (hx : x ∈ Icc a b) : Integrable (fun t => g (line x t)) := by
    have hcont := hc.comp_continuous (continuous_line x)
      (fun t => by simpa using hx)
    exact hm.mono' hcont.aestronglyMeasurable (ae_of_all _ (hbound x hx))
  refine ⟨hi, ?_⟩
  let V (R : ℝ) := (∫ t in (-R)..R, g (line a t)) - (∫ t in (-R)..R, g (line b t))
  let E (t : ℝ) := ∫ x in a..b, g (line x t)
  have hrect {R : ℝ} (hR : 0 ≤ R) : V R = I * (E R - E (-R)) := by
    have H := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
      g (line a (-R)) (line b R) ∅ countable_empty
      (hc.mono (by
        intro z hz
        simpa only [mem_preimage, mem_reProdIm, line_re, uIcc_of_le hab] using hz.1))
      (fun z hz => hd z (by
        simpa only [line_re, min_eq_left hab, max_eq_right hab, mem_preimage] using hz.1.1))
    have H' : E (-R) - E R + I * (∫ t in (-R)..R, g (line b t)) -
        I * (∫ t in (-R)..R, g (line a t)) = 0 := by
      simp only [line_re, line_im, smul_eq_mul] at H
      simpa only [E, line] using H
    have hI : I * I = -1 := I_mul_I
    dsimp only [V]
    linear_combination I * H' + ((∫ t in (-R)..R, g (line a t)) -
      (∫ t in (-R)..R, g (line b t))) * hI
  have hE (t : ℝ) : ‖E t‖ ≤ m t * (b - a) := by
    rw [← abs_of_nonneg (sub_nonneg.mpr hab)]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    exact hbound x ⟨hx.1.le, hx.2⟩ t
  have hv : Tendsto V atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg (V R)) ?_
      (show Tendsto (fun R : ℝ => m R * (b - a) + m (-R) * (b - a)) atTop (𝓝 0) from ?_)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      rw [hrect hR, norm_mul, norm_I, one_mul]
      exact (norm_sub_le _ _).trans (add_le_add (hE R) (hE (-R)))
    · simpa using (htop.mul_const (b - a)).add
        ((hbot.comp tendsto_neg_atTop_atBot).mul_const (b - a))
  have hl := (intervalIntegral_tendsto_integral (hi a ⟨le_rfl, hab⟩)
      tendsto_neg_atTop_atBot tendsto_id).sub
    (intervalIntegral_tendsto_integral (hi b ⟨hab, le_rfl⟩)
      tendsto_neg_atTop_atBot tendsto_id)
  exact sub_eq_zero.mp (tendsto_nhds_unique hl hv)

/-- The shift for the logistic kernel on the left half of the Yang strip. -/
theorem weighted_vertical_integrals_eq {H : ℂ → ℂ}
    (hc : ContinuousOn H (re ⁻¹' Icc 0 (1 / 4 : ℝ)))
    (hd : ∀ z : ℂ, z.re ∈ Ioo 0 (1 / 4 : ℝ) → DifferentiableAt ℂ H z)
    {C : ℝ} (hb : ∀ z : ℂ, z.re ∈ Icc 0 (1 / 4 : ℝ) → ‖H z‖ ≤ C) :
    (∀ x ∈ Icc 0 (1 / 4 : ℝ), Integrable (fun t => kernel (line x t) * H (line x t))) ∧
      (∫ t : ℝ, kernel (line 0 t) * H (line 0 t)) =
        ∫ t : ℝ, kernel (line (1 / 4) t) * H (line (1 / 4) t) := by
  let m (t : ℝ) := (2 * Real.pi * C) * Real.exp (-(2 * Real.pi * |t|))
  have ht : Tendsto m atTop (𝓝 0) := by
    have hlin : Tendsto (fun t : ℝ => 2 * Real.pi * |t|) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (by positivity : 0 < 2 * Real.pi)).2 tendsto_abs_atTop_atTop
    simpa [m, Function.comp_def] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).const_mul (2 * Real.pi * C)
  have hl : Tendsto m atBot (𝓝 0) := by
    simpa [m, Function.comp_def] using ht.comp tendsto_neg_atBot_atTop
  apply vertical_integrals_eq (by norm_num) (continuousOn_kernel.mul hc)
    (fun z hz => (differentiableAt_kernel ⟨hz.1.le, hz.2.le⟩).mul (hd z hz))
    (integrable_decay.const_mul (2 * Real.pi * C)) _ ht hl
  intro x hx t
  change ‖kernel (line x t) * H (line x t)‖ ≤ m t
  rw [norm_mul]
  calc
    _ ≤ ((2 * Real.pi) * Real.exp (-(2 * Real.pi * |t|))) * C :=
      mul_le_mul (norm_kernel_le hx t) (hb _ (by simpa using hx)) (norm_nonneg _) (mul_nonneg (by positivity) (Real.exp_nonneg _))
    _ = m t := by dsimp [m]; ring

def reflect (z : ℂ) : ℂ := (1 / 2 : ℂ) - conj z

private theorem reflect_line (x t : ℝ) : reflect (line x t) = line (1 / 2 - x) t := by
  apply Complex.ext <;> simp [reflect, line]

private theorem reflect_re (z : ℂ) : (reflect z).re = 1 / 2 - z.re := by
  have he : line z.re z.im = z := by apply Complex.ext <;> simp
  rw [← he, reflect_line, line_re, line_re]

private theorem line_mem (x t : ℝ) (hx : x ∈ Icc 0 (1 / 2 : ℝ)) :
    line x t ∈ closedStrip := by
  simpa only [closedStrip, mem_preimage, line_re] using hx

private theorem reflect_mem {z : ℂ} (hz : z ∈ closedStrip) : reflect z ∈ closedStrip := by
  change 0 ≤ z.re ∧ z.re ≤ 1 / 2 at hz
  change 0 ≤ (reflect z).re ∧ (reflect z).re ≤ 1 / 2
  rw [reflect_re]
  constructor <;> linarith [hz.1, hz.2]

section Hilbert

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Mathlib's inner product is conjugate-linear in its first argument. -/
def reflectedPair (f : ℂ → E) (z : ℂ) : ℂ := ⟪f (reflect z), f z⟫_ℂ

/-- The reflected inner product is complex differentiable even for an
infinite-dimensional target. Its real derivative is complex-linear because the
conjugation in the reflection cancels the one in the first slot. -/
theorem differentiableAt_reflectedPair {f : ℂ → E} {z : ℂ}
    (hz : DifferentiableAt ℂ f z) (hr : DifferentiableAt ℂ f (reflect z)) :
    DifferentiableAt ℂ (reflectedPair f) z := by
  have hReflect : HasFDerivAt reflect
      (-Complex.conjCLE.toContinuousLinearMap) z := by
    change HasFDerivAt (fun x : ℂ => (1 / 2 : ℂ) - Complex.conjCLE.toContinuousLinearMap x) _ z
    exact (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z)).const_sub (1 / 2 : ℂ)
  let v := deriv f (reflect z)
  let w := deriv f z
  have hv : HasDerivAt f v (reflect z) := hr.hasDerivAt
  have hw : HasDerivAt f w z := hz.hasDerivAt
  have hleft := (hv.hasFDerivAt.restrictScalars ℝ).comp z hReflect
  have hreal := hleft.inner ℂ (hw.hasFDerivAt.restrictScalars ℝ)
  let d : ℂ := ⟪f (reflect z), w⟫_ℂ - ⟪v, f z⟫_ℂ
  let D : ℂ →L[ℂ] ℂ := (1 : ℂ →L[ℂ] ℂ).smulRight d
  apply (hasFDerivAt_of_restrictScalars ℝ (f' := D) hreal ?_).differentiableAt
  ext u : 1
  change u * d = ⟪f (reflect z), u • w⟫_ℂ + ⟪(-conj u) • v, f z⟫_ℂ
  simp only [inner_smul_right, inner_smul_left, map_neg, Complex.conj_conj, d]
  ring

private theorem continuousOn_reflectedPair {f : ℂ → E} (hc : ContinuousOn f closedStrip) :
    ContinuousOn (reflectedPair f) closedStrip := by
  have hr : Continuous reflect := by unfold reflect; fun_prop
  exact (hc.comp hr.continuousOn (fun _ h => reflect_mem h)).inner hc

/-- The exact midline identity, with absolute integrability on both lines. -/
theorem integral_midline {f : ℂ → E}
    (hc : ContinuousOn f closedStrip) (hd : DifferentiableOn ℂ f openStrip)
    {B : ℝ} (hb : ∀ z ∈ closedStrip, ‖f z‖ ≤ B) :
    Integrable (fun t => upperWeight t * (reflectedPair f (line 0 t)).re) ∧
      Integrable (fun t => midlineWeight t * ‖f (line (1 / 4) t)‖ ^ 2) ∧
      (∫ t, upperWeight t * (reflectedPair f (line 0 t)).re) =
        ∫ t, midlineWeight t * ‖f (line (1 / 4) t)‖ ^ 2 := by
  have hOpen : IsOpen openStrip := continuous_re.isOpen_preimage _ isOpen_Ioo
  have hf (z : ℂ) (hz : z ∈ openStrip) : DifferentiableAt ℂ f z :=
    hd.differentiableAt (hOpen.mem_nhds hz)
  have hsmall : re ⁻¹' Icc 0 (1 / 4 : ℝ) ⊆ closedStrip :=
    fun _ h => ⟨h.1, h.2.trans (by norm_num)⟩
  have hB : 0 ≤ B := (norm_nonneg _).trans (hb _ (line_mem 0 0 (by norm_num)))
  obtain ⟨hi, he⟩ := weighted_vertical_integrals_eq
    ((continuousOn_reflectedPair hc).mono hsmall)
    (fun z hz => differentiableAt_reflectedPair
      (hf z ⟨hz.1, hz.2.trans (by norm_num)⟩)
      (hf (reflect z) (by
        change 0 < (reflect z).re ∧ (reflect z).re < 1 / 2
        rw [reflect_re]
        constructor <;> linarith [hz.1, hz.2])))
    (fun z hz => by
      exact (norm_inner_le_norm _ _).trans
        (by simpa only [pow_two] using
          (mul_le_mul (hb _ (reflect_mem (hsmall hz))) (hb _ (hsmall hz))
            (norm_nonneg _) hB)))
  have h0 (t : ℝ) : (kernel (line 0 t) * reflectedPair f (line 0 t)).re =
      upperWeight t * (reflectedPair f (line 0 t)).re := by
    rw [kernel_zero]
    simp [Complex.mul_re]
  have hm (t : ℝ) : (kernel (line (1 / 4) t) * reflectedPair f (line (1 / 4) t)).re =
      midlineWeight t * ‖f (line (1 / 4) t)‖ ^ 2 := by
    have hr : reflect (line (1 / 4) t) = line (1 / 4) t := by rw [reflect_line]; norm_num
    rw [reflectedPair, hr, inner_self_eq_norm_sq_to_K]
    change (kernel (line (1 / 4) t) * ((‖f (line (1 / 4) t)‖ : ℝ) : ℂ) ^ 2).re = _
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      kernel_midline_re]
  have hi0 := (hi 0 (by norm_num)).re
  have him := (hi (1 / 4) (by norm_num)).re
  have he' := congrArg Complex.re he
  change RCLike.re (∫ t : ℝ, kernel (line 0 t) * reflectedPair f (line 0 t)) =
    RCLike.re (∫ t : ℝ, kernel (line (1 / 4) t) * reflectedPair f (line (1 / 4) t)) at he'
  rw [← integral_re (hi 0 (by norm_num)), ← integral_re (hi (1 / 4) (by norm_num))] at he'
  simpa only [show (RCLike.re : ℂ → ℝ) = Complex.re from rfl, h0, hm] using
    And.intro hi0 (And.intro him he')

private theorem upperWeight_nonneg (t : ℝ) : 0 ≤ upperWeight t := by
  unfold upperWeight
  positivity [Real.cosh_pos (2 * Real.pi * t)]

private theorem continuous_upperWeight : Continuous upperWeight := by
  unfold upperWeight
  exact continuous_const.div (by fun_prop) (fun t => by positivity [Real.cosh_pos (2 * Real.pi * t)])

theorem integrable_upperWeight : Integrable upperWeight := by
  refine (integrable_decay.const_mul (2 * Real.pi)).mono' ?_ (ae_of_all _ fun t => ?_)
  · exact continuous_upperWeight.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (upperWeight_nonneg t)]
    simpa only [kernel_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (upperWeight_nonneg t)] using norm_kernel_le (x := 0) (by norm_num) t

theorem weight_difference_eq {t : ℝ} (ht : t ≠ 0) :
    lowerWeight t - upperWeight t = 2 * Real.pi / Real.sinh (2 * Real.pi * t) ^ 2 := by
  let u := 2 * Real.pi * t
  have hs : Real.sinh u ≠ 0 := by
    exact fun h => (mul_ne_zero (by positivity : 2 * Real.pi ≠ 0) ht) (Real.sinh_eq_zero.mp h)
  have hc := Real.cosh_sq_sub_sinh_sq u
  have hp : Real.cosh u + 1 ≠ 0 := by positivity
  have hm : Real.cosh u - 1 ≠ 0 := by
    intro h
    have he : Real.cosh u = 1 := by linarith
    rw [he] at hc
    exact hs (by nlinarith)
  change Real.pi / (Real.cosh u - 1) - Real.pi / (Real.cosh u + 1) =
    2 * Real.pi / Real.sinh u ^ 2
  have he : (Real.cosh u - 1) * (Real.cosh u + 1) = Real.sinh u ^ 2 := by
    nlinarith
  rw [← he]
  field_simp
  ring

private theorem upperWeight_le_lowerWeight {t : ℝ} (ht : t ≠ 0) :
    upperWeight t ≤ lowerWeight t := by
  rw [← sub_nonneg, weight_difference_eq ht]
  positivity

omit [InnerProductSpace ℂ E] in
private theorem line_continuous {f : ℂ → E} (hc : ContinuousOn f closedStrip)
    {x : ℝ} (hx : x ∈ Icc 0 (1 / 2 : ℝ)) : Continuous (fun t => f (line x t)) :=
  hc.comp_continuous (continuous_line x) (fun t => line_mem x t hx)

omit [InnerProductSpace ℂ E] in
private theorem integrable_weighted_norm_sq {g : ℝ → E} (hc : Continuous g) {B : ℝ}
    (hb : ∀ t, ‖g t‖ ≤ B) : Integrable (fun t => upperWeight t * ‖g t‖ ^ 2) := by
  refine (integrable_upperWeight.mul_const (B ^ 2)).mono' ?_ (ae_of_all _ fun t => ?_)
  · apply Continuous.aestronglyMeasurable
    exact continuous_upperWeight.mul (hc.norm.pow 2)
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (upperWeight_nonneg t) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hb t) 2) (upperWeight_nonneg t)

/-- The full logistic boundary energy, together with its exact nonnegative remainder.
Only the singular lower boundary energy needs an integrability hypothesis. -/
theorem full_logistic_strip {f : ℂ → E}
    (hc : ContinuousOn f closedStrip) (hd : DifferentiableOn ℂ f openStrip)
    {B : ℝ} (hb : ∀ z ∈ closedStrip, ‖f z‖ ≤ B)
    (hLower : Integrable (fun t => lowerWeight t * ‖f (line 0 t)‖ ^ 2)) :
    Integrable (fun t => upperWeight t * ‖f (line (1 / 2) t) - f (line 0 t)‖ ^ 2) ∧
      (∫ t, lowerWeight t * ‖f (line 0 t)‖ ^ 2) +
        (∫ t, upperWeight t * ‖f (line (1 / 2) t)‖ ^ 2) -
        (∫ t, upperWeight t * ‖f (line (1 / 2) t) - f (line 0 t)‖ ^ 2) =
        (∫ t, (lowerWeight t - upperWeight t) * ‖f (line 0 t)‖ ^ 2) +
          2 * (∫ t, midlineWeight t * ‖f (line (1 / 4) t)‖ ^ 2) ∧
      (∫ t, upperWeight t * ‖f (line (1 / 2) t) - f (line 0 t)‖ ^ 2) ≤
        (∫ t, lowerWeight t * ‖f (line 0 t)‖ ^ 2) +
          (∫ t, upperWeight t * ‖f (line (1 / 2) t)‖ ^ 2) := by
  have h0 t := hb (line 0 t) (line_mem 0 t (by norm_num))
  have h1 t := hb (line (1 / 2) t) (line_mem _ _ (by norm_num))
  have hc0 := line_continuous hc (x := 0) (by norm_num)
  have hc1 := line_continuous hc (x := 1 / 2) (by norm_num)
  have hInt0 := integrable_weighted_norm_sq hc0 h0
  have hInt1 := integrable_weighted_norm_sq hc1 h1
  have hIntD := integrable_weighted_norm_sq (hc1.sub hc0) (B := B + B)
    (fun t => (norm_sub_le _ _).trans (add_le_add (h1 t) (h0 t)))
  obtain ⟨hPair, _, hMid⟩ := integral_midline hc hd hb
  have hPoint (t : ℝ) :
      upperWeight t * ‖f (line (1 / 2) t) - f (line 0 t)‖ ^ 2 =
        upperWeight t * ‖f (line (1 / 2) t)‖ ^ 2 + upperWeight t * ‖f (line 0 t)‖ ^ 2 -
          2 * (upperWeight t * (reflectedPair f (line 0 t)).re) := by
    rw [reflectedPair, reflect_line, sub_zero, norm_sub_sq (𝕜 := ℂ)]
    simp only [show (RCLike.re : ℂ → ℝ) = Complex.re from rfl]
    ring
  have hEnergy : (∫ t, upperWeight t * ‖f (line (1 / 2) t) - f (line 0 t)‖ ^ 2) =
      (∫ t, upperWeight t * ‖f (line (1 / 2) t)‖ ^ 2) +
        (∫ t, upperWeight t * ‖f (line 0 t)‖ ^ 2) -
        2 * (∫ t, midlineWeight t * ‖f (line (1 / 4) t)‖ ^ 2) := by
    simp_rw [hPoint]
    have hSum : Integrable (fun t => upperWeight t * ‖f (line (1 / 2) t)‖ ^ 2 +
        upperWeight t * ‖f (line 0 t)‖ ^ 2) := hInt1.add hInt0
    rw [integral_sub hSum (hPair.const_mul 2),
      integral_add hInt1 hInt0, integral_const_mul, hMid]
  have hRemainder : (∫ t, lowerWeight t * ‖f (line 0 t)‖ ^ 2) +
      (∫ t, upperWeight t * ‖f (line (1 / 2) t)‖ ^ 2) -
      (∫ t, upperWeight t * ‖f (line (1 / 2) t) - f (line 0 t)‖ ^ 2) =
      (∫ t, (lowerWeight t - upperWeight t) * ‖f (line 0 t)‖ ^ 2) +
        2 * (∫ t, midlineWeight t * ‖f (line (1 / 4) t)‖ ^ 2) := by
    rw [hEnergy]
    simp_rw [sub_mul]
    rw [integral_sub hLower hInt0]
    ring
  refine ⟨hIntD, hRemainder, sub_nonneg.mp ?_⟩
  rw [hRemainder]
  have hLeft : 0 ≤ ∫ t, (lowerWeight t - upperWeight t) * ‖f (line 0 t)‖ ^ 2 := by
    apply integral_nonneg_of_ae
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
    exact mul_nonneg (sub_nonneg.mpr (upperWeight_le_lowerWeight ht)) (sq_nonneg _)
  exact add_nonneg hLeft (mul_nonneg (by norm_num)
    (integral_nonneg fun _ => mul_nonneg (by unfold midlineWeight; positivity) (sq_nonneg _)))

end Hilbert

end

end PetzLogisticMidline
