/- GID: D5/S3/Analytic/Asymptotics/WeightedFilterStability
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/WeightedFilterStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An exponentially decaying error stays bounded under the Robin Laplace response. -/

import D5.S3.Analytic.Asymptotics.WeightedFilterLeadingMode
import D5.S3.Analytic.Asymptotics.WeightedFilterTailTransmutation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-! Stability of the Robin Laplace response under an exponentially decaying remainder. -/

open MeasureTheory Set
open WeightedFilterCDF WeightedFilterLeadingMode

noncomputable section

namespace WeightedFilterStability

private abbrev halfLine := (volume : Measure ℝ).restrict (Ici 0)

private def density (t y : ℝ) : ℝ := (1 + y) * Real.exp (-t * y)

private def laplaceBracket (B : ℝ → ℝ) (y : ℝ) : ℝ :=
  B 0 - y * (∫ v : ℝ in Ici 0, Real.exp (-y * v) * B v)

private theorem exp_integrable {a : ℝ} (ha : a < 0) :
    Integrable (fun v : ℝ => Real.exp (a * v)) halfLine := by
  change IntegrableOn _ (Ici (0 : ℝ))
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi ha 0

private theorem density_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (density t) halfLine :=
  WeightedFilterTailTransmutation.integrableOn_laplace_density ht

private theorem integral_density {t : ℝ} (ht : 0 < t) :
    (∫ y, density t y ∂halfLine) = weight t := by
  rw [← integral_tail_exp ht, tailMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  apply setIntegral_congr_fun measurableSet_Ici
  intro y hy
  have hn : 0 ≤ 1 + y := by linarith [mem_Ici.mp hy]
  simp only [density, ENNReal.toReal_ofReal hn, smul_eq_mul]

private theorem laplaceBracket_measurable {D : ℝ → ℝ}
    (hD : AEMeasurable D halfLine) : Measurable (laplaceBracket D) := by
  have hprod : Measurable (fun z : ℝ × ℝ =>
      Real.exp (-z.1 * z.2) * hD.mk D z.2) :=
    (show Measurable (fun z : ℝ × ℝ => Real.exp (-z.1 * z.2)) by fun_prop).mul
      (hD.measurable_mk.comp measurable_snd)
  have hint : Measurable (fun y : ℝ =>
      ∫ v, Real.exp (-y * v) * hD.mk D v ∂halfLine) :=
    (hprod.stronglyMeasurable.integral_prod_right' (ν := halfLine)).measurable
  have heq (y : ℝ) :
      (∫ v, Real.exp (-y * v) * D v ∂halfLine) =
        ∫ v, Real.exp (-y * v) * hD.mk D v ∂halfLine :=
    integral_congr_ae (hD.ae_eq_mk.mono fun v hv =>
      congrArg (fun z => Real.exp (-y * v) * z) hv)
  unfold laplaceBracket
  simp_rw [heq]
  exact measurable_const.sub (measurable_id.mul hint)

private theorem laplaceBracket_error {D : ℝ → ℝ} {δ E y : ℝ}
    (hD : AEMeasurable D halfLine) (hδ : δ < 0) (hE : 0 ≤ E)
    (herror : ∀ v : ℝ, 0 ≤ v → |D v| ≤ E * Real.exp (δ * v))
    (hy : 0 ≤ y) :
    Integrable (fun v => Real.exp (-y * v) * D v) halfLine ∧
      |laplaceBracket D y| ≤ 2 * E := by
  have hδy : δ - y < 0 := by linarith
  have hdom : Integrable (fun v => E * Real.exp ((δ - y) * v)) halfLine :=
    (exp_integrable hδy).const_mul E
  have hbound : ∀ᵐ v ∂halfLine, ‖Real.exp (-y * v) * D v‖ ≤
      E * Real.exp ((δ - y) * v) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ici (a := (0 : ℝ)))]
      with v hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-y * v) * (E * Real.exp (δ * v)) :=
        mul_le_mul_of_nonneg_left (herror v (mem_Ici.mp hv)) (Real.exp_pos _).le
      _ = _ := by
        rw [show (δ - y) * v = -y * v + δ * v by ring, Real.exp_add]
        ring
  refine ⟨hdom.mono' ((show Measurable (fun v : ℝ => Real.exp (-y * v)) by
    fun_prop).aestronglyMeasurable.mul hD.aestronglyMeasurable) hbound, ?_⟩
  have hzero : |D 0| ≤ E := by simpa using herror 0 le_rfl
  rcases eq_or_lt_of_le hy with hzero_y | hy_pos
  · subst y
    simp only [laplaceBracket, zero_mul, sub_zero]
    linarith only [hzero, hE]
  have hLap : |∫ v, Real.exp (-y * v) * D v ∂halfLine| ≤ E / (y - δ) := by
    calc
      _ ≤ ∫ v, E * Real.exp ((δ - y) * v) ∂halfLine := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hdom hbound
      _ = _ := by
        rw [integral_const_mul]
        change E * (∫ v : ℝ in Ici 0, Real.exp ((δ - y) * v)) = _
        rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hδy 0]
        simp only [mul_zero, Real.exp_zero]
        rw [show δ - y = -(y - δ) by ring, neg_div_neg_eq, ← mul_div_assoc, mul_one]
  have hscaled : y * (E / (y - δ)) ≤ E := by
    calc
      _ = E * (y / (y - δ)) := by ring
      _ ≤ E := mul_le_of_le_one_right hE
        ((div_le_one (by linarith only [hy_pos, hδ])).mpr (by linarith only [hδ]))
  unfold laplaceBracket
  calc
    _ ≤ |D 0| + |y * (∫ v, Real.exp (-y * v) * D v ∂halfLine)| := by
      simpa only [Real.norm_eq_abs] using
        norm_sub_le (D 0) (y * (∫ v, Real.exp (-y * v) * D v ∂halfLine))
    _ ≤ E + y * (E / (y - δ)) := by
      rw [abs_mul, abs_of_nonneg hy]
      exact add_le_add hzero (mul_le_mul_of_nonneg_left hLap hy)
    _ ≤ 2 * E := by linarith only [hscaled]

private def mode (A lam : ℂ) (v : ℝ) : ℝ := (A * Complex.exp (lam * (v : ℂ))).re

private theorem denominator_norm_ge {lam : ℂ} {y : ℝ} (hy : 0 ≤ y) :
    -lam.re ≤ ‖(y : ℂ) - lam‖ := by
  have hre := Complex.re_le_norm ((y : ℂ) - lam)
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  linarith only [hy, hre]

private theorem laplaceBracket_mode {A lam : ℂ} {y : ℝ}
    (hlam : lam.re < 0) (hy : 0 ≤ y) :
    Integrable (fun v => Real.exp (-y * v) * mode A lam v) halfLine ∧
      laplaceBracket (mode A lam) y = (A * (-lam / ((y : ℂ) - lam))).re := by
  let a : ℂ := lam - (y : ℂ)
  let f : ℝ → ℂ := fun v => A * Complex.exp (a * (v : ℂ))
  have ha : a.re < 0 := by
    dsimp only [a]
    rw [Complex.sub_re, Complex.ofReal_re]
    linarith only [hlam, hy]
  have hf : Integrable f halfLine := by
    change IntegrableOn _ (Ici (0 : ℝ))
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_exp_mul_complex_Ioi ha 0).const_mul A
  have hp (v : ℝ) : Real.exp (-y * v) * mode A lam v = (f v).re := by
    have hprod :
        (Real.exp (-y * v) : ℂ) * (A * Complex.exp (lam * (v : ℂ))) = f v := by
      have hexp : a * (v : ℂ) =
          lam * (v : ℂ) + ((-y * v : ℝ) : ℂ) := by
        simp only [a, Complex.ofReal_mul, Complex.ofReal_neg]
        ring
      dsimp only [f]
      rw [hexp, Complex.exp_add, ← Complex.ofReal_exp (-y * v)]
      ring
    rw [← hprod]
    simp only [mode, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hshift : (y : ℂ) - lam = -a := by simp only [a, neg_sub]
  have hfi : (∫ v, f v ∂halfLine) = A / ((y : ℂ) - lam) := by
    change (∫ v : ℝ in Ici 0, A * Complex.exp (a * (v : ℂ))) = _
    rw [integral_const_mul, integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi ha 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, hshift,
      div_eq_mul_inv, neg_one_mul, inv_neg]
  have hreal : (∫ v, Real.exp (-y * v) * mode A lam v ∂halfLine) =
      (A / ((y : ℂ) - lam)).re := by
    calc
      _ = ∫ v, (f v).re ∂halfLine := integral_congr_ae (ae_of_all _ hp)
      _ = (∫ v, f v ∂halfLine).re := integral_re hf
      _ = _ := congrArg Complex.re hfi
  refine ⟨hf.re.congr (ae_of_all _ fun v => (hp v).symm), ?_⟩
  have hne : (y : ℂ) - lam ≠ 0 :=
    norm_pos_iff.mp ((neg_pos.mpr hlam).trans_le (denominator_norm_ge hy))
  have halg : A - (y : ℂ) * (A / ((y : ℂ) - lam)) =
      A * (-lam / ((y : ℂ) - lam)) := by
    field_simp [hne]
    ring
  unfold laplaceBracket
  rw [hreal, ← halg]
  simp only [mode, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- A decaying error in the unweighted average costs at most twice its initial
envelope in the exact scalar Laplace expression for the weighted Robin tail. -/
theorem abs_laplace_sub_re_response_le
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {h t δ E : ℝ} {A lam : ℂ}
    {B : ℝ → ℝ} (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (ht : 0 < t)
    (hlam : lam.re < 0) (hδ : δ < 0) (hE : 0 ≤ E)
    (hB : AEMeasurable B (volume.restrict (Ici (0 : ℝ))))
    (happrox : ∀ v : ℝ, 0 ≤ v →
      |B v - (A * Complex.exp (lam * (v : ℂ))).re| ≤ E * Real.exp (δ * v)) :
    |(∫ y : ℝ in Ici 0, ((1 + y) * Real.exp (-t * y) / moment μ y) *
        (B 0 - y * (∫ v : ℝ in Ici 0, Real.exp (-y * v) * B v))) -
      (A * response μ lam t).re| ≤ 2 * E * weight t := by
  let D : ℝ → ℝ := fun v => B v - mode A lam v
  let coeff : ℝ → ℝ := fun y => density t y / moment μ y
  let g : ℝ → ℂ := fun y => (coeff y : ℂ) * (A * (-lam / ((y : ℂ) - lam)))
  let err : ℝ → ℝ := fun y => coeff y * laplaceBracket D y
  have hhalf : ∀ᵐ y ∂halfLine, y ∈ Ici (0 : ℝ) := ae_restrict_mem measurableSet_Ici
  have hd := density_integrable ht
  have hD : AEMeasurable D halfLine :=
    hB.sub ((Complex.measurable_re.comp (show Measurable
      (fun v : ℝ => A * Complex.exp (lam * (v : ℂ))) by fun_prop)).aemeasurable)
  have hpoint (y : ℝ) (hy : 0 ≤ y) :=
    laplaceBracket_error hD hδ hE happrox hy
  have hM : Measurable (moment μ) := by
    have hm : Measurable (fun z : ℝ × ℝ => Real.exp (z.1 * z.2)) := by fun_prop
    exact (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hcoeffM : Measurable coeff :=
    (show Measurable (density t) by unfold density; fun_prop).div hM
  have hcoeff (y : ℝ) (hy : 0 ≤ y) : 0 ≤ coeff y ∧ coeff y ≤ density t y := by
    have hd₀ : 0 ≤ density t y :=
      mul_nonneg (by linarith only [hy]) (Real.exp_pos _).le
    have hM₁ := (moment_bounds hμ hy).1
    exact ⟨div_nonneg hd₀ (zero_le_one.trans hM₁), div_le_self hd₀ hM₁⟩
  have hg : Integrable g halfLine := by
    have hgm : Measurable g :=
      (Complex.measurable_ofReal.comp hcoeffM).mul (measurable_const.mul
        (measurable_const.div (Complex.measurable_ofReal.sub measurable_const)))
    let C : ℝ := ‖A‖ * (‖lam‖ / (-lam.re))
    have hC : 0 ≤ C := mul_nonneg (norm_nonneg _)
      (div_nonneg (norm_nonneg _) (neg_nonneg.mpr hlam.le))
    apply (hd.const_mul C).mono' hgm.aestronglyMeasurable
    filter_upwards [hhalf] with y hy
    obtain ⟨hc₀, hc⟩ := hcoeff y (mem_Ici.mp hy)
    change ‖(coeff y : ℂ) * (A * (-lam / ((y : ℂ) - lam)))‖ ≤ C * density t y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc₀,
      norm_mul, Complex.norm_div, norm_neg]
    have hratio : ‖lam‖ / ‖(y : ℂ) - lam‖ ≤ ‖lam‖ / (-lam.re) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (neg_pos.mpr hlam)
        (denominator_norm_ge (mem_Ici.mp hy))
    calc
      _ ≤ coeff y * C :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hratio (norm_nonneg _)) hc₀
      _ ≤ density t y * C := mul_le_mul_of_nonneg_right hc hC
      _ = C * density t y := mul_comm _ _
  have hresponse : (A * response μ lam t).re = ∫ y, (g y).re ∂halfLine := by
    rw [response_eq_integral_Ici, ← integral_const_mul]
    calc
      _ = (∫ y, g y ∂halfLine).re := by
        apply congrArg Complex.re
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          change A * (↑(density t y) * multiplier μ lam y) =
            ↑(density t y / moment μ y) * (A * (-lam / ((y : ℂ) - lam)))
          simp only [multiplier, div_eq_mul_inv, Complex.ofReal_mul,
            Complex.ofReal_inv, mul_inv_rev]
          ring
      _ = _ := (integral_re hg).symm
  have herrBound : ∀ᵐ y ∂halfLine, ‖err y‖ ≤ (2 * E) * density t y := by
    filter_upwards [hhalf] with y hy
    obtain ⟨hc₀, hc⟩ := hcoeff y (mem_Ici.mp hy)
    change ‖coeff y * laplaceBracket D y‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc₀, mul_comm (2 * E)]
    exact mul_le_mul hc (hpoint y (mem_Ici.mp hy)).2 (abs_nonneg _)
      (hc₀.trans hc)
  have herr : Integrable err halfLine :=
    (hd.const_mul (2 * E)).mono'
      (hcoeffM.mul (laplaceBracket_measurable hD)).aestronglyMeasurable herrBound
  have hsplit (y : ℝ) (hy : 0 ≤ y) :
      laplaceBracket B y = laplaceBracket D y + (A * (-lam / ((y : ℂ) - lam))).re := by
    obtain ⟨hmodeI, hmode⟩ := laplaceBracket_mode (A := A) hlam hy
    have hsum : (fun v : ℝ => Real.exp (-y * v) * B v) =
        fun v => Real.exp (-y * v) * D v + Real.exp (-y * v) * mode A lam v := by
      funext v
      dsimp only [D]
      ring
    rw [← hmode]
    simp only [laplaceBracket]
    rw [hsum, integral_add (hpoint y hy).1 hmodeI]
    dsimp only [D]
    ring
  have htransfer :
      (∫ y, coeff y * laplaceBracket B y ∂halfLine) =
        (∫ y, err y ∂halfLine) + ∫ y, (g y).re ∂halfLine := by
    have hgr : Integrable (fun y => (g y).re) halfLine := hg.re
    rw [← integral_add herr hgr]
    apply setIntegral_congr_fun measurableSet_Ici
    intro y hy
    change coeff y * laplaceBracket B y = err y + (g y).re
    rw [hsplit y (mem_Ici.mp hy)]
    simp only [g, err, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, mul_add]
  change |(∫ y, coeff y * laplaceBracket B y ∂halfLine) -
    (A * response μ lam t).re| ≤ 2 * E * weight t
  rw [htransfer, hresponse, add_sub_cancel_right]
  calc
    _ ≤ ∫ y, (2 * E) * density t y ∂halfLine := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_of_norm_le (hd.const_mul (2 * E)) herrBound
    _ = _ := by rw [integral_const_mul, integral_density ht]

end WeightedFilterStability
