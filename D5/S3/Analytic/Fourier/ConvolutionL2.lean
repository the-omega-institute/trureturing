/- GID: D5/S3/Analytic/Fourier/ConvolutionL2
   generality: G
   mirror-B: D5/B/S3/Analytic/Fourier/ConvolutionL2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Young and Schwartz multiplier bounds control convolution on square-integrable functions. -/

import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic

/-! Concrete Young and Fourier multiplier inequalities on the real line. -/

namespace D5.S3.Analytic.Fourier.ConvolutionL2

open MeasureTheory Filter Set
open scoped NNReal ENNReal FourierTransform Topology

noncomputable def conv (k f : ℝ → ℂ) : ℝ → ℂ :=
  convolution k f (ContinuousLinearMap.mul ℂ ℂ) volume

private lemma weighted_cauchy {a b : ℝ → ℝ≥0∞}
    (ha : AEMeasurable a volume) (hb : AEMeasurable b volume) :
    (∫⁻ v, a v * b v) ^ 2 ≤ (∫⁻ v, a v) * ∫⁻ v, a v * b v ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    (ha.pow_const (1 / 2 : ℝ)) ((ha.pow_const (1 / 2 : ℝ)).mul hb)
  have hhalf (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hsquare (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, ← mul_assoc (a _ ^ (1 / 2 : ℝ)), hhalf,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), hsquare,
    ENNReal.rpow_two] at h
  have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul] at h2
  norm_num at h2
  exact h2

private lemma norm_two_sq (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 ^ 2 = ∫⁻ y, ‖f y‖ₑ ^ 2 := by
  simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using
    eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf

/-- Young's inequality for an integrable kernel and a square-integrable function. -/
theorem convolution_memLp_two {q f : ℝ → ℂ} (hq : Integrable q) (hf : MemLp f 2) :
    MemLp (conv q f) 2 ∧
      eLpNorm (conv q f) 2 ≤ ENNReal.ofReal (∫ v, ‖q v‖) * eLpNorm f 2 := by
  have hmeas : AEStronglyMeasurable (conv q f) volume :=
    hq.aestronglyMeasurable.convolution (ContinuousLinearMap.mul ℂ ℂ) hf.aestronglyMeasurable
  have hprod : AEMeasurable
      (fun p : ℝ × ℝ => ‖q p.2‖ₑ * ‖f (p.1 - p.2)‖ₑ ^ 2) (volume.prod volume) := by
    have h := hq.aestronglyMeasurable.norm.convolution_integrand
      (ContinuousLinearMap.mul ℝ ℝ) hf.norm.aestronglyMeasurable
    have hf2 := hf.aestronglyMeasurable.enorm.pow_const (2 : ℕ)
    exact hq.aestronglyMeasurable.enorm.comp_snd.mul
      (hf2.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  have hpoint (y : ℝ) : ‖conv q f y‖ₑ ^ 2 ≤
      (∫⁻ v, ‖q v‖ₑ) * ∫⁻ v, ‖q v‖ₑ * ‖f (y - v)‖ₑ ^ 2 := by
    calc
      _ ≤ (∫⁻ v, ‖q v‖ₑ * ‖f (y - v)‖ₑ) ^ 2 := by
        apply pow_le_pow_left'
        simpa [conv, convolution_def, enorm_mul] using
          enorm_integral_le_lintegral_enorm (fun v => q v * f (y - v))
      _ ≤ _ := weighted_cauchy hq.aestronglyMeasurable.enorm
        (hf.aestronglyMeasurable.comp_measurePreserving
          (volume.measurePreserving_sub_left y)).enorm
  have htranslate (v : ℝ) : (∫⁻ y, ‖f (y - v)‖ₑ ^ 2) = eLpNorm f 2 ^ 2 := by
    rw [norm_two_sq _ hf.aestronglyMeasurable]
    simpa only [sub_eq_add_neg] using
      (measurePreserving_add_right volume (-v)).lintegral_comp_emb
        (Homeomorph.addRight (-v)).measurableEmbedding (fun y => ‖f y‖ₑ ^ 2)
  have hinner (v : ℝ) : (∫⁻ y, ‖q v‖ₑ * ‖f (y - v)‖ₑ ^ 2) =
      ‖q v‖ₑ * eLpNorm f 2 ^ 2 := by
    rw [lintegral_const_mul'']
    · rw [htranslate]
    · simpa only [sub_eq_add_neg, Function.comp_def] using
        (hf.aestronglyMeasurable.comp_measurePreserving
          (measurePreserving_add_right volume (-v))).enorm.pow_const (2 : ℕ)
  have hsq : eLpNorm (conv q f) 2 ^ 2 ≤
      ((∫⁻ v, ‖q v‖ₑ) * eLpNorm f 2) ^ 2 := by
    rw [norm_two_sq _ hmeas]
    calc
      _ ≤ ∫⁻ y, (∫⁻ v, ‖q v‖ₑ) * ∫⁻ v, ‖q v‖ₑ * ‖f (y - v)‖ₑ ^ 2 :=
        lintegral_mono hpoint
      _ = (∫⁻ v, ‖q v‖ₑ) * ((∫⁻ v, ‖q v‖ₑ) * eLpNorm f 2 ^ 2) := by
        rw [lintegral_const_mul'' _ hprod.lintegral_prod_right', lintegral_lintegral_swap hprod]
        congr 1
        simp_rw [hinner]
        rw [lintegral_mul_const'']
        exact hq.aestronglyMeasurable.enorm
      _ = _ := by ring
  have hbound : eLpNorm (conv q f) 2 ≤ (∫⁻ v, ‖q v‖ₑ) * eLpNorm f 2 := by
    exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp (by
      simpa only [ENNReal.rpow_two] using hsq)
  have hqint : (∫⁻ v, ‖q v‖ₑ) = ENNReal.ofReal (∫ v, ‖q v‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal hq.norm (ae_of_all _ (fun _ => norm_nonneg _))]
    simp only [ofReal_norm]
  rw [hqint] at hbound
  exact ⟨hbound.trans_lt (by finiteness), hbound⟩

private lemma schwartz_plancherel (g : SchwartzMap ℝ ℂ) :
    eLpNorm ((𝓕 g : SchwartzMap ℝ ℂ) : ℝ → ℂ) 2 volume = eLpNorm g 2 := by
  calc
    _ = ENNReal.ofReal ‖(𝓕 g).toLp 2 volume‖ := by
      rw [SchwartzMap.norm_toLp (μ := volume), ENNReal.ofReal_toReal (𝓕 g |>.memLp 2).ne]
    _ = ENNReal.ofReal ‖g.toLp 2 volume‖ := by rw [SchwartzMap.norm_fourier_toL2_eq]
    _ = _ := by
      rw [SchwartzMap.norm_toLp (μ := volume)]
      exact ENNReal.ofReal_toReal (g.memLp 2 volume).ne

private lemma schwartz_multiplier (k g : SchwartzMap ℝ ℂ) {B : ℝ}
    (hbound : ∀ ξ, ‖𝓕 k ξ‖ ≤ B) :
    eLpNorm (conv k g) 2 ≤ ENNReal.ofReal B * eLpNorm g 2 := by
  let c := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) k g
  have hc : (c : ℝ → ℂ) = conv k g := by
    funext y
    exact SchwartzMap.convolution_apply _ k g y
  rw [← hc, ← schwartz_plancherel c]
  calc
    _ ≤ ENNReal.ofReal B * eLpNorm ((𝓕 g : SchwartzMap ℝ ℂ) : ℝ → ℂ) 2 volume := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (𝓕 c).continuous.aestronglyMeasurable
        (ae_of_all _ (fun ξ => ?_)) 2
      have hfourier : 𝓕 c ξ = 𝓕 (conv k g) ξ := by
        exact SchwartzMap.fourier_convolution_apply _ k g ξ
      rw [hfourier]
      change ‖𝓕 (convolution (k : ℝ → ℂ) g (ContinuousLinearMap.mul ℂ ℂ) volume) ξ‖ ≤ _
      rw [Real.fourier_mul_convolution_eq k.integrable g.integrable, norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound ξ) (norm_nonneg _)
    _ = _ := by rw [schwartz_plancherel g]

private lemma schwartz_approx {f : ℝ → ℂ} (hf : MemLp f 2) :
    ∃ g : ℕ → SchwartzMap ℝ ℂ,
      Tendsto (fun n => (g n).toLp 2) atTop (𝓝 (hf.toLp f)) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume) (by norm_num)
  obtain ⟨s, hs, ht⟩ := mem_closure_iff_seq_limit.mp (hd (hf.toLp f))
  choose g hg using hs
  refine ⟨g, ?_⟩
  have heq : s = fun n => (g n).toLp 2 volume := by
    funext n
    exact (hg n).symm
  rwa [heq] at ht

private lemma convolution_tendsto_of_schwartz_approx
    (k : SchwartzMap ℝ ℂ) {f : ℝ → ℂ} (hf : MemLp f 2)
    {g : ℕ → SchwartzMap ℝ ℂ}
    (hg : Tendsto (fun n => (g n).toLp 2) atTop (𝓝 (hf.toLp f))) (y : ℝ) :
    Tendsto (fun n => conv k (g n) y) atTop (𝓝 (conv k f y)) := by
  have hex (h : ℝ → ℂ) (hh : MemLp h 2) :
      ConvolutionExists k h (ContinuousLinearMap.mul ℂ ℂ) volume :=
    ConvolutionExists.of_memLp_memLp (p := 2) (q := 2) _ (k.memLp 2) hh
  have hdiff (n : ℕ) : conv k (g n) y - conv k f y =
      conv k ((g n : ℝ → ℂ) - f) y := by
    simp only [conv, convolution_def, Pi.sub_apply, ContinuousLinearMap.mul_apply', mul_sub]
    exact (integral_sub (hex (g n) ((g n).memLp 2) y) (hex f hf y)).symm
  have hsmall : Tendsto (fun n => eLpNorm ((g n : ℝ → ℂ) - f) 2) atTop (𝓝 0) := by
    have h := hg.edist (tendsto_const_nhds (x := hf.toLp f))
    change Tendsto (fun n => edist (((g n).memLp 2 volume).toLp (g n)) (hf.toLp f))
      atTop (𝓝 (edist (hf.toLp f) (hf.toLp f))) at h
    simpa only [edist_self, Lp.edist_toLp_toLp] using h
  have hbound (n : ℕ) : ‖conv k (g n) y - conv k f y‖ₑ ≤
      ‖ContinuousLinearMap.mul ℂ ℂ‖ₑ * eLpNorm k 2 *
        eLpNorm ((g n : ℝ → ℂ) - f) 2 := by
    rw [hdiff]
    exact enorm_convolution_le (p := 2) (q := 2) (ContinuousLinearMap.mul ℂ ℂ)
      k.continuous.aestronglyMeasurable
      (((g n).memLp 2).sub hf).aestronglyMeasurable y
  have hC : ‖ContinuousLinearMap.mul ℂ ℂ‖ₑ * eLpNorm (k : ℝ → ℂ) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top enorm_ne_top (k.memLp 2 volume).ne
  have hlim := ENNReal.Tendsto.const_mul
    (a := ‖ContinuousLinearMap.mul ℂ ℂ‖ₑ * eLpNorm (k : ℝ → ℂ) 2 volume)
    hsmall (Or.inr hC)
  simp only [mul_zero] at hlim
  have ht : Tendsto (fun n => ‖conv k (g n) y - conv k f y‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
      hlim (fun _ => bot_le) hbound
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa [enorm] using
    (ENNReal.tendsto_toReal_zero_iff (fun n => enorm_ne_top)).mpr ht

/-- A bounded Fourier transform of a Schwartz kernel controls its convolution operator on L². -/
theorem schwartz_convolution_l2_multiplier
    (k : SchwartzMap ℝ ℂ) {f : ℝ → ℂ} (hf : MemLp f 2) {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ ξ, ‖𝓕 k ξ‖ ≤ B) :
    MemLp (conv k f) 2 ∧
      eLpNorm (conv k f) 2 ≤ ENNReal.ofReal B * eLpNorm f 2 := by
  obtain ⟨g, hg⟩ := schwartz_approx hf
  have hmeas := k.continuous.aestronglyMeasurable.convolution
    (ContinuousLinearMap.mul ℂ ℂ) hf.aestronglyMeasurable
  have hgnorm : Tendsto (fun n => eLpNorm (g n) 2) atTop (𝓝 (eLpNorm f 2)) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hg.norm
    simpa only [Function.comp_def, SchwartzMap.norm_toLp (μ := volume), Lp.norm_toLp,
      ENNReal.ofReal_toReal hf.ne, ENNReal.ofReal_toReal ((g _).memLp 2).ne] using h
  have hmajor : Tendsto (fun n => ENNReal.ofReal B * eLpNorm (g n) 2) atTop
      (𝓝 (ENNReal.ofReal B * eLpNorm f 2)) :=
    ENNReal.Tendsto.const_mul hgnorm (Or.inr ENNReal.ofReal_ne_top)
  have hle : eLpNorm (conv k f) 2 ≤ ENNReal.ofReal B * eLpNorm f 2 := by
    apply le_of_forall_gt
    intro C hC
    obtain ⟨D, hD, hDC⟩ := exists_between hC
    apply lt_of_le_of_lt ?_ hDC
    apply Lp.eLpNorm_le_of_ae_tendsto
      ((hmajor.eventually (gt_mem_nhds hD)).mono (fun n hn =>
        (schwartz_multiplier k (g n) hbound).trans hn.le))
      (fun n => k.continuous.aestronglyMeasurable.convolution
        (ContinuousLinearMap.mul ℂ ℂ) (g n).continuous.aestronglyMeasurable)
      hmeas
      (ae_of_all _ (convolution_tendsto_of_schwartz_approx k hf hg))
  exact ⟨hle.trans_lt (by finiteness), hle⟩

private lemma complex_l2_integral {f : ℝ → ℂ} (hf : MemLp f 2) :
    (∫ y, ‖f y‖ ^ 2) = (eLpNorm f 2).toReal ^ 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun y => sq_nonneg ‖f y‖))
    (hf.aestronglyMeasurable.norm.pow 2), ← ENNReal.toReal_pow,
    norm_two_sq f hf.aestronglyMeasurable]
  congr 1
  apply lintegral_congr_ae
  filter_upwards with y
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma real_convolution_identity (k f : ℝ → ℝ) (y : ℝ) :
    conv (fun v => (k v : ℂ)) (fun v => (f v : ℂ)) y =
      ((∫ v, k v * f (y - v) : ℝ) : ℂ) := by
  simp only [conv, convolution_def, ContinuousLinearMap.mul_apply', ← Complex.ofReal_mul]
  exact integral_complex_ofReal

private lemma real_integral_bound {k f : ℝ → ℝ} (hf : MemLp f 2) {B : ℝ} (hB : 0 ≤ B)
    (hmem : MemLp (conv (fun v => (k v : ℂ)) (fun v => (f v : ℂ))) 2)
    (hbound : eLpNorm (conv (fun v => (k v : ℂ)) (fun v => (f v : ℂ))) 2 ≤
      ENNReal.ofReal B * eLpNorm (fun v => (f v : ℂ)) 2) :
    (∫ y, (∫ v, k v * f (y - v)) ^ 2) ≤ B ^ 2 * ∫ y, f y ^ 2 := by
  have hfC : MemLp (fun v => (f v : ℂ)) 2 := hf.ofReal
  have hnorm := ENNReal.toReal_mono (by finiteness) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] at hnorm
  have hsq := sq_le_sq₀ (by positivity : 0 ≤
    (eLpNorm (conv (fun v => (k v : ℂ)) (fun v => (f v : ℂ))) 2).toReal)
      (by positivity : 0 ≤ B * (eLpNorm (fun v => (f v : ℂ)) 2).toReal)
  have h := hsq.mpr hnorm
  rw [mul_pow, ← complex_l2_integral hmem, ← complex_l2_integral hfC] at h
  simpa only [real_convolution_identity, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

/-- A real integrable kernel has the squared Young bound for every measurable square-integrable input. -/
theorem real_convolution_l2_young {k f : ℝ → ℝ}
    (hk : Integrable k) (hf : AEStronglyMeasurable f volume)
    (hf2 : Integrable (fun y => f y ^ 2)) {B : ℝ}
    (hB : 0 ≤ B) (hkB : (∫ v, ‖k v‖) ≤ B) :
    (∫ y, (∫ v, k v * f (y - v)) ^ 2) ≤ B ^ 2 * ∫ y, f y ^ 2 := by
  have hfL : MemLp f 2 := (memLp_two_iff_integrable_sq hf).mpr hf2
  have h := convolution_memLp_two hk.ofReal (hfL.ofReal (K := ℂ))
  apply real_integral_bound hfL hB h.1
  apply h.2.trans
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by
    simpa using hkB)) le_rfl

/-- A real-valued complex Schwartz kernel gives an integrable square
and the real multiplier bound. -/
theorem real_schwartz_convolution_l2_multiplier_of_complex
    (k : SchwartzMap ℝ ℂ) {r f : ℝ → ℝ}
    (hk : ∀ v, k v = (r v : ℂ))
    (hf : AEStronglyMeasurable f volume) (hf2 : Integrable (fun y => f y ^ 2))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ ξ : ℝ, ‖𝓕 k ξ‖ ≤ B) :
    Integrable (fun y => (∫ v, r v * f (y - v)) ^ 2) ∧
      (∫ y, (∫ v, r v * f (y - v)) ^ 2) ≤ B ^ 2 * ∫ y, f y ^ 2 := by
  have hfL : MemLp f 2 := (memLp_two_iff_integrable_sq hf).mpr hf2
  have h := schwartz_convolution_l2_multiplier k (hfL.ofReal (K := ℂ)) hB hbound
  have he : (k : ℝ → ℂ) = fun v => (r v : ℂ) := funext hk
  rw [he] at h
  have hr : MemLp (fun y => ∫ v, r v * f (y - v)) 2 := by
    have hrC := h.1.re
    change MemLp (fun y => (conv (fun v => (r v : ℂ)) (fun v => (f v : ℂ)) y).re) 2 at hrC
    simpa only [real_convolution_identity, Complex.ofReal_re] using hrC
  exact ⟨hr.integrable_sq, real_integral_bound hfL hB h.1 h.2⟩

end D5.S3.Analytic.Fourier.ConvolutionL2
