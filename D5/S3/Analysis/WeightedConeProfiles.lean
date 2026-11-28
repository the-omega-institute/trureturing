/- GID: D5/S3/Analysis/WeightedConeProfiles
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-weak-boundary5-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted radial Fourier embeddings of separated interior cone profiles over compact angular spaces. -/

import OmegaBuild.Commands
import D5.S3.Analysis.FourierTestSeparation
import D5.S3.Analysis.AngularFourierPairing
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.Deriv.Support
import D5.S3.Analysis.LogarithmicFourierTail
import D5.S3.Analysis.ModularLogPairing
import D5.S3.Analysis.LogisticCoordinate

/-!
Omega original.

Weighted radial Fourier embeddings of separated interior cone profiles over compact angular spaces.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators FourierTransform Topology ENNReal NNReal InnerProductSpace

namespace Omega.ConeProfiles

variable {A : Type*} [MetricSpace A]

/-- A separated cone profile with smooth interior radial support and Lipschitz angular factor. -/
structure ConeProfileTerm (A : Type*) [MetricSpace A] where
  radial : ℝ → ℂ
  angular : A → ℂ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) radial
  compact : HasCompactSupport radial
  interior : tsupport radial ⊆ Ioo 0 1
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K angular

/-- A finite sum of separated cone profiles. -/
abbrev ConeProfile (A : Type*) [MetricSpace A] := List (ConeProfileTerm A)

/-- The affine radial value of the profile. -/
def profileValue (F : ConeProfile A) (u : ℝ) (n : A) : ℂ :=
  (F.map fun f => f.radial u * f.angular n).sum

/-- The affine radial derivative. -/
def profileDeriv (F : ConeProfile A) (u : ℝ) (n : A) : ℂ :=
  (F.map fun f => deriv f.radial u * f.angular n).sum

/-- The increasing affine coordinate on the interior of the cone. -/
def affineRadius : ℝ → ℝ := Omega.logistic (2 * Real.pi)

private theorem affineRadius_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) affineRadius := by
  unfold affineRadius Omega.logistic Real.sigmoid
  apply ContDiff.inv
  · exact contDiff_const.add (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).neg))
  · intro s
    positivity

private theorem affineRadius_compact (f : ConeProfileTerm A) :
    HasCompactSupport (f.radial ∘ affineRadius) := by
  have htop : Tendsto affineRadius atTop (𝓝 1) :=
    Real.tendsto_sigmoid_atTop.comp
      ((tendsto_const_mul_atTop_of_pos (by positivity : 0 < 2 * Real.pi)).2 tendsto_id)
  have hbot : Tendsto affineRadius atBot (𝓝 0) :=
    Real.tendsto_sigmoid_atBot.comp
      ((tendsto_const_mul_atBot_of_pos (by positivity : 0 < 2 * Real.pi)).2 tendsto_id)
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  change (∀ᶠ s in atBot ⊔ atTop, f.radial (affineRadius s) = 0)
  rw [Filter.eventually_sup]
  have hzero {x : ℝ} (hx : x ∉ Ioo (0 : ℝ) 1) :
      f.radial =ᶠ[𝓝 x] (0 : ℝ → ℂ) := by
    have he := (isClosed_tsupport (f := f.radial)).isOpen_compl.mem_nhds
      (show x ∉ tsupport f.radial from fun h => hx (f.interior h))
    filter_upwards [he] with y hy using image_eq_zero_of_notMem_tsupport hy
  exact ⟨(hzero (by simp : (0 : ℝ) ∉ Ioo 0 1)).comp_tendsto hbot,
    (hzero (by simp : (1 : ℝ) ∉ Ioo 0 1)).comp_tendsto htop⟩

def modularRadial (f : ConeProfileTerm A) : SchwartzMap ℝ ℂ :=
  (affineRadius_compact f).toSchwartzMap (f.smooth.comp affineRadius_smooth)

def frequencyScale : ℝ := 2 * Real.pi

theorem frequencyScale_pos : 0 < frequencyScale := by
  unfold frequencyScale
  positivity

def angularFourierRadial (f : ConeProfileTerm A) (ν : ℝ) : ℂ :=
  (Real.sqrt frequencyScale : ℂ)⁻¹ * 𝓕 (modularRadial f) (frequencyScale⁻¹ * ν)

section Weighted

variable (wgt : ℝ → ℝ) (hwgt : Measurable wgt)
  (wgt_bounds : ∀ ν, 2 ≤ wgt ν ∧ |ν| ≤ wgt ν ∧ wgt ν ≤ 2 + |ν|)

include hwgt in
private theorem weightedRadial_measurable (f : ConeProfileTerm A) :
    Measurable (fun ν => (Real.sqrt (wgt ν) : ℂ) * angularFourierRadial f ν) := by
  have hw := hwgt
  unfold angularFourierRadial
  have hs := (𝓕 (modularRadial f) : SchwartzMap ℝ ℂ).continuous.measurable
  fun_prop

include hwgt wgt_bounds in
private theorem angularFourierRadial_weighted_memLp (f : ConeProfileTerm A) :
    MemLp (fun ν => (Real.sqrt (wgt ν) : ℂ) * angularFourierRadial f ν) 2 volume := by
  let h : SchwartzMap ℝ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.smulOfNeZero ℝ ℝ frequencyScale⁻¹
        (inv_ne_zero frequencyScale_pos.ne')).toContinuousLinearEquiv) (𝓕 (modularRadial f))
  let B : ℝ := (Real.sqrt frequencyScale)⁻¹
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hh (ν : ℝ) : h ν = 𝓕 (modularRadial f) (frequencyScale⁻¹ * ν) := rfl
  have hm := weightedRadial_measurable wgt hwgt f
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
  have hp (k : ℕ) : Integrable (fun ν : ℝ => ‖ν‖ ^ k * ‖h ν‖ ^ 2) := by
    apply ((h.integrable_pow_mul volume k).const_mul (SchwartzMap.seminorm ℝ 0 0 h)).mono'
    · fun_prop
    · filter_upwards with ν
      rw [Real.norm_of_nonneg (by positivity), show ‖h ν‖ ^ 2 = ‖h ν‖ * ‖h ν‖ by ring]
      have hb := h.norm_le_seminorm ℝ ν
      calc
        _ ≤ ‖ν‖ ^ k * ‖h ν‖ * SchwartzMap.seminorm ℝ 0 0 h := by
          rw [mul_assoc]
          gcongr
        _ = _ := mul_comm _ _
  refine (((hp 0).const_mul 2).add (hp 1) |>.const_mul (B ^ 2)).mono'
    (hm.norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards with ν
  have hw : 0 ≤ wgt ν := by linarith [(wgt_bounds ν).1]
  simp only [angularFourierRadial, ← hh, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hw, pow_zero, one_mul, pow_one, Real.norm_of_nonneg (sq_nonneg _),
    abs_of_nonneg hw]
  change wgt ν * (B ^ 2 * ‖h ν‖ ^ 2) ≤ B ^ 2 * (2 * ‖h ν‖ ^ 2 + |ν| * ‖h ν‖ ^ 2)
  rw [← mul_assoc]
  calc
    wgt ν * B ^ 2 * ‖h ν‖ ^ 2 ≤ (2 + |ν|) * B ^ 2 * ‖h ν‖ ^ 2 := by
      gcongr
      exact (wgt_bounds ν).2.2
    _ = B ^ 2 * (2 * ‖h ν‖ ^ 2 + |ν| * ‖h ν‖ ^ 2) := by ring

variable [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
variable (sphereMeasure : Measure A) [IsFiniteMeasure sphereMeasure]

/-- The product of Lebesgue measure and the angular measure. -/
abbrev phaseMeasure := (volume : Measure ℝ).prod sphereMeasure

def termFrequency (f : ConeProfileTerm A) (p : (ℝ × A)) : ℂ :=
  ((Real.sqrt (wgt p.1) : ℂ) * angularFourierRadial f p.1) * f.angular p.2

include hwgt wgt_bounds in
theorem termFrequency_memLp (f : ConeProfileTerm A) :
    MemLp (termFrequency wgt f) 2 (phaseMeasure sphereMeasure) := by
  have hr := angularFourierRadial_weighted_memLp wgt hwgt wgt_bounds f
  have ha := f.lipschitz.choose_spec.continuous
  have ha₂ : Integrable (fun n => ‖f.angular n‖ ^ 2) sphereMeasure :=
    (ha.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hrad := weightedRadial_measurable wgt hwgt f
  have hi := ((memLp_two_iff_integrable_sq_norm hrad.aestronglyMeasurable).mp hr).mul_prod ha₂
  have hm : AEStronglyMeasurable (termFrequency wgt f) (phaseMeasure sphereMeasure) :=
    ((hrad.comp (measurable_fst : Measurable (Prod.fst : (ℝ × A) → ℝ))).mul
      (ha.measurable.comp measurable_snd)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  simpa only [termFrequency, norm_mul, mul_pow] using hi

/-- The weighted modular Fourier embedding into the given phase space. -/
def profileEmbed (F : ConeProfile A) : (Lp ℂ 2 (phaseMeasure sphereMeasure)) :=
  (F.map fun f => (termFrequency_memLp wgt hwgt wgt_bounds sphereMeasure f).toLp (termFrequency wgt f)).sum

private def modularCoordinate (u : ℝ) : ℝ :=
  Real.log (u / (1 - u)) / frequencyScale

private theorem affineRadius_mem (s : ℝ) : affineRadius s ∈ Ioo (0 : ℝ) 1 :=
  ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩

private theorem affineRadius_leftInverse (s : ℝ) :
    modularCoordinate (affineRadius s) = s := by
  have he : Real.exp (-(frequencyScale * s)) ≠ 0 := Real.exp_ne_zero _
  have hf : 1 + Real.exp (-(frequencyScale * s)) ≠ 0 := by positivity
  have hq : affineRadius s / (1 - affineRadius s) = Real.exp (frequencyScale * s) := by
    change (1 + Real.exp (-(frequencyScale * s)))⁻¹ /
      (1 - (1 + Real.exp (-(frequencyScale * s)))⁻¹) = _
    rw [show Real.exp (frequencyScale * s) = (Real.exp (-(frequencyScale * s)))⁻¹ by
      rw [← Real.exp_neg, neg_neg]]
    field_simp [he, hf]
    ring
  rw [modularCoordinate, hq, Real.log_exp]
  field_simp [frequencyScale_pos.ne']

private theorem affineRadius_rightInverse {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    affineRadius (modularCoordinate u) = u := by
  have h0 : 0 < u := hu.1
  have h1 : u < 1 := hu.2
  change Real.sigmoid (frequencyScale * (Real.log (u / (1-u)) / frequencyScale)) = _
  rw [mul_div_cancel₀ _ frequencyScale_pos.ne', Real.sigmoid, Real.exp_neg,
    Real.exp_log (by positivity : 0 < u / (1 - u))]
  have hd : 1 - u ≠ 0 := by linarith
  field_simp [h0.ne', hd]
  ring

private def affineTest (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Ioo (0 : ℝ) 1).indicator (g ∘ modularCoordinate) u

private theorem affineTest_support (g : ℝ → ℂ) (hg : HasCompactSupport g) :
    tsupport (affineTest g) ⊆ affineRadius '' tsupport g := by
  apply closure_minimal _ (hg.image affineRadius_smooth.continuous).isClosed
  intro u hu
  by_cases hi : u ∈ Ioo (0 : ℝ) 1
  · refine ⟨modularCoordinate u, subset_closure ?_, affineRadius_rightInverse hi⟩
    simpa [affineTest, hi] using hu
  · have hz : affineTest g u = 0 := by simp [affineTest, hi]
    exact (hu hz).elim

private theorem affineTest_smooth {g : ℝ → ℂ}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (affineTest g) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hi : u ∈ Ioo (0 : ℝ) 1
  · have h0 : 0 < u := hi.1
    have h1 : u < 1 := hi.2
    have hdiv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℝ => v / (1 - v)) u :=
      contDiffAt_id.div (contDiffAt_const.sub contDiffAt_id) (by linarith)
    have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) modularCoordinate u :=
      (hdiv.log (by positivity : u / (1 - u) ≠ 0)).div contDiffAt_const frequencyScale_pos.ne'
    refine (hg.contDiffAt.comp u hlog).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hi] with v hv
    simp [affineTest, hv]
  · have hn : u ∉ tsupport (affineTest g) := fun he => by
      obtain ⟨s, -, rfl⟩ := affineTest_support g hgc he
      exact hi (affineRadius_mem s)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport (f := affineTest g)).isOpen_compl.mem_nhds hn]
      with v hv using image_eq_zero_of_notMem_tsupport hv

private def separatedModular (g : ℝ → ℂ) (h : A → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hc : HasCompactSupport g)
    (hh : ∃ K : ℝ≥0, LipschitzWith K h) : (ConeProfileTerm A) where
  radial := affineTest g
  angular := h
  smooth := affineTest_smooth hg hc
  compact := by
    apply IsCompact.of_isClosed_subset
      (hc.image affineRadius_smooth.continuous)
      (isClosed_tsupport (affineTest g)) (affineTest_support g hc)
  interior := fun u hu => by
    obtain ⟨s, -, rfl⟩ := affineTest_support g hc hu
    exact affineRadius_mem s
  lipschitz := hh

private theorem modularRadial_separated (g : ℝ → ℂ) (h : A → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hc : HasCompactSupport g)
    (hh : ∃ K : ℝ≥0, LipschitzWith K h) :
    (modularRadial (separatedModular g h hg hc hh) : ℝ → ℂ) = g := by
  funext s
  change affineTest g (affineRadius s) = _
  rw [affineTest, indicator_of_mem (affineRadius_mem s), Function.comp_apply,
    affineRadius_leftInverse]


private theorem phase_slice_integrable (h : (Lp ℂ 2 (phaseMeasure sphereMeasure))) :
    ∀ᵐ ν : ℝ, Integrable (fun n => star (h (ν, n))) sphereMeasure := by
  have hm := (Lp.memLp h).aestronglyMeasurable
  have hi := (memLp_two_iff_integrable_sq_norm hm).mp (Lp.memLp h)
  have hs := hi.prod_right_ae
  have hmeas := hm.prodMk_left
  filter_upwards [hs, hmeas] with ν hn hmν
  have hLp : MemLp (fun n => h (ν, n)) 2 sphereMeasure :=
    (memLp_two_iff_integrable_sq_norm hmν).mpr hn
  exact Complex.conjCLE.toContinuousLinearMap.integrable_comp
    (memLp_one_iff_integrable.mp (hLp.mono_exponent (by norm_num)))

private def modularWeight (ν : ℝ) : ℂ :=
  (Real.sqrt (wgt ν) : ℂ) * (Real.sqrt frequencyScale : ℂ)⁻¹

private theorem separated_frequency (g : ℝ → ℂ) (b : A → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hc : HasCompactSupport g)
    (hb : ∃ K : ℝ≥0, LipschitzWith K b) (p : (ℝ × A)) :
    termFrequency wgt (separatedModular g b hg hc hb) p =
      modularWeight wgt p.1 * 𝓕 g (frequencyScale⁻¹ * p.1) * b p.2 := by
  unfold termFrequency angularFourierRadial modularWeight
  rw [SchwartzMap.fourier_coe, modularRadial_separated]
  change _ * b p.2 = _
  ring

private theorem separated_pairing (h : (Lp ℂ 2 (phaseMeasure sphereMeasure))) (g : ℝ → ℂ) (b : A → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hc : HasCompactSupport g)
    (hb : ∃ K : ℝ≥0, LipschitzWith K b) :
    let q := fun ν => (∫ n, star (h (ν, n)) * b n ∂sphereMeasure) *
      modularWeight wgt ν * 𝓕 g (frequencyScale⁻¹ * ν)
    Integrable q ∧
      (∫ ν, q ν) = ⟪h, profileEmbed wgt hwgt wgt_bounds sphereMeasure [separatedModular g b hg hc hb]⟫_ℂ := by
  let f := separatedModular g b hg hc hb
  let E := (termFrequency_memLp wgt hwgt wgt_bounds sphereMeasure f).toLp (termFrequency wgt f)
  have hcoe : (E : (ℝ × A) → ℂ) =ᵐ[(phaseMeasure sphereMeasure)] fun p =>
      modularWeight wgt p.1 * 𝓕 g (frequencyScale⁻¹ * p.1) * b p.2 :=
    (MemLp.coeFn_toLp _).trans (Eventually.of_forall (separated_frequency wgt g b hg hc hb))
  have heq : (fun p : (ℝ × A) => ⟪h p, E p⟫_ℂ) =ᵐ[(phaseMeasure sphereMeasure)] fun p =>
      (star (h p) * b p.2) * (modularWeight wgt p.1 * 𝓕 g (frequencyScale⁻¹ * p.1)) := by
    filter_upwards [hcoe] with p hp
    rw [RCLike.inner_apply, hp, Complex.star_def]
    ring
  have hi := (L2.integrable_inner h E).congr heq
  have hsec (ν : ℝ) :
      (∫ n, star (h (ν, n)) * b n * (modularWeight wgt ν * 𝓕 g (frequencyScale⁻¹ * ν))
        ∂sphereMeasure) = (∫ n, star (h (ν, n)) * b n ∂sphereMeasure) *
          modularWeight wgt ν * 𝓕 g (frequencyScale⁻¹ * ν) := by
    rw [integral_mul_const, mul_assoc]
  constructor
  · simpa only [hsec] using hi.integral_prod_left
  · have hE : profileEmbed wgt hwgt wgt_bounds sphereMeasure [f] = E := by simp [profileEmbed, E]
    rw [show profileEmbed wgt hwgt wgt_bounds sphereMeasure [separatedModular g b hg hc hb] = E from hE, L2.inner_def,
      integral_congr_ae heq]
    exact (integral_congr_ae (Eventually.of_forall fun ν => (hsec ν).symm)).trans
      (integral_prod _ hi).symm

private theorem profile_pairing_eq_zero {h : (Lp ℂ 2 (phaseMeasure sphereMeasure))}
    (hz : ∀ F : (ConeProfile A), ⟪h, profileEmbed wgt hwgt wgt_bounds sphereMeasure F⟫_ℂ = 0) : h = 0 := by
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let f : ℝ → ℂ := fun x => (χ x : ℂ)
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hfc : HasCompactSupport f := χ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hi : Integrable χ := χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport
  have h₀ : (∫ x, f x) ≠ 0 := by
    rw [integral_complex_ofReal]
    apply Complex.ofReal_ne_zero.mpr
    apply (integral_pos_of_integrable_nonneg_nonzero (x := (0 : ℝ)) χ.continuous hi
      (fun _ => χ.nonneg) ?_).ne'
    rw [χ.one_of_mem_closedBall (by simp : (0 : ℝ) ∈ Metric.closedBall 0 1)]
    exact one_ne_zero
  have hsmul (n : ℕ) :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ fun x : ℝ => ((n : ℝ) + 1) * x) :=
    hf.comp (contDiff_const.mul contDiff_id)
  have hcompact (n : ℕ) : HasCompactSupport (f ∘ fun x : ℝ => ((n : ℝ) + 1) * x) := by
    convert hfc.comp_smul (show (n : ℝ) + 1 ≠ 0 by positivity) using 1
    rfl
  have hweight : ∀ᵐ ν : ℝ, modularWeight wgt ν ≠ 0 := .of_forall fun ν => by
    have hw : 0 < wgt ν := by linarith [(wgt_bounds ν).1]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hw))
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr frequencyScale_pos)))
  have hstar : (fun p : (ℝ × A) => star (h p)) =ᵐ[(phaseMeasure sphereMeasure)] 0 := by
    apply Omega.ae_eq_zero_of_lipschitz_slice_pairing (Lp.aestronglyMeasurable h).star
      (phase_slice_integrable sphereMeasure h)
    intro b hb
    apply Omega.ae_eq_zero_of_weighted_fourier_pairing (inv_ne_zero frequencyScale_pos.ne')
      hweight (hf.continuous.integrable_of_hasCompactSupport hfc) h₀
    · intro n
      exact (separated_pairing wgt hwgt wgt_bounds sphereMeasure h _ b (hsmul n) (hcompact n) hb).1
    · intro n t
      have hs := (hsmul n).comp (contDiff_id.add (contDiff_const (c := t)))
      have hc := (hcompact n).comp_homeomorph (Homeomorph.addRight t)
      exact (separated_pairing wgt hwgt wgt_bounds sphereMeasure h _ b hs hc hb).2.trans (hz _)
  apply Lp.ext
  filter_upwards [hstar, Lp.coeFn_zero ℂ 2 (phaseMeasure sphereMeasure)] with p hp h0
  rw [h0, Pi.zero_apply]
  exact star_eq_zero.mp hp

private theorem profileEmbed_append (F G : ConeProfile A) :
    profileEmbed wgt hwgt wgt_bounds sphereMeasure (F ++ G) = profileEmbed wgt hwgt wgt_bounds sphereMeasure F + profileEmbed wgt hwgt wgt_bounds sphereMeasure G := by
  simp [profileEmbed]

private def ConeProfileTerm.scale (c : ℂ) (f : ConeProfileTerm A) : (ConeProfileTerm A) :=
  { f with angular := fun n => c * f.angular n
           lipschitz := by
             have hl : LipschitzWith ‖c‖₊ (fun z : ℂ => c * z) := by
               apply LipschitzWith.of_dist_le_mul
               intro x y
               rw [dist_eq_norm, ← mul_sub, norm_mul, dist_eq_norm]
               rfl
             exact ⟨_, hl.comp f.lipschitz.choose_spec⟩ }

private theorem profileEmbed_scale (c : ℂ) (F : ConeProfile A) :
    profileEmbed wgt hwgt wgt_bounds sphereMeasure (F.map (ConeProfileTerm.scale c)) = c • profileEmbed wgt hwgt wgt_bounds sphereMeasure F := by
  induction F with
  | nil => simp [profileEmbed]
  | cons f F ih =>
    have he :
        (termFrequency_memLp wgt hwgt wgt_bounds sphereMeasure (f.scale c)).toLp _ =
          c • (termFrequency_memLp wgt hwgt wgt_bounds sphereMeasure f).toLp (termFrequency wgt f) := by
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (termFrequency_memLp wgt hwgt wgt_bounds sphereMeasure (f.scale c)),
        Lp.coeFn_smul c ((termFrequency_memLp wgt hwgt wgt_bounds sphereMeasure f).toLp (termFrequency wgt f)),
        MemLp.coeFn_toLp (termFrequency_memLp wgt hwgt wgt_bounds sphereMeasure f)] with p h1 h2 h3
      rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
      have hr : angularFourierRadial (f.scale c) = angularFourierRadial f := rfl
      simp only [termFrequency, hr]
      change (_ * (c * f.angular p.2)) = c * (_ * f.angular p.2)
      ring
    simp only [List.map_cons, profileEmbed, List.sum_cons] at ih ⊢
    simpa only [smul_add, he] using congrArg
      (fun v => c • (termFrequency_memLp wgt hwgt wgt_bounds sphereMeasure f).toLp (termFrequency wgt f) + v) ih

/-- Compact separated cone profiles span a dense subspace of the phase Hilbert space. -/
theorem profileEmbed_dense : DenseRange (profileEmbed wgt hwgt wgt_bounds sphereMeasure) := by
  let V : Submodule ℂ (Lp ℂ 2 (phaseMeasure sphereMeasure)) :=
    { carrier := range (profileEmbed wgt hwgt wgt_bounds sphereMeasure)
      zero_mem' := ⟨[], by simp [profileEmbed]⟩
      add_mem' := by rintro _ _ ⟨F, rfl⟩ ⟨G, rfl⟩; exact ⟨F ++ G, profileEmbed_append wgt hwgt wgt_bounds sphereMeasure F G⟩
      smul_mem' := by rintro c _ ⟨F, rfl⟩; exact ⟨_, profileEmbed_scale wgt hwgt wgt_bounds sphereMeasure c F⟩ }
  have hz : Vᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro h hh
    rw [Submodule.mem_bot]
    apply profile_pairing_eq_zero wgt hwgt wgt_bounds sphereMeasure
    intro F
    exact (Submodule.mem_orthogonal' _ _).mp hh _ ⟨F, rfl⟩
  have hc : V.topologicalClosure = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp ((Submodule.orthogonal_closure V).trans hz)
  exact dense_iff_closure_eq.mpr (congrArg SetLike.coe hc)


/-- The unitary angular-frequency transform before multiplication by the square root of the weight. -/
def profileFourier (F : ConeProfile A) (p : (ℝ × A)) : ℂ :=
  (F.map fun f => angularFourierRadial f p.1 * f.angular p.2).sum

theorem profileEmbed_ae (F : ConeProfile A) :
    (profileEmbed wgt hwgt wgt_bounds sphereMeasure F : (ℝ × A) → ℂ) =ᵐ[(phaseMeasure sphereMeasure)]
      fun p => (Real.sqrt (wgt p.1) : ℂ) * profileFourier F p := by
  induction F with
  | nil =>
    filter_upwards [Lp.coeFn_zero ℂ 2 (phaseMeasure sphereMeasure)] with p hp
    simpa only [profileEmbed, profileFourier, List.map_nil, List.sum_nil, mul_zero,
      Pi.zero_apply] using hp
  | cons f F ih =>
    let e := (termFrequency_memLp wgt hwgt wgt_bounds sphereMeasure f).toLp (termFrequency wgt f)
    change ((e + profileEmbed wgt hwgt wgt_bounds sphereMeasure F : (Lp ℂ 2 (phaseMeasure sphereMeasure))) : (ℝ × A) → ℂ) =ᵐ[(phaseMeasure sphereMeasure)] _
    filter_upwards [Lp.coeFn_add e (profileEmbed wgt hwgt wgt_bounds sphereMeasure F), MemLp.coeFn_toLp (termFrequency_memLp wgt hwgt wgt_bounds sphereMeasure f),
      ih] with p hp he hf
    rw [hp, Pi.add_apply, he, hf]
    simp [profileFourier, termFrequency, ← mul_assoc, mul_add]

end Weighted

def modularProfile (F : ConeProfile A) (n : A) : SchwartzMap ℝ ℂ :=
  (F.map fun f => f.angular n • modularRadial f).sum

theorem modularProfile_compact (F : ConeProfile A) (n : A) :
    HasCompactSupport (modularProfile F n) := by
  induction F with
  | nil => exact HasCompactSupport.zero
  | cons f F ih =>
    change HasCompactSupport (fun s : ℝ =>
      f.angular n * modularRadial f s + modularProfile F n s)
    exact ((affineRadius_compact f).mul_left (f := fun _ => f.angular n)).add ih

theorem profileFourier_modular (F : ConeProfile A) (ν : ℝ) (n : A) :
    profileFourier F (ν, n) =
      (Real.sqrt frequencyScale : ℂ)⁻¹ *
        𝓕 (modularProfile F n) (frequencyScale⁻¹ * ν) := by
  induction F with
  | nil => simp [profileFourier, modularProfile]
  | cons f F ih =>
    change angularFourierRadial f ν * f.angular n + profileFourier F (ν, n) =
      _ * 𝓕 (f.angular n • modularRadial f + modularProfile F n) (frequencyScale⁻¹ * ν)
    rw [ih, FourierTransform.fourier_add, FourierTransform.fourier_smul]
    simp only [angularFourierRadial, add_apply, smul_apply, smul_eq_mul]
    ring

/-- The modular test is the affine profile evaluated at the logistic radius. -/
theorem modularProfile_apply (F : ConeProfile A) (n : A) (s : ℝ) :
    modularProfile F n s = profileValue F (affineRadius s) n := by
  induction F with
  | nil => rfl
  | cons f F ih =>
    change f.angular n * f.radial (affineRadius s) + modularProfile F n s =
      f.radial (affineRadius s) * f.angular n + profileValue F (affineRadius s) n
    rw [ih, mul_comm (f.angular n)]

theorem profileValue_hasDerivAt (F : ConeProfile A) (u : ℝ) (n : A) :
    HasDerivAt (fun v => profileValue F v n) (profileDeriv F u n) u := by
  induction F with
  | nil => exact hasDerivAt_const u 0
  | cons f F ih =>
    exact (((f.smooth.differentiable (by simp) u).hasDerivAt).mul_const (f.angular n)).add ih


theorem profileDeriv_continuous (F : (ConeProfile A)) :
    Continuous (fun p : (ℝ × A) => profileDeriv F p.1 p.2) := by
  induction F with
  | nil => simpa [profileDeriv] using continuous_const (y := (0 : ℂ))
  | cons f F ih =>
    have hr : Continuous (deriv f.radial) :=
      f.smooth.continuous_deriv (by exact_mod_cast le_top)
    exact ((hr.comp continuous_fst).mul
      (f.lipschitz.choose_spec.continuous.comp continuous_snd)).add ih

theorem profileDeriv_zero_near_origin (F : (ConeProfile A)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ, 0 < u → u ≤ δ →
      ∀ n : A, profileDeriv F u n = 0 := by
  have h : ∀ᶠ u : ℝ in 𝓝 0, ∀ n : A, profileDeriv F u n = 0 := by
    induction F with
    | nil => exact .of_forall fun u n => by simp [profileDeriv]
    | cons f F ih =>
      have h₀ : (0 : ℝ) ∉ tsupport f.radial := fun h => by simpa using f.interior h
      have h₁ := (isClosed_tsupport f.radial).isOpen_compl.mem_nhds h₀
      filter_upwards [h₁, ih] with u hu hf n
      have hd : deriv f.radial u = 0 :=
        image_eq_zero_of_notMem_tsupport fun hd => hu (tsupport_deriv_subset hd)
      change deriv f.radial u * f.angular n + profileDeriv F u n = 0
      rw [hd, hf n, zero_mul, zero_add]
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨δ / 2, by positivity, fun u hu hu' n => ?_⟩
  have hm : u ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hu.le] using (show u < δ by linarith)
  exact hb hm n

theorem profileValue_smooth_support (F : (ConeProfile A)) (n : A) :
    ContDiff ℝ 1 (fun u => profileValue F u n) ∧
    tsupport (fun u => profileValue F u n) ⊆ Ioo 0 1 := by
  induction F with
  | nil =>
    simp [profileValue, contDiff_const]
  | cons f F ih =>
    change ContDiff ℝ 1 (fun u => f.radial u * f.angular n + profileValue F u n) ∧ _
    refine ⟨((f.smooth.of_le (by simp)).mul contDiff_const).add ih.1, ?_⟩
    exact (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_left.trans f.interior) ih.2)


theorem modularProfile_deriv_chain (F : (ConeProfile A)) (n : A) (s : ℝ) :
    deriv (modularProfile F n) s =
      ((2 * Real.pi * (affineRadius s * (1 - affineRadius s)) : ℝ) : ℂ) *
        profileDeriv F (affineRadius s) n := by
  have hd := (profileValue_hasDerivAt F (affineRadius s) n).scomp s
    (Omega.hasDerivAt_logistic (2 * Real.pi) s)
  have hfun : (modularProfile F n : ℝ → ℂ) = (fun u => profileValue F u n) ∘ affineRadius :=
    funext (modularProfile_apply F n)
  rw [hfun]
  simpa only [affineRadius, Complex.real_smul] using hd.deriv

theorem profileFourier_bounded_continuous [CompactSpace A] (F : (ConeProfile A)) :
    Continuous (profileFourier F) ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖profileFourier F p‖ ≤ B := by
  change Continuous (fun p : (ℝ × A) => profileFourier F (p.1, p.2)) ∧ _
  unfold profileFourier
  apply Omega.continuous_bounded_listSum
  intro f
  change Continuous (fun p : (ℝ × A) => (Real.sqrt frequencyScale : ℂ)⁻¹ *
    (𝓕 (_ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) (frequencyScale⁻¹ * p.1) * f.angular p.2) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : (ℝ × A), ‖(Real.sqrt frequencyScale : ℂ)⁻¹ *
      (𝓕 (_ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) (frequencyScale⁻¹ * p.1) * f.angular p.2‖ ≤ B
  exact Omega.bounded_continuous_separated_fourier _ _ f.lipschitz.choose_spec.continuous _ _

end Omega.ConeProfiles
