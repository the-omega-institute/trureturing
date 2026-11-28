/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact cone profiles and their weighted modular Fourier representation. -/

import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondSphere4D
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondMultipliers4D
import D5.S3.Analytic.CothBernoulliDegree.PartialFraction
import D5.S3.Analytic.PetzCothStripMode
import D5.S3.Analysis.FourierTestSeparation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.Deriv.Support
import D5.S3.Analysis.LogarithmicFourierTail
import D5.S3.Analysis.ModularLogPairing
import D5.S3.Analysis.LogisticCoordinate

/-! Compactly supported cone profiles and the angular-frequency transform. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators FourierTransform Topology ENNReal NNReal InnerProductSpace

namespace NullConeGravity

/-- A separated cone profile with smooth interior radial support and Lipschitz angular factor. -/
structure ConeProfileTerm where
  radial : ℝ → ℂ
  angular : Sphere4D → ℂ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) radial
  compact : HasCompactSupport radial
  interior : tsupport radial ⊆ Ioo 0 1
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K angular

/-- A finite sum of separated cone profiles. -/
abbrev ConeProfile := List ConeProfileTerm

/-- The affine radial value of the profile. -/
def profileValue (F : ConeProfile) (u : ℝ) (n : Sphere4D) : ℂ :=
  (F.map fun f => f.radial u * f.angular n).sum

/-- The affine radial derivative. -/
def profileDeriv (F : ConeProfile) (u : ℝ) (n : Sphere4D) : ℂ :=
  (F.map fun f => deriv f.radial u * f.angular n).sum

/-- The increasing affine coordinate on the interior of the cone. -/
def affineRadius : ℝ → ℝ := Omega.logistic (2 * Real.pi)

private theorem affineRadius_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) affineRadius := by
  unfold affineRadius Omega.logistic Real.sigmoid
  apply ContDiff.inv
  · exact contDiff_const.add (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).neg))
  · intro s
    positivity

private theorem affineRadius_compact (f : ConeProfileTerm) :
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

private def modularRadial (f : ConeProfileTerm) : SchwartzMap ℝ ℂ :=
  (affineRadius_compact f).toSchwartzMap (f.smooth.comp affineRadius_smooth)

private def frequencyScale : ℝ := 2 * Real.pi

private theorem frequencyScale_pos : 0 < frequencyScale := by
  unfold frequencyScale
  positivity

private def angularFourierRadial (f : ConeProfileTerm) (ν : ℝ) : ℂ :=
  (Real.sqrt frequencyScale : ℂ)⁻¹ * 𝓕 (modularRadial f) (frequencyScale⁻¹ * ν)

private theorem wgt_measurable_profile : Measurable wgt := by
  unfold wgt
  exact Measurable.ite (measurableSet_singleton _) measurable_const (by fun_prop)

private theorem weightedRadial_measurable (f : ConeProfileTerm) :
    Measurable (fun ν => (Real.sqrt (wgt ν) : ℂ) * angularFourierRadial f ν) := by
  have hw := wgt_measurable_profile
  unfold angularFourierRadial
  have hs := (𝓕 (modularRadial f) : SchwartzMap ℝ ℂ).continuous.measurable
  fun_prop

private theorem angularFourierRadial_weighted_memLp (f : ConeProfileTerm) :
    MemLp (fun ν => (Real.sqrt (wgt ν) : ℂ) * angularFourierRadial f ν) 2 volume := by
  let h : SchwartzMap ℝ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.smulOfNeZero ℝ ℝ frequencyScale⁻¹
        (inv_ne_zero frequencyScale_pos.ne')).toContinuousLinearEquiv) (𝓕 (modularRadial f))
  let B : ℝ := (Real.sqrt frequencyScale)⁻¹
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hh (ν : ℝ) : h ν = 𝓕 (modularRadial f) (frequencyScale⁻¹ * ν) := rfl
  have hm := weightedRadial_measurable f
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

private def termFrequency (f : ConeProfileTerm) (p : Phase4D) : ℂ :=
  ((Real.sqrt (wgt p.1) : ℂ) * angularFourierRadial f p.1) * f.angular p.2

private theorem termFrequency_memLp (f : ConeProfileTerm) :
    MemLp (termFrequency f) 2 phaseMeasure := by
  have hr := angularFourierRadial_weighted_memLp f
  have ha := f.lipschitz.choose_spec.continuous
  have ha₂ : Integrable (fun n => ‖f.angular n‖ ^ 2) sphereMeasure :=
    (ha.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hrad := weightedRadial_measurable f
  have hi := ((memLp_two_iff_integrable_sq_norm hrad.aestronglyMeasurable).mp hr).mul_prod ha₂
  have hm : AEStronglyMeasurable (termFrequency f) phaseMeasure :=
    ((hrad.comp (measurable_fst : Measurable (Prod.fst : Phase4D → ℝ))).mul
      (ha.measurable.comp measurable_snd)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  simpa only [termFrequency, phaseMeasure, norm_mul, mul_pow] using hi

/-- The weighted modular Fourier embedding into the given phase space. -/
def profileEmbed (F : ConeProfile) : H4D :=
  (F.map fun f => (termFrequency_memLp f).toLp (termFrequency f)).sum

private theorem coth_even (ν : ℝ) : wgt (-ν) = wgt ν := by
  simp [wgt, neg_div, Real.cosh_neg, Real.sinh_neg, div_neg]

open D5.S3.Analytic.CothBernoulliDegree.Defs in
private theorem coth_series_nonneg (ν : ℝ) (hν : 0 ≤ ν) :
    2 + 4 * ν ^ 2 * (∑' k : ℕ, 1 / ((2 * Real.pi * ((k : ℝ) + 1)) ^ 2 + ν ^ 2)) = wgt ν := by
  rcases hν.eq_or_lt with h | h
  · simp [← h, wgt]
  let x := ν / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hh :
      Real.cosh x / Real.sinh x / x - x ^ (-2 : ℤ) =
        2 * ∑' k : ℕ, 1 / (x ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2) := by
    simpa [P, p, Finset.sum_range_one] using
      D5.S3.Analytic.CothBernoulliDegree.PartialFraction.P_eq_tsum 0 0 hx
  have he (k : ℕ) : 1 / ((2 * Real.pi * ((k : ℝ) + 1)) ^ 2 + ν ^ 2) =
      (1 / 4 : ℝ) * (1 / (x ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2)) := by
    rw [show (2 * Real.pi * ((k : ℝ) + 1)) ^ 2 + ν ^ 2 =
      4 * (x ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2) by dsimp [x]; ring]
    rw [one_div, mul_inv]
    simp [one_div]
  simp_rw [he]
  rw [tsum_mul_left, ← mul_assoc, show 4 * ν ^ 2 * (1 / 4) = ν ^ 2 by ring,
    show ν ^ 2 = 2 * x ^ 2 * 2 by dsimp [x]; ring, mul_assoc, ← hh]
  rw [wgt, ite_eq_right h.ne']
  change _ = ν * Real.cosh x / Real.sinh x
  have hs := (Real.sinh_pos_iff.mpr hx).ne'
  simp only [zpow_neg, zpow_ofNat]
  field_simp [hx.ne', hs]
  dsimp [x]
  ring

private theorem weight_sub_eq (ν : ℝ) : wgt ν - ν = wgt ν * a ν := by
  by_cases hν : ν = 0
  · subst ν
    norm_num [wgt, a]
  have hs : Real.sinh (ν / 2) ≠ 0 := by simpa using hν
  simp only [wgt, ite_eq_right hν, a]
  have he : Real.exp (ν / 2) = Real.exp ν * Real.exp (-(ν / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  field_simp [hs, show 1 + Real.exp ν ≠ 0 by positivity]
  rw [Real.cosh_eq, Real.sinh_eq, he]
  ring

/-- The exponential terms of the symmetric logarithmic kernel and the oriented sign
term give the scalar series with its zero-frequency value. -/
theorem profile_log_series_symbol (ν : ℝ) :
    2 + 4 * ν ^ 2 * (∑' k : ℕ, 1 / ((2 * Real.pi * ((k : ℝ) + 1)) ^ 2 + ν ^ 2)) - ν =
      wgt ν * a ν := by
  rw [← weight_sub_eq]
  congr 1
  rcases le_total 0 ν with hν | hν
  · exact coth_series_nonneg ν hν
  · simpa only [neg_sq, coth_even] using coth_series_nonneg (-ν) (neg_nonneg.mpr hν)


/-- Fourier identification of the decaying part of the logarithmic kernel,
with the linear-distance and oriented sign contributions included in the symbol. -/
theorem profile_log_fourier_symbol (ν : ℝ) :
    2 + (ν ^ 2 / Real.pi) *
      (∫ s : ℝ, Complex.exp (-Complex.I * (ν : ℂ) * s) * Omega.logTail s).re - ν =
      wgt ν * a ν := by
  rw [Omega.logarithmic_mode_integral, ← Complex.ofReal_tsum]
  simp only [Complex.ofReal_re]
  have he (k : ℕ) : 4 * Real.pi / ((2 * Real.pi * ((k : ℝ) + 1)) ^ 2 + ν ^ 2) =
      (4 * Real.pi) * (1 / ((2 * Real.pi * ((k : ℝ) + 1)) ^ 2 + ν ^ 2)) := by ring
  simp_rw [he, tsum_mul_left]
  rw [← profile_log_series_symbol, ← mul_assoc (ν ^ 2 / Real.pi),
    show ν ^ 2 / Real.pi * (4 * Real.pi) = 4 * ν ^ 2 by field_simp [Real.pi_ne_zero]]


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

private def separatedModular (g : ℝ → ℂ) (h : Sphere4D → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hc : HasCompactSupport g)
    (hh : ∃ K : ℝ≥0, LipschitzWith K h) : ConeProfileTerm where
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

private theorem modularRadial_separated (g : ℝ → ℂ) (h : Sphere4D → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hc : HasCompactSupport g)
    (hh : ∃ K : ℝ≥0, LipschitzWith K h) :
    (modularRadial (separatedModular g h hg hc hh) : ℝ → ℂ) = g := by
  funext s
  change affineTest g (affineRadius s) = _
  rw [affineTest, indicator_of_mem (affineRadius_mem s), Function.comp_apply,
    affineRadius_leftInverse]


private local instance : SFinite phaseMeasure := by unfold phaseMeasure; infer_instance

private theorem phase_slice_integrable (h : H4D) :
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

private theorem separated_frequency (g : ℝ → ℂ) (b : Sphere4D → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hc : HasCompactSupport g)
    (hb : ∃ K : ℝ≥0, LipschitzWith K b) (p : Phase4D) :
    termFrequency (separatedModular g b hg hc hb) p =
      modularWeight p.1 * 𝓕 g (frequencyScale⁻¹ * p.1) * b p.2 := by
  unfold termFrequency angularFourierRadial modularWeight
  rw [SchwartzMap.fourier_coe, modularRadial_separated]
  change _ * b p.2 = _
  ring

private theorem separated_pairing (h : H4D) (g : ℝ → ℂ) (b : Sphere4D → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hc : HasCompactSupport g)
    (hb : ∃ K : ℝ≥0, LipschitzWith K b) :
    let q := fun ν => (∫ n, star (h (ν, n)) * b n ∂sphereMeasure) *
      modularWeight ν * 𝓕 g (frequencyScale⁻¹ * ν)
    Integrable q ∧
      (∫ ν, q ν) = ⟪h, profileEmbed [separatedModular g b hg hc hb]⟫_ℂ := by
  let f := separatedModular g b hg hc hb
  let E := (termFrequency_memLp f).toLp (termFrequency f)
  have hcoe : (E : Phase4D → ℂ) =ᵐ[phaseMeasure] fun p =>
      modularWeight p.1 * 𝓕 g (frequencyScale⁻¹ * p.1) * b p.2 :=
    (MemLp.coeFn_toLp _).trans (Eventually.of_forall (separated_frequency g b hg hc hb))
  have heq : (fun p : Phase4D => ⟪h p, E p⟫_ℂ) =ᵐ[phaseMeasure] fun p =>
      (star (h p) * b p.2) * (modularWeight p.1 * 𝓕 g (frequencyScale⁻¹ * p.1)) := by
    filter_upwards [hcoe] with p hp
    rw [RCLike.inner_apply, hp, Complex.star_def]
    ring
  have hi := (L2.integrable_inner h E).congr heq
  have hsec (ν : ℝ) :
      (∫ n, star (h (ν, n)) * b n * (modularWeight ν * 𝓕 g (frequencyScale⁻¹ * ν))
        ∂sphereMeasure) = (∫ n, star (h (ν, n)) * b n ∂sphereMeasure) *
          modularWeight ν * 𝓕 g (frequencyScale⁻¹ * ν) := by
    rw [integral_mul_const, mul_assoc]
  constructor
  · simpa only [hsec] using hi.integral_prod_left
  · have hE : profileEmbed [f] = E := by simp [profileEmbed, E]
    rw [show profileEmbed [separatedModular g b hg hc hb] = E from hE, L2.inner_def,
      integral_congr_ae heq]
    exact (integral_congr_ae (Eventually.of_forall fun ν => (hsec ν).symm)).trans
      (integral_prod _ hi).symm

private theorem profile_pairing_eq_zero {h : H4D}
    (hz : ∀ F : ConeProfile, ⟪h, profileEmbed F⟫_ℂ = 0) : h = 0 := by
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
  have hweight : ∀ᵐ ν : ℝ, modularWeight ν ≠ 0 := .of_forall fun ν => by
    have hw : 0 < wgt ν := by linarith [(wgt_bounds ν).1]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hw))
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr frequencyScale_pos)))
  have hstar : (fun p : Phase4D => star (h p)) =ᵐ[phaseMeasure] 0 := by
    apply Omega.ae_eq_zero_of_lipschitz_slice_pairing (Lp.aestronglyMeasurable h).star
      (phase_slice_integrable h)
    intro b hb
    apply Omega.ae_eq_zero_of_weighted_fourier_pairing (inv_ne_zero frequencyScale_pos.ne')
      hweight (hf.continuous.integrable_of_hasCompactSupport hfc) h₀
    · intro n
      exact (separated_pairing h _ b (hsmul n) (hcompact n) hb).1
    · intro n t
      have hs := (hsmul n).comp (contDiff_id.add (contDiff_const (c := t)))
      have hc := (hcompact n).comp_homeomorph (Homeomorph.addRight t)
      exact (separated_pairing h _ b hs hc hb).2.trans (hz _)
  apply Lp.ext
  filter_upwards [hstar, Lp.coeFn_zero ℂ 2 phaseMeasure] with p hp h0
  rw [h0, Pi.zero_apply]
  exact star_eq_zero.mp hp

private theorem profileEmbed_append (F G : ConeProfile) :
    profileEmbed (F ++ G) = profileEmbed F + profileEmbed G := by
  simp [profileEmbed]

private def ConeProfileTerm.scale (c : ℂ) (f : ConeProfileTerm) : ConeProfileTerm :=
  { f with angular := fun n => c * f.angular n
           lipschitz := by
             have hl : LipschitzWith ‖c‖₊ (fun z : ℂ => c * z) := by
               apply LipschitzWith.of_dist_le_mul
               intro x y
               rw [dist_eq_norm, ← mul_sub, norm_mul, dist_eq_norm]
               rfl
             exact ⟨_, hl.comp f.lipschitz.choose_spec⟩ }

private theorem profileEmbed_scale (c : ℂ) (F : ConeProfile) :
    profileEmbed (F.map (ConeProfileTerm.scale c)) = c • profileEmbed F := by
  induction F with
  | nil => simp [profileEmbed]
  | cons f F ih =>
    have he :
        (termFrequency_memLp (f.scale c)).toLp _ =
          c • (termFrequency_memLp f).toLp (termFrequency f) := by
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (termFrequency_memLp (f.scale c)),
        Lp.coeFn_smul c ((termFrequency_memLp f).toLp (termFrequency f)),
        MemLp.coeFn_toLp (termFrequency_memLp f)] with p h1 h2 h3
      rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
      have hr : angularFourierRadial (f.scale c) = angularFourierRadial f := rfl
      simp only [termFrequency, hr]
      change (_ * (c * f.angular p.2)) = c * (_ * f.angular p.2)
      ring
    simp only [List.map_cons, profileEmbed, List.sum_cons] at ih ⊢
    simpa only [smul_add, he] using congrArg
      (fun v => c • (termFrequency_memLp f).toLp (termFrequency f) + v) ih

/-- Compact separated cone profiles span a dense subspace of the phase Hilbert space. -/
theorem profileEmbed_dense : DenseRange profileEmbed := by
  let V : Submodule ℂ H4D :=
    { carrier := range profileEmbed
      zero_mem' := ⟨[], by simp [profileEmbed]⟩
      add_mem' := by rintro _ _ ⟨F, rfl⟩ ⟨G, rfl⟩; exact ⟨F ++ G, profileEmbed_append F G⟩
      smul_mem' := by rintro c _ ⟨F, rfl⟩; exact ⟨_, profileEmbed_scale c F⟩ }
  have hz : Vᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro h hh
    rw [Submodule.mem_bot]
    apply profile_pairing_eq_zero
    intro F
    exact (Submodule.mem_orthogonal' _ _).mp hh _ ⟨F, rfl⟩
  have hc : V.topologicalClosure = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp ((Submodule.orthogonal_closure V).trans hz)
  exact dense_iff_closure_eq.mpr (congrArg SetLike.coe hc)


/-- The unitary angular-frequency transform before multiplication by the square root of the weight. -/
def profileFourier (F : ConeProfile) (p : Phase4D) : ℂ :=
  (F.map fun f => angularFourierRadial f p.1 * f.angular p.2).sum

private theorem profileEmbed_ae (F : ConeProfile) :
    (profileEmbed F : Phase4D → ℂ) =ᵐ[phaseMeasure]
      fun p => (Real.sqrt (wgt p.1) : ℂ) * profileFourier F p := by
  induction F with
  | nil =>
    filter_upwards [Lp.coeFn_zero ℂ 2 phaseMeasure] with p hp
    simpa only [profileEmbed, profileFourier, List.map_nil, List.sum_nil, mul_zero,
      Pi.zero_apply] using hp
  | cons f F ih =>
    let e := (termFrequency_memLp f).toLp (termFrequency f)
    change ((e + profileEmbed F : H4D) : Phase4D → ℂ) =ᵐ[phaseMeasure] _
    filter_upwards [Lp.coeFn_add e (profileEmbed F), MemLp.coeFn_toLp (termFrequency_memLp f),
      ih] with p hp he hf
    rw [hp, Pi.add_apply, he, hf]
    simp [profileFourier, termFrequency, ← mul_assoc, mul_add]

private theorem profile_massless_pairing_ae (F : ConeProfile) :
    (fun p : Phase4D => ⟪profileEmbed F p, nullA (profileEmbed F) p⟫_ℂ) =ᵐ[phaseMeasure]
      fun p => ((wgt p.1 - p.1 : ℝ) : ℂ) * (‖profileFourier F p‖ ^ 2 : ℝ) := by
  let f := profileEmbed F
  have hA : (nullA f : Phase4D → ℂ) =ᵐ[phaseMeasure]
      fun p => ((a p.1 : ℝ) : ℂ) * f p := by
    unfold nullA
    refine (mulOp_ae phaseMeasure _ _ f).trans ?_
    exact Eventually.of_forall fun p => by
      change (↑(a p.1 ^ (1 : ℝ)) : ℂ) * f p = _
      rw [Real.rpow_one]
  have hF := profileEmbed_ae F
  filter_upwards [hA, hF] with p hp hf
  rw [RCLike.inner_apply, hp]
  change (a p.1 : ℂ) * f p * star (f p) = _
  rw [hf, mul_assoc, Complex.star_def, Complex.mul_conj, ← Complex.sq_norm,
    norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by linarith [(wgt_bounds p.1).1]), weight_sub_eq]
  push_cast
  ring


/-- The multiplier of the massless operator pairing in unweighted Fourier coordinates. -/
theorem profile_nullA_pairing (F : ConeProfile) :
    ⟪profileEmbed F, nullA (profileEmbed F)⟫_ℂ =
      ∫ p, ((wgt p.1 - p.1 : ℝ) : ℂ) * (‖profileFourier F p‖ ^ 2 : ℝ) ∂phaseMeasure := by
  rw [L2.inner_def]
  exact integral_congr_ae (profile_massless_pairing_ae F)

/-- The compact Schwartz test along one angular direction in modular coordinates. -/
def modularProfile (F : ConeProfile) (n : Sphere4D) : SchwartzMap ℝ ℂ :=
  (F.map fun f => f.angular n • modularRadial f).sum

theorem modularProfile_compact (F : ConeProfile) (n : Sphere4D) :
    HasCompactSupport (modularProfile F n) := by
  induction F with
  | nil => exact HasCompactSupport.zero
  | cons f F ih =>
    change HasCompactSupport (fun s : ℝ =>
      f.angular n * modularRadial f s + modularProfile F n s)
    exact ((affineRadius_compact f).mul_left (f := fun _ => f.angular n)).add ih

theorem profileFourier_modular (F : ConeProfile) (ν : ℝ) (n : Sphere4D) :
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

private theorem radial_symbol (ξ : ℝ) :
    2 + (frequencyScale * ξ) ^ 2 / Real.pi * (𝓕 Omega.logTail ξ).re - frequencyScale * ξ =
      wgt (frequencyScale * ξ) - frequencyScale * ξ := by
  have he : 𝓕 Omega.logTail ξ =
      ∫ s : ℝ, Complex.exp (-Complex.I * ((frequencyScale * ξ : ℝ) : ℂ) * s) *
        Omega.logTail s := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with s
    rw [smul_eq_mul]
    unfold frequencyScale
    push_cast
    congr 2
    ring
  rw [he, profile_log_fourier_symbol, ← weight_sub_eq]

/-- The quadratic logarithmic form in the modular radial variable equals the
spectral pairing against the massless multiplier on the given phase space. -/
theorem profile_modular_log_pairing (F : ConeProfile) :
    (∫ n : Sphere4D, Omega.modularLogPairing (modularProfile F n) (modularProfile F n)
      ∂sphereMeasure) = ⟪profileEmbed F, nullA (profileEmbed F)⟫_ℂ := by
  let P : Phase4D → ℂ := fun p =>
    ((wgt p.1 - p.1 : ℝ) : ℂ) * (‖profileFourier F p‖ ^ 2 : ℝ)
  have hi : Integrable P phaseMeasure := (L2.integrable_inner (profileEmbed F)
    (nullA (profileEmbed F))).congr (profile_massless_pairing_ae F)
  rw [profile_nullA_pairing F]
  change _ = ∫ p, P p ∂phaseMeasure
  have hprod := integral_prod_symm P hi
  refine Eq.trans ?_ hprod.symm
  apply integral_congr_ae
  filter_upwards with n
  rw [Omega.modularLogPairing_eq_fourier _ _ (modularProfile_compact F n)
    (modularProfile_compact F n)]
  have hscale := Measure.integral_comp_mul_left (fun ν => P (ν, n)) frequencyScale
  rw [abs_of_nonneg (inv_nonneg.mpr frequencyScale_pos.le)] at hscale
  rw [← inv_smul_smul₀ (inv_ne_zero frequencyScale_pos.ne') (∫ ν, P (ν, n)), ← hscale,
    inv_inv, Complex.real_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [show 2 * Real.pi * ξ = frequencyScale * ξ from rfl, radial_symbol]
  dsimp only [P]
  rw [profileFourier_modular, ← mul_assoc, Complex.star_def]
  rw [show ∀ c b : ℂ, (starRingEnd ℂ) b * c * b = c * (b * (starRingEnd ℂ) b)
    by intro c b; ring]
  rw [Complex.mul_conj, ← Complex.sq_norm, inv_mul_cancel_left₀ frequencyScale_pos.ne']
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt frequencyScale_pos.le]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr frequencyScale_pos.ne']


/-- In the unweighted Fourier representation the two square roots in the
profile embeddings cancel the two weights in the existing correction kernel. -/
theorem profile_nullT_pairing {M : ℝ} (hM : 0 < M) (F : ConeProfile) :
    ⟪profileEmbed F, nullT M hM (profileEmbed F)⟫_ℂ =
      ∫ p : Phase4D × Phase4D,
        star (profileFourier F p.1) *
          fourierG M p.1.1 p.2.1 (sphereDot p.1.2 p.2.2) *
          profileFourier F p.2 ∂(phaseMeasure.prod phaseMeasure) := by
  let f := profileEmbed F
  unfold nullT
  refine (integralKernelOp_inner phaseMeasure _ _ f f).trans ?_
  apply integral_congr_ae
  have hf := profileEmbed_ae F
  filter_upwards [(phaseMeasure.quasiMeasurePreserving_fst (ν := phaseMeasure)).ae hf,
    (phaseMeasure.quasiMeasurePreserving_snd (μ := phaseMeasure)).ae hf] with p h₁ h₂
  have hn (ν : ℝ) : (Real.sqrt (wgt ν) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by linarith [(wgt_bounds ν).1]))
  rw [h₁, h₂, tKernel, Complex.ofReal_mul]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
  field_simp [hn]


/-- The modular test is the affine profile evaluated at the logistic radius. -/
theorem modularProfile_apply (F : ConeProfile) (n : Sphere4D) (s : ℝ) :
    modularProfile F n s = profileValue F (affineRadius s) n := by
  induction F with
  | nil => rfl
  | cons f F ih =>
    change f.angular n * f.radial (affineRadius s) + modularProfile F n s =
      f.radial (affineRadius s) * f.angular n + profileValue F (affineRadius s) n
    rw [ih, mul_comm (f.angular n)]

theorem profileValue_hasDerivAt (F : ConeProfile) (u : ℝ) (n : Sphere4D) :
    HasDerivAt (fun v => profileValue F v n) (profileDeriv F u n) u := by
  induction F with
  | nil => exact hasDerivAt_const u 0
  | cons f F ih =>
    exact (((f.smooth.differentiable (by simp) u).hasDerivAt).mul_const (f.angular n)).add ih

end NullConeGravity

