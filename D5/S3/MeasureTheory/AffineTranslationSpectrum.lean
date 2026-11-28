/- GID: D5/S3/MeasureTheory/AffineTranslationSpectrum
   generality: G
   mirror-B: none(waiver:covered-by-hyperfinite-type-ii1-factor-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Fourier translation multiplier on the positive half-line has spectrum equal to the nonnegative real axis. -/

import D5.S3.MeasureTheory.RealAffineRepresentation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Omega original.

The Fourier translation multiplier on the positive half-line has spectrum equal
to the nonnegative real axis. Bounded inverse multiplication off that axis
and interval-supported approximate eigenvectors give the two inclusions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.RealAffine

open MeasureTheory Set
open scoped NNReal ENNReal Topology FourierTransform ComplexInnerProductSpace

/-- Lebesgue measure on the positive-frequency half-line, viewed on the ambient line. -/
def positiveVolume : Measure ℝ := volume.restrict (Ici 0)

/-- Frequency-space realization of the positive-frequency Hilbert space. -/
abbrev PositiveL2 := Lp ℂ 2 positiveVolume

private theorem ae_positive : ∀ᵐ ξ ∂positiveVolume, 0 ≤ ξ :=
  ae_restrict_mem measurableSet_Ici

/-- The domain of the maximal translation multiplier. -/
def EnergyDomain : Submodule ℂ PositiveL2 where
  carrier := {f | MemLp (fun ξ => (frequency ξ : ℂ) * f ξ) 2 positiveVolume}
  zero_mem' := by
    refine (memLp_congr_ae ?_).mp (MemLp.zero (p := 2) (μ := positiveVolume) (ε := ℂ))
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := positiveVolume)] with ξ hξ
    change (0 : ℂ) = (frequency ξ : ℂ) * (0 : PositiveL2) ξ
    rw [hξ, Pi.zero_apply, mul_zero]
  add_mem' {f g} hf hg := by
    refine (memLp_congr_ae ?_).mp (hf.add hg)
    filter_upwards [Lp.coeFn_add f g] with ξ hξ
    change _ = (frequency ξ : ℂ) * (f + g) ξ
    rw [hξ]
    change _ = (frequency ξ : ℂ) * (f ξ + g ξ)
    rw [mul_add]
    rfl
  smul_mem' a f hf := by
    refine (memLp_congr_ae ?_).mp (hf.const_smul a)
    filter_upwards [Lp.coeFn_smul a f] with ξ hξ
    change a * ((frequency ξ : ℂ) * f ξ) = (frequency ξ : ℂ) * (a • f) ξ
    rw [hξ, Pi.smul_apply, smul_eq_mul]
    ring

private theorem memLp_energy (f : EnergyDomain) :
    MemLp (fun ξ => (frequency ξ : ℂ) * (f : PositiveL2) ξ) 2 positiveVolume := f.property

/-- Maximal multiplication operator by `2πξ` on positive frequencies. -/
def translationEnergy (f : EnergyDomain) : PositiveL2 :=
  (memLp_energy f).toLp _

private theorem translationEnergy_ae (f : EnergyDomain) :
    ⇑(translationEnergy f) =ᵐ[positiveVolume] fun ξ => (frequency ξ : ℂ) * (f : PositiveL2) ξ :=
  (memLp_energy f).coeFn_toLp

/-- The operator obtained by subtracting a scalar from translation energy. -/
def shiftedEnergy (z : ℂ) (f : EnergyDomain) : PositiveL2 :=
  translationEnergy f - z • (f : PositiveL2)

private theorem shiftedEnergy_ae (z : ℂ) (f : EnergyDomain) :
    ⇑(shiftedEnergy z f) =ᵐ[positiveVolume]
      fun ξ => ((frequency ξ : ℂ) - z) * (f : PositiveL2) ξ := by
  filter_upwards [Lp.coeFn_sub (translationEnergy f) (z • (f : PositiveL2)),
    translationEnergy_ae f, Lp.coeFn_smul z (f : PositiveL2)] with ξ h₁ h₂ h₃
  change (translationEnergy f - z • (f : PositiveL2)) ξ = _
  rw [h₁, Pi.sub_apply, h₂, h₃, Pi.smul_apply, smul_eq_mul, sub_mul]

/-- The resolvent condition for an unbounded operator, with its inverse bounded in Hilbert norm. -/
def IsEnergyResolvent (z : ℂ) : Prop :=
  Function.Surjective (shiftedEnergy z) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : EnergyDomain, ‖(f : PositiveL2)‖ ≤ C * ‖shiftedEnergy z f‖

/-- The spectrum of the maximal translation multiplier. -/
def translationSpectrum : Set ℂ := {z | ¬ IsEnergyResolvent z}

private theorem norm_bound {f g : PositiveL2} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ ξ ∂positiveVolume, ‖f ξ‖ ≤ C * ‖g ξ‖) : ‖f‖ ≤ C * ‖g‖ := by
  have hsm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.aestronglyMeasurable f) h 2
  rw [Lp.norm_def, Lp.norm_def]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top g)) hsm

private theorem gap_for_nonreal_or_negative (z : ℂ) (hz : ¬ (0 ≤ z.re ∧ z.im = 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ξ ≥ 0, δ ≤ ‖(frequency ξ : ℂ) - z‖ := by
  by_cases him : z.im = 0
  · have hre : z.re < 0 := lt_of_not_ge fun h => hz ⟨h, him⟩
    refine ⟨-z.re, neg_pos.mpr hre, fun ξ hξ => ?_⟩
    have h := Complex.re_le_norm ((frequency ξ : ℂ) - z)
    simp only [Complex.sub_re, Complex.ofReal_re] at h
    linarith [frequency_nonneg hξ]
  · refine ⟨|z.im|, abs_pos.mpr him, fun ξ _ => ?_⟩
    simpa using Complex.abs_im_le_norm ((frequency ξ : ℂ) - z)

private theorem resolvent_of_gap {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ ξ ≥ 0, δ ≤ ‖(frequency ξ : ℂ) - z‖) : IsEnergyResolvent z := by
  have hne (ξ : ℝ) (hξ : 0 ≤ ξ) : (frequency ξ : ℂ) - z ≠ 0 :=
    norm_pos_iff.mp (hδ.trans_le (hgap ξ hξ))
  constructor
  · intro f
    let v : ℝ → ℂ := fun ξ => (((frequency ξ : ℂ) - z)⁻¹) * f ξ
    have hm : Measurable (fun ξ : ℝ => ((frequency ξ : ℂ) - z)⁻¹) := by
      unfold frequency
      fun_prop
    have hv : MemLp v 2 positiveVolume := by
      apply (Lp.memLp f).of_le_mul (hm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      filter_upwards [ae_positive] with ξ hξ
      dsimp [v]
      rw [norm_mul, norm_inv]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ (hgap ξ hξ)) (norm_nonneg _)
    let g : PositiveL2 := hv.toLp v
    have huv : ∀ᵐ ξ ∂positiveVolume, ((frequency ξ : ℂ) - z) * g ξ = f ξ := by
      filter_upwards [hv.coeFn_toLp, ae_positive] with ξ hvξ hξ
      rw [hvξ]
      dsimp [v]
      rw [← mul_assoc, mul_inv_cancel₀ (hne ξ hξ), one_mul]
    have hg : g ∈ EnergyDomain := by
      refine (memLp_congr_ae ?_).mp ((Lp.memLp f).add ((Lp.memLp g).const_smul z))
      filter_upwards [huv] with ξ huvξ
      change f ξ + z * g ξ = (frequency ξ : ℂ) * g ξ
      rw [← huvξ]
      ring
    refine ⟨⟨g, hg⟩, Lp.ext ?_⟩
    exact (shiftedEnergy_ae z ⟨g, hg⟩).trans huv
  · refine ⟨δ⁻¹, inv_nonneg.mpr hδ.le, fun f => norm_bound (inv_nonneg.mpr hδ.le) ?_⟩
    filter_upwards [shiftedEnergy_ae z f, ae_positive] with ξ hshift hξ
    rw [hshift, norm_mul, ← mul_assoc]
    have hb : 1 ≤ δ⁻¹ * ‖(frequency ξ : ℂ) - z‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ hδ, one_mul]
      exact hgap ξ hξ
    exact le_mul_of_one_le_left (norm_nonneg _) hb

private theorem ofReal_not_resolvent (x : ℝ) (hx : 0 ≤ x) : ¬ IsEnergyResolvent (x : ℂ) := by
  rintro ⟨_, C, hC, hbound⟩
  let ε : ℝ := (C + 1)⁻¹
  have hε : 0 < ε := inv_pos.mpr (by positivity)
  have hπ : 0 < 2 * Real.pi := by positivity
  let a : ℝ := x / (2 * Real.pi)
  let b : ℝ := (x + ε) / (2 * Real.pi)
  let S : Set ℝ := Ioo a b
  have ha : 0 ≤ a := div_nonneg hx hπ.le
  have hab : a < b := (div_lt_div_iff_of_pos_right hπ).2 (lt_add_of_pos_right x hε)
  have hS : positiveVolume S = ENNReal.ofReal (b - a) := by
    have hsub : Ioo a b ⊆ Ici (0 : ℝ) := fun _ hξ => ha.trans hξ.1.le
    rw [positiveVolume, Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hsub,
      Real.volume_Ioo]
  have hSn : positiveVolume S ≠ 0 := by
    rw [hS]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hSt : positiveVolume S ≠ ∞ := by rw [hS]; exact ENNReal.ofReal_ne_top
  let v : ℝ → ℂ := S.indicator (fun _ => 1)
  have hv : MemLp v 2 positiveVolume :=
    memLp_indicator_const 2 measurableSet_Ioo.nullMeasurableSet 1 (.inr hSt)
  let g : PositiveL2 := hv.toLp v
  have hgpos : 0 < ‖g‖ := by
    change 0 < ‖hv.toLp v‖
    rw [Lp.norm_toLp, eLpNorm_indicator_const' measurableSet_Ioo.nullMeasurableSet hSn
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
    rw [enorm_one, one_mul, ← ENNReal.toReal_rpow]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hSn hSt) _
  have hξS {ξ : ℝ} (hξ : ξ ∈ S) : x < frequency ξ ∧ frequency ξ < x + ε := by
    refine ⟨?_, ?_⟩
    · dsimp [frequency, S, a] at hξ ⊢
      exact (div_lt_iff₀' hπ).1 hξ.1
    · dsimp [frequency, S, b] at hξ ⊢
      exact (lt_div_iff₀' hπ).1 hξ.2
  have hg : g ∈ EnergyDomain := by
    apply (Lp.memLp g).of_le_mul
    · have hfreq : Continuous (fun ξ : ℝ => (frequency ξ : ℂ)) := by
        unfold frequency
        fun_prop
      exact hfreq.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)
    filter_upwards [hv.coeFn_toLp] with ξ hξ
    change ‖(frequency ξ : ℂ) * g ξ‖ ≤ (x + ε) * ‖g ξ‖
    by_cases hmem : ξ ∈ S
    · rw [norm_mul, Complex.norm_of_nonneg ((hx.trans (hξS hmem).1.le))]
      gcongr
      exact (hξS hmem).2.le
    · have hz : g ξ = 0 := hξ.trans (indicator_of_notMem hmem _)
      simp [hz]
  let u : EnergyDomain := ⟨g, hg⟩
  have happrox : ‖shiftedEnergy (x : ℂ) u‖ ≤ ε * ‖g‖ := by
    apply norm_bound hε.le
    filter_upwards [shiftedEnergy_ae (x : ℂ) u, hv.coeFn_toLp] with ξ h₁ h₂
    rw [h₁]
    change ‖((frequency ξ : ℂ) - (x : ℂ)) * g ξ‖ ≤ _
    by_cases hmem : ξ ∈ S
    · rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_nonneg.mpr (hξS hmem).1.le)]
      gcongr
      linarith [(hξS hmem).2]
    · have hz : g ξ = 0 := h₂.trans (indicator_of_notMem hmem _)
      simp [hz]
  have hmul := (hbound u).trans (mul_le_mul_of_nonneg_left happrox hC)
  change ‖g‖ ≤ C * (ε * ‖g‖) at hmul
  rw [← mul_assoc] at hmul
  have hfinal := (le_of_mul_le_mul_right (by simpa only [one_mul] using hmul) hgpos : 1 ≤ C * ε)
  have hC1 : 0 < C + 1 := by positivity
  dsimp [ε] at hfinal
  rw [← div_eq_mul_inv, le_div_iff₀ hC1, one_mul] at hfinal
  linarith

/-- The unbounded translation generator has spectrum exactly the nonnegative real axis. -/
theorem translationEnergy_spectrum :
    translationSpectrum = {z : ℂ | 0 ≤ z.re ∧ z.im = 0} := by
  ext z
  change (¬ IsEnergyResolvent z) ↔ 0 ≤ z.re ∧ z.im = 0
  constructor
  · intro h
    by_contra hn
    obtain ⟨δ, hδ, hgap⟩ := gap_for_nonreal_or_negative z hn
    exact h (resolvent_of_gap hδ hgap)
  · rintro ⟨hz, hi⟩
    have he : (z.re : ℂ) = z := Complex.ext (by simp) (by simpa using hi.symm)
    exact he ▸ ofReal_not_resolvent z.re hz

/-- Restriction to nonnegative frequencies, preserving representatives almost everywhere. -/
def positiveRestriction (f : PositionL2) : PositiveL2 :=
  ((Lp.memLp f).restrict (Ici 0)).toLp f

private theorem positiveRestriction_ae (f : PositionL2) :
    ⇑(positiveRestriction f) =ᵐ[positiveVolume] f :=
  ((Lp.memLp f).restrict (Ici 0)).coeFn_toLp

private theorem phase_memLp_positive (a : ℝ) (f : PositiveL2) :
    MemLp (fun ξ => phase a ξ * f ξ) 2 positiveVolume := by
  have h : Continuous (phase a) := by unfold phase frequency; fun_prop
  apply (Lp.memLp f).of_le (h.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun ξ => by
    change ‖phase a ξ * f ξ‖ ≤ ‖f ξ‖
    simp [phase, Complex.norm_exp]

/-- Positive-frequency translation in the Plancherel representation. -/
def positiveTranslation (a : ℝ) (f : PositiveL2) : PositiveL2 :=
  (phase_memLp_positive a f).toLp _

theorem positiveTranslation_ae (a : ℝ) (f : PositiveL2) :
    ⇑(positiveTranslation a f) =ᵐ[positiveVolume] fun ξ => phase a ξ * f ξ :=
  (phase_memLp_positive a f).coeFn_toLp

theorem positiveTranslation_fourier (c a : ℝ) (f : PositionL2) :
    positiveRestriction (𝓕 (affineUnitary c (translation c a) f)) =
      positiveTranslation a (positiveRestriction (𝓕 f)) := by
  apply Lp.ext
  have hs : scale (translation c a) = 1 := by simp [scale, translation]
  filter_upwards [positiveRestriction_ae (𝓕 (affineUnitary c (translation c a) f)),
    (fourier_affineUnitary_ae (translation c a) f).filter_mono
      (ae_mono Measure.restrict_le_self), positiveRestriction_ae (𝓕 f),
    positiveTranslation_ae a (positiveRestriction (𝓕 f))] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₄, h₃]
  rw [hs]
  simp [translation]

private theorem positiveTranslation_zero (f : PositiveL2) : positiveTranslation 0 f = f := by
  apply Lp.ext
  filter_upwards [positiveTranslation_ae 0 f] with ξ hξ
  simpa [phase] using hξ

private def phaseSlope (a : ℝ) (f : PositiveL2) (ξ : ℝ) : ℂ :=
  a⁻¹ • ((phase a ξ - 1) * f ξ)

private theorem phaseSlope_ae (a : ℝ) (f : PositiveL2) :
    ⇑(a⁻¹ • (positiveTranslation a f - f) : PositiveL2) =ᵐ[positiveVolume] phaseSlope a f := by
  filter_upwards [Lp.coeFn_smul a⁻¹ (positiveTranslation a f - f),
    Lp.coeFn_sub (positiveTranslation a f) f, positiveTranslation_ae a f] with ξ h₁ h₂ h₃
  rw [h₁, Pi.smul_apply, h₂, Pi.sub_apply, h₃, phaseSlope, sub_mul, one_mul]

private theorem phaseSlope_tendsto (f : PositiveL2) (ξ : ℝ) :
    Filter.Tendsto (fun a => phaseSlope a f ξ) (𝓝[≠] (0 : ℝ))
      (𝓝 (Complex.I * ((frequency ξ : ℂ) * f ξ))) := by
  have h := (phase_hasDerivAt 0 ξ).mul_const (f ξ)
  convert h.tendsto_slope_zero using 1
  · funext a
    simp only [phaseSlope, zero_add, phase, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
      one_mul, sub_mul]
  · simp only [phase, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]
    congr 1
    ring

private theorem phaseSlope_bound (a : ℝ) (f : PositiveL2) (ξ : ℝ) :
    ‖phaseSlope a f ξ‖ ≤ ‖(frequency ξ : ℂ) * f ξ‖ := by
  by_cases ha : a = 0
  · simp [ha, phaseSlope, abs_nonneg, mul_nonneg]
  have h : ‖phase a ξ - 1‖ ≤ ‖a * frequency ξ‖ := by
    simpa [phase, mul_comm] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a * frequency ξ))
  calc
    _ = ‖a⁻¹‖ * (‖phase a ξ - 1‖ * ‖f ξ‖) := by rw [phaseSlope, norm_smul, norm_mul]
    _ ≤ ‖a⁻¹‖ * (‖a * frequency ξ‖ * ‖f ξ‖) := by gcongr
    _ = _ := by
      rw [norm_inv, norm_mul a, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha),
        one_mul, norm_mul, Complex.norm_real]

private def infinitesimal (f : PositiveL2) (ξ : ℝ) : ℂ :=
  Complex.I * ((frequency ξ : ℂ) * f ξ)

private theorem derivative_representative {f g : PositiveL2}
    (h : HasDerivAt (fun a => positiveTranslation a f) g 0) :
    ⇑g =ᵐ[positiveVolume] infinitesimal f := by
  have hlp := h.tendsto_slope_zero
  simp only [zero_add, positiveTranslation_zero] at hlp
  have hm := tendstoInMeasure_of_tendsto_Lp hlp
  have hm' := hm.congr_left (fun a => phaseSlope_ae a f)
  obtain ⟨a, ha, hae⟩ := hm'.exists_seq_tendsto_ae'
  filter_upwards [hae] with ξ hξ
  exact tendsto_nhds_unique hξ ((phaseSlope_tendsto f ξ).comp ha)

private theorem infinitesimal_ae (f : EnergyDomain) :
    ⇑(Complex.I • translationEnergy f) =ᵐ[positiveVolume] infinitesimal (f : PositiveL2) := by
  filter_upwards [Lp.coeFn_smul Complex.I (translationEnergy f), translationEnergy_ae f]
    with ξ h₁ h₂
  rw [h₁, Pi.smul_apply, smul_eq_mul, h₂, infinitesimal]

private theorem phaseSlope_memLp (a : ℝ) (f : PositiveL2) :
    MemLp (phaseSlope a f) 2 positiveVolume :=
  (memLp_congr_ae (phaseSlope_ae a f)).mp (Lp.memLp _)

private theorem phaseSlope_sub_bound (a : ℝ) (f : EnergyDomain) (ξ : ℝ) :
    ‖phaseSlope a (f : PositiveL2) ξ - infinitesimal (f : PositiveL2) ξ‖ ≤
      ‖(2 : ℂ) * ((frequency ξ : ℂ) * (f : PositiveL2) ξ)‖ := by
  calc
    _ ≤ ‖phaseSlope a (f : PositiveL2) ξ‖ + ‖infinitesimal (f : PositiveL2) ξ‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [infinitesimal, norm_mul Complex.I, Complex.norm_I, one_mul, norm_mul (2 : ℂ)]
      norm_num
      have hb := phaseSlope_bound a (f : PositiveL2) ξ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hb
      linarith only [hb]

set_option maxHeartbeats 600000 in
/-- The maximal multiplication operator is the strong derivative of the translation orbit. -/
theorem translationEnergy_hasDerivAt (f : EnergyDomain) :
    HasDerivAt (fun a => positiveTranslation a (f : PositiveL2))
      (Complex.I • translationEnergy f) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, positiveTranslation_zero]
  let q := fun a => a⁻¹ • (positiveTranslation a (f : PositiveL2) - (f : PositiveL2))
  let g := Complex.I • translationEnergy f
  let F := fun a ξ => phaseSlope a (f : PositiveL2) ξ - infinitesimal (f : PositiveL2) ξ
  have hF (a : ℝ) : ⇑(q a - g) =ᵐ[positiveVolume] F a := by
    filter_upwards [Lp.coeFn_sub (q a) g, phaseSlope_ae a (f : PositiveL2), infinitesimal_ae f]
      with ξ h₁ h₂ h₃
    rw [h₁, Pi.sub_apply, h₂, h₃]
  have hFm (a : ℝ) : MemLp (F a) 2 positiveVolume :=
    (memLp_congr_ae (hF a)).mp (Lp.memLp _)
  have hz (ξ : ℝ) : Filter.Tendsto (fun a => F a ξ) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have ht : Filter.Tendsto (fun a => phaseSlope a (f : PositiveL2) ξ)
        (𝓝[≠] (0 : ℝ)) (𝓝 (infinitesimal (f : PositiveL2) ξ)) :=
      phaseSlope_tendsto (f : PositiveL2) ξ
    simpa only [sub_self] using ht.sub_const (infinitesimal (f : PositiveL2) ξ)
  let M := fun ξ => (2 : ℂ) * ((frequency ξ : ℂ) * (f : PositiveL2) ξ)
  have hM : MemLp M 2 positiveVolume := (memLp_energy f).const_smul (2 : ℂ)
  have hMt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hM.eLpNorm_lt_top
  have hInt : Filter.Tendsto (fun a : ℝ => ∫⁻ ξ, ‖F a ξ‖ₑ ^ (2 : ℝ) ∂positiveVolume)
      (𝓝[≠] 0) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence'
      (l := 𝓝[≠] (0 : ℝ)) (F := fun a ξ => ‖F a ξ‖ₑ ^ (2 : ℝ)) (f := fun _ : ℝ => (0 : ℝ≥0∞)) (μ := positiveVolume)
      (fun ξ => ‖M ξ‖ₑ ^ (2 : ℝ))
      (Filter.Eventually.of_forall fun a => (hFm a).aestronglyMeasurable.enorm.pow_const _)
      (Filter.Eventually.of_forall fun a => Filter.Eventually.of_forall fun ξ => by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (phaseSlope_sub_bound a f ξ))
      (by simpa using hMt.ne)
      (Filter.Eventually.of_forall fun ξ => by
        simpa [Function.comp_def] using
          (ENNReal.continuous_rpow_const (y := 2)).continuousAt.tendsto.comp
          ((continuous_enorm.continuousAt (x := 0)).tendsto.comp (hz ξ)))
    simpa using h
  change Filter.Tendsto q (𝓝[≠] (0 : ℝ)) (𝓝 g)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (a : ℝ) : ‖q a - g‖ =
      ((∫⁻ ξ, ‖F a ξ‖ₑ ^ (2 : ℝ) ∂positiveVolume) ^ (1 / 2 : ℝ)).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae (hF a),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (hFm a).aestronglyMeasurable]
    norm_num
  simp_rw [he]
  have hr := (ENNReal.continuous_rpow_const (y := 1 / 2)).continuousAt.tendsto.comp hInt
  have hr₀ : Filter.Tendsto
      (fun a : ℝ => (∫⁻ ξ, ‖F a ξ‖ₑ ^ (2 : ℝ) ∂positiveVolume) ^ (1 / 2 : ℝ))
      (𝓝[≠] 0) (𝓝 0) := by simpa [Function.comp_def] using hr
  simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hr₀

/-- A strong translation derivative exists exactly on the maximal multiplier domain. -/
theorem translationEnergy_deriv_iff (f : PositiveL2) :
    (∃ g : PositiveL2, HasDerivAt (fun a => positiveTranslation a f) g 0) ↔ f ∈ EnergyDomain := by
  constructor
  · rintro ⟨g, hg⟩
    have h := derivative_representative hg
    have hm := (Lp.memLp g).const_smul (-Complex.I)
    refine (memLp_congr_ae ?_).mp hm
    filter_upwards [h] with ξ hξ
    change -Complex.I * g ξ = (frequency ξ : ℂ) * f ξ
    rw [hξ, infinitesimal, ← mul_assoc, neg_mul, ← pow_two, Complex.I_sq, neg_neg, one_mul]
  · intro hf
    exact ⟨_, translationEnergy_hasDerivAt ⟨f, hf⟩⟩

/-- Every vector in the maximal multiplier domain has nonnegative translation energy. -/
theorem translationEnergy_nonneg (f : EnergyDomain) :
    0 ≤ (inner ℂ (f : PositiveL2) (translationEnergy f)).re := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (f : PositiveL2) (translationEnergy f)
  rw [L2.inner_def]
  change 0 ≤ RCLike.re (K := ℂ) (∫ ξ, inner ℂ ((f : PositiveL2) ξ)
    (translationEnergy f ξ) ∂positiveVolume)
  rw [← integral_re hi]
  apply integral_nonneg_of_ae
  filter_upwards [translationEnergy_ae f, ae_positive] with ξ h₁ hξ
  rw [h₁]
  change 0 ≤ (inner ℂ ((f : PositiveL2) ξ) ((frequency ξ : ℂ) • (f : PositiveL2) ξ)).re
  rw [inner_smul_right]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (frequency_nonneg hξ) (inner_self_nonneg (𝕜 := ℂ) (x := (f : PositiveL2) ξ))

end Omega.RealAffine
