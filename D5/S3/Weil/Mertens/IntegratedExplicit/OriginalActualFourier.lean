/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/OriginalActualFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite zero-mass complex prefix has an integrable actual Fourier density. -/

/-
Copyright (c) 2026. Released under Apache 2.0.

Suppliers are imported, not copied. In particular Mathlib's FourierTransform
(David Loeffler), ImproperIntegrals (David Loeffler), and Bochner integral
files retain their own Apache-2.0 copyright and author notices upstream.
This file uses the elementary finite-step route, not an identification of the
pointwise Fourier integral with an abstract L2 transform.
-/
import D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Finite closed-step Fourier transforms and the actual finite spectral density. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology ComplexConjugate

namespace OriginalActualFourier

open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy

/-- Angular phase; the forward transform below uses `phase (-w) u`. -/
def phase (w u : ℝ) : ℂ := Complex.exp (Complex.I * (w : ℂ) * (u : ℂ))

lemma phase_norm (w u : ℝ) : ‖phase w u‖ = 1 := by
  have he : Complex.I * (w : ℂ) * (u : ℂ) = Complex.I * ((w * u : ℝ) : ℂ) := by
    push_cast
    ring
  simpa only [phase, he] using Complex.norm_exp_I_mul_ofReal (w * u)

lemma phase_continuous : Continuous (fun p : ℝ × ℝ => phase p.1 p.2) := by
  unfold phase
  fun_prop

lemma phase_add (w u v : ℝ) : phase w (u + v) = phase w u * phase w v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma phase_conj (w u : ℝ) : conj (phase w u) = phase (-w) u := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp

lemma phase_re (w u : ℝ) : (phase w u).re = Real.cos (w * u) := by
  have he : Complex.I * (w : ℂ) * (u : ℂ) = ((w * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simpa only [phase, he] using Complex.exp_ofReal_mul_I_re (w * u)

lemma phase_neg_left (w u : ℝ) : phase (-w) u = phase w (-u) := by
  unfold phase
  congr 1
  push_cast
  ring

/-- Literal Lebesgue integral, defined at every frequency. -/
def Ahat (A : ℝ → ℂ) (w : ℝ) : ℂ := ∫ u : ℝ, A u * phase (-w) u

lemma transform_integrable {A : ℝ → ℂ} (hA : Integrable A) (w : ℝ) :
    Integrable (fun u => A u * phase (-w) u) := by
  refine hA.mul_bdd ?_ (ae_of_all _ fun u => (phase_norm (-w) u).le)
  exact (phase_continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

lemma Ahat_bound {A : ℝ → ℂ} (_hA : Integrable A) (w : ℝ) :
    ‖Ahat A w‖ ≤ ∫ u : ℝ, ‖A u‖ := by
  calc
    _ ≤ ∫ u : ℝ, ‖A u * phase (-w) u‖ := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_mul, phase_norm, mul_one]

lemma Ahat_continuous {A : ℝ → ℂ} (hA : Integrable A) : Continuous (Ahat A) := by
  apply continuous_of_dominated (bound := fun u => ‖A u‖)
  · intro w
    exact (transform_integrable hA w).aestronglyMeasurable
  · intro w
    exact ae_of_all _ fun u => by simp only [norm_mul, phase_norm, mul_one, le_refl]
  · exact hA.norm
  · exact ae_of_all _ fun u => by unfold phase; fun_prop

variable {ι : Type*} [Fintype ι]

/-- Closed-step expansion. Its common tail cancels by the actual zero mass. -/
lemma prefix_eq_steps (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i, x i ≤ D) (u : ℝ) :
    «prefix» x a u = ∑ i, (Icc (x i) D).indicator (fun _ => a i) u := by
  classical
  simpa only [add_zero, sub_zero, intervalStep, Set.indicator, ite_mul, one_mul, zero_mul] using
    prefix_interval_expansion x a ha D 0 (by simpa only [sub_zero] using hx) u

lemma prefix_measurable (x : ι → ℝ) (a : ι → ℂ) : Measurable («prefix» x a) := by
  classical
  unfold «prefix»
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_Ici) measurable_const measurable_const

lemma prefix_zero_off_window (x : ι → ℝ) (a : ι → ℂ)
    (ha : ∑ i, a i = 0) {D : ℝ} (hx : ∀ i, x i ∈ Icc 0 D)
    (u : ℝ) (hu : u ∉ Icc 0 D) : «prefix» x a u = 0 := by
  classical
  by_cases h0 : 0 ≤ u
  · have hD : D < u := lt_of_not_ge (fun h => hu ⟨h0, h⟩)
    have hi : ∀ i, x i ≤ u := fun i => (hx i).2.trans hD.le
    simp [«prefix», hi, ha]
  · have hi : ∀ i, ¬x i ≤ u := fun i h => h0 ((hx i).1.trans h)
    simp [«prefix», hi]

/-- Equality is pointwise, including both window endpoints. -/
lemma prefix_eq_zero_extension (x : ι → ℝ) (a : ι → ℂ)
    (ha : ∑ i, a i = 0) {D : ℝ} (hx : ∀ i, x i ∈ Icc 0 D) :
    (Icc 0 D).indicator («prefix» x a) = «prefix» x a := by
  funext u
  by_cases hu : u ∈ Icc 0 D
  · simp [hu]
  · simp [hu, prefix_zero_off_window x a ha hx u hu]

lemma prefix_integrable (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i, x i ≤ D) : Integrable («prefix» x a) := by
  have hi (i : ι) : Integrable ((Icc (x i) D).indicator (fun _ : ℝ => a i)) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const (by simp [Real.volume_Icc])
  exact (integrable_finsetSum _ (fun i _ => hi i)).congr
    (ae_of_all _ fun u => (prefix_eq_steps x a ha D hx u).symm)

/-- The L2 statement is consumed directly from the pinned atomic owner. -/
theorem prefix_L1_L2 (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i, x i ≤ D) :
    Integrable («prefix» x a) ∧ Integrable (fun u : ℝ => ‖«prefix» x a u‖ ^ 2) :=
  ⟨prefix_integrable x a ha D hx, (shifted_hinge_prefix_energy x a ha 0).2.1⟩

private lemma step_transform_integrable (l D : ℝ) (b : ℂ) (w : ℝ) :
    Integrable (fun u : ℝ => (Icc l D).indicator (fun _ => b) u * phase (-w) u) := by
  apply Integrable.mul_bdd
    ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simp [Real.volume_Icc])))
  · exact (phase_continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ fun u => (phase_norm (-w) u).le

private lemma step_transform (l D : ℝ) (hl : l ≤ D) (b : ℂ) (w : ℝ) (hw : w ≠ 0) :
    (Complex.I * (w : ℂ)) *
        (∫ u : ℝ, (Icc l D).indicator (fun _ => b) u * phase (-w) u) =
      b * (phase (-w) l - phase (-w) D) := by
  have hc : -Complex.I * (w : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hw)
  have hind : (fun u : ℝ => (Icc l D).indicator (fun _ => b) u * phase (-w) u) =
      (Icc l D).indicator (fun u => b * Complex.exp ((-Complex.I * (w : ℂ)) * (u : ℂ))) := by
    funext u
    by_cases hu : u ∈ Icc l D <;> simp [hu, phase]
  rw [hind, integral_indicator measurableSet_Icc, integral_const_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hl,
    integral_exp_mul_complex hc]
  have he (u : ℝ) : (-Complex.I * (w : ℂ)) * (u : ℂ) =
      Complex.I * ((-w : ℝ) : ℂ) * (u : ℂ) := by push_cast; ring
  simp only [he]
  unfold phase
  field_simp [hc, Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr hw]
  <;> ring

/-- Exact finite Fourier identity, including frequency zero. -/
theorem frequency_mul_Ahat (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i, x i ≤ D) (w : ℝ) :
    (Complex.I * (w : ℂ)) * Ahat («prefix» x a) w = ∑ i, a i * phase (-w) (x i) := by
  classical
  by_cases hw : w = 0
  · simp [hw, phase, ha]
  · have he (u : ℝ) : «prefix» x a u * phase (-w) u =
        ∑ i, (Icc (x i) D).indicator (fun _ => a i) u * phase (-w) u := by
      rw [prefix_eq_steps x a ha D hx u, Finset.sum_mul]
    have hs (i : ι) := step_transform (x i) D (hx i) (a i) w hw
    unfold Ahat
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => step_transform_integrable (x i) D (a i) w),
      Finset.mul_sum]
    simp_rw [hs, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ha, zero_mul, sub_zero]

lemma frequency_Ahat_bound (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i, x i ≤ D) (w : ℝ) :
    |w| * ‖Ahat («prefix» x a) w‖ ≤ ∑ i, ‖a i‖ := by
  have h := congrArg norm (frequency_mul_Ahat x a ha D hx w)
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul] at h
  calc
    _ = ‖∑ i, a i * phase (-w) (x i)‖ := h
    _ ≤ ∑ i, ‖a i * phase (-w) (x i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, phase_norm, mul_one]

/-- One integrable global envelope avoids all near-zero and tail exclusions. -/
lemma normSq_Ahat_bound (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i, x i ≤ D) (w : ℝ) :
    ‖Ahat («prefix» x a) w‖ ^ 2 ≤
      ((∫ u : ℝ, ‖«prefix» x a u‖) ^ 2 + (∑ i, ‖a i‖) ^ 2) / (1 + w ^ 2) := by
  have h0 := Ahat_bound (prefix_L1_L2 x a ha D hx).1 w
  have h1 := frequency_Ahat_bound x a ha D hx w
  have hs0 : ‖Ahat («prefix» x a) w‖ ^ 2 ≤ (∫ u : ℝ, ‖«prefix» x a u‖) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) h0
  have hs1 : w ^ 2 * ‖Ahat («prefix» x a) w‖ ^ 2 ≤ (∑ i, ‖a i‖) ^ 2 := by
    simpa only [← pow_two, mul_pow, sq_abs] using
      mul_self_le_mul_self (mul_nonneg (abs_nonneg w) (norm_nonneg _)) h1
  have hd : 0 < 1 + w ^ 2 := by positivity
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem normSq_Ahat_integrable (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i, x i ≤ D) :
    Integrable (fun w : ℝ => ‖Ahat («prefix» x a) w‖ ^ 2) := by
  have hA := (prefix_L1_L2 x a ha D hx).1
  have hm := (Ahat_continuous hA).norm.pow 2
  have hb := integrable_inv_one_add_sq.const_mul
    ((∫ u : ℝ, ‖«prefix» x a u‖) ^ 2 + (∑ i, ‖a i‖) ^ 2)
  apply hb.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun w => by
    change ‖‖Ahat («prefix» x a) w‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖Ahat («prefix» x a) w‖)]
    simpa only [div_eq_mul_inv] using normSq_Ahat_bound x a ha D hx w

/-- Exactly the original density and positive Lebesgue `withDensity` measure. -/
def density (A : ℝ → ℂ) (w : ℝ) : ℝ := ‖Ahat A w‖ ^ 2 / (2 * Real.pi)
def rho (A : ℝ → ℂ) : Measure ℝ := volume.withDensity (fun w => ENNReal.ofReal (density A w))

lemma density_nonneg (A : ℝ → ℂ) (w : ℝ) : 0 ≤ density A w := by
  unfold density
  positivity

lemma density_continuous {A : ℝ → ℂ} (hA : Integrable A) : Continuous (density A) :=
  ((Ahat_continuous hA).norm.pow 2).div_const _

theorem actual_rho_finite (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i, x i ≤ D) : IsFiniteMeasure (rho («prefix» x a)) := by
  have hi : Integrable (density («prefix» x a)) :=
    (normSq_Ahat_integrable x a ha D hx).div_const (2 * Real.pi)
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (ae_of_all _ fun w => density_nonneg _ w)).mpr hi

end OriginalActualFourier
