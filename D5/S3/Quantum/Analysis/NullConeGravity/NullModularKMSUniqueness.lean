/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullModularKMSUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Detailed balance, bounded analytic modular strips, spectral temperature uniqueness, and null dilation support. -/

import D5.S3.Quantum.Analysis.NullConeGravity.HyperfiniteTypeII1Factor
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondMultipliers4D
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! The normalized thermal multiplier has an exact complementary KMS boundary
value on the upper strip. The existing null-diamond convention has reflected
frequency and twice the normalized multiplier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace NullConeGravity.NullModularKMSUniqueness

open Complex MeasureTheory Set Filter Omega.RealAffine
open D5.S3.Quantum.Analysis.NullConeGravity.HyperfiniteTypeII1Factor
open scoped ENNReal InnerProductSpace ComplexConjugate Topology

/-- The normalized positive-frequency multiplier. -/
def thermal (β ν : ℝ) : ℝ := (1 + Real.exp (-β * ν))⁻¹

/-- Detailed balance for a covariance symbol and its skew part. -/
def DetailedBalance (β ν a j : ℝ) : Prop :=
  a - j = Real.exp (-β * ν) * (a + j)

private theorem denominator_pos (x : ℝ) : 0 < 1 + Real.exp x := by positivity

theorem kms_detailed_balance_unique {β ν : ℝ} (hβ : 0 < β) (hν : ν ≠ 0)
    (a j : ℝ) :
    DetailedBalance β ν a j ↔
      a = (1 + Real.exp (-β * ν)) / (1 - Real.exp (-β * ν)) * j ∧
      a = Real.cosh (β * ν / 2) / Real.sinh (β * ν / 2) * j := by
  have hn : -β * ν ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hβ.ne') hν
  have he : Real.exp (-β * ν) ≠ 1 := by
    intro h
    apply hn
    exact Real.exp_injective (h.trans Real.exp_zero.symm)
  have hd : 1 - Real.exp (-β * ν) ≠ 0 := sub_ne_zero.mpr he.symm
  have hs : Real.sinh (β * ν / 2) ≠ 0 := by
    intro hz
    exact (div_ne_zero (mul_ne_zero hβ.ne' hν) (by norm_num)) (Real.sinh_eq_zero.mp hz)
  have hhalf : Real.exp (-(β * ν / 2)) =
      Real.exp (β * ν / 2) * Real.exp (-β * ν) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hc : Real.cosh (β * ν / 2) / Real.sinh (β * ν / 2) =
      (1 + Real.exp (-β * ν)) / (1 - Real.exp (-β * ν)) := by
    rw [Real.cosh_eq, Real.sinh_eq, hhalf]
    field_simp
  rw [hc, and_self]
  unfold DetailedBalance
  rw [div_mul_eq_mul_div, eq_div_iff hd]
  constructor <;> intro h <;> linarith

theorem kms_normalized_symbol_unique (β ν a : ℝ) :
    1 - a = Real.exp (-β * ν) * a ↔ a = thermal β ν := by
  unfold thermal
  rw [← one_div, eq_div_iff (denominator_pos _).ne']
  constructor <;> intro h <;> linarith

theorem kms_normalized_symbol_properties (β ν : ℝ) :
    0 < thermal β ν ∧ thermal β ν < 1 ∧
      thermal β (-ν) = 1 - thermal β ν ∧
      2 * thermal β ν - 1 = Real.tanh (β * ν / 2) ∧
      1 + Real.tanh (β * ν / 2) = 2 / (1 + Real.exp (-β * ν)) ∧
      1 - Real.tanh (β * ν / 2) = 2 / (1 + Real.exp (β * ν)) := by
  have he : 0 < Real.exp (-β * ν) := Real.exp_pos _
  have hr : thermal β (-ν) = 1 - thermal β ν := by
    unfold thermal
    rw [show -β * -ν = -(-β * ν) by ring, Real.exp_neg]
    field_simp
    ring
  have hhalf : Real.exp (-(β * ν / 2)) =
      Real.exp (β * ν / 2) * Real.exp (-β * ν) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have ht : 2 * thermal β ν - 1 = Real.tanh (β * ν / 2) := by
    unfold thermal
    rw [Real.tanh_eq, hhalf]
    field_simp
    ring
  refine ⟨inv_pos.mpr (denominator_pos _), ?_, hr, ht, ?_, ?_⟩
  · unfold thermal
    exact inv_lt_one_of_one_lt₀ (by linarith)
  · rw [← ht]
    unfold thermal
    ring
  · rw [← ht, show 1 - (2 * thermal β ν - 1) = 2 * (1 - thermal β ν) by ring, ← hr]
    unfold thermal
    rw [show -β * -ν = β * ν by ring]
    ring

/-- Null-diamond symbols use the reflected dimensionless frequency and normalization two. -/
theorem kms_beta_two_pi_equals_nullA (ν : ℝ) :
    thermal (2 * Real.pi) ν = NullConeGravity.a (-(2 * Real.pi) * ν) / 2 ∧
      thermal 1 ν = NullConeGravity.a (-ν) / 2 := by
  unfold thermal NullConeGravity.a
  constructor
  · ring
  · simp only [neg_mul, one_mul]
    ring

/-- Fourier phase with negative real-time frequency sign. -/
def phase (z : ℂ) (ν : ℝ) : ℂ := Complex.exp (-Complex.I * z * (ν : ℂ))

/-- The lower-boundary thermal symbol times the entire Fourier phase. -/
def stripKernel (β : ℝ) (z : ℂ) (ν : ℝ) : ℂ :=
  ((1 + Real.exp (β * ν))⁻¹ : ℝ) * phase z ν

/-- The normalized correlation integral on the upper KMS strip. -/
def kmsStrip (β : ℝ) (φ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ ν, φ ν * stripKernel β z ν

private theorem phase_norm (z : ℂ) (ν : ℝ) :
    ‖phase z ν‖ = Real.exp (z.im * ν) := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem stripKernel_norm (β : ℝ) (z : ℂ) (ν : ℝ) :
    ‖stripKernel β z ν‖ = Real.exp (z.im * ν) / (1 + Real.exp (β * ν)) := by
  rw [stripKernel, norm_mul, phase_norm, Complex.norm_real, Real.norm_of_nonneg
    (inv_nonneg.mpr (denominator_pos _).le), inv_mul_eq_div]

private theorem stripKernel_bound (β : ℝ) (z : ℂ) (ν : ℝ)
    (h₀ : 0 ≤ z.im) (hβ : z.im ≤ β) : ‖stripKernel β z ν‖ ≤ 1 := by
  rw [stripKernel_norm, div_le_iff₀ (denominator_pos _), one_mul]
  rcases le_total 0 ν with hn | hn
  · have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ hn)
    linarith
  · have he := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos h₀ hn)
    linarith [Real.exp_pos (β * ν)]

private theorem integrand_measurable (β : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ)
    (z : ℂ) : AEStronglyMeasurable (fun ν => φ ν * stripKernel β z ν) volume := by
  exact hφ.aestronglyMeasurable.mul (by
    unfold stripKernel phase
    fun_prop)

theorem modular_kms_strip_integrable (β : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ)
    (z : ℂ) (h₀ : 0 ≤ z.im) (hβ : z.im ≤ β) :
    Integrable (fun ν => φ ν * stripKernel β z ν) := by
  apply hφ.norm.mono' (integrand_measurable β hφ z)
  filter_upwards [] with ν
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (stripKernel_bound β z ν h₀ hβ)

theorem modular_kms_strip_bounded (β : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ)
    (z : ℂ) (h₀ : 0 ≤ z.im) (hβ : z.im ≤ β) :
    ‖kmsStrip β φ z‖ ≤ ∫ ν, ‖φ ν‖ := by
  unfold kmsStrip
  apply norm_integral_le_of_norm_le hφ.norm
  filter_upwards [] with ν
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (stripKernel_bound β z ν h₀ hβ)

theorem modular_kms_strip_continuous (β : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ) :
    ContinuousOn (kmsStrip β φ) {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β} := by
  unfold kmsStrip
  refine continuousOn_of_dominated (bound := fun ν => ‖φ ν‖)
    (fun z _ => integrand_measurable β hφ z) ?_ hφ.norm ?_
  · intro z hz
    filter_upwards [] with ν
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (stripKernel_bound β z ν hz.1 hz.2)
  · filter_upwards [] with ν
    apply Continuous.continuousOn
    unfold stripKernel phase
    fun_prop

/-- At distance at least δ from either boundary, the frequency factor in the derivative
has a uniform integrable domination coefficient independent of frequency. -/
private theorem derivative_bound (β δ : ℝ) (z : ℂ) (ν : ℝ)
    (hδ : 0 < δ) (hlo : δ ≤ z.im) (hhi : z.im ≤ β - δ) :
    |ν| * ‖stripKernel β z ν‖ ≤ δ⁻¹ := by
  have hexp : δ * |ν| ≤ Real.exp (δ * |ν|) := by
    linarith [Real.add_one_le_exp (δ * |ν|)]
  have hdecay : ‖stripKernel β z ν‖ ≤ Real.exp (-(δ * |ν|)) := by
    rw [stripKernel_norm, div_le_iff₀ (denominator_pos _)]
    rcases le_total 0 ν with hn | hn
    · rw [abs_of_nonneg hn]
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hn)
      rw [sub_mul, sub_eq_add_neg, Real.exp_add] at he
      linarith [Real.exp_pos (-(δ * ν))]
    · rw [abs_of_nonpos hn, mul_neg, neg_neg]
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hlo hn)
      exact he.trans (le_mul_of_one_le_right (Real.exp_pos _).le
        (by linarith [Real.exp_pos (β * ν)]))
  calc
    |ν| * ‖stripKernel β z ν‖ ≤ |ν| * Real.exp (-(δ * |ν|)) :=
      mul_le_mul_of_nonneg_left hdecay (abs_nonneg _)
    _ ≤ δ⁻¹ := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      rw [inv_mul_eq_div, le_div_iff₀ hδ]
      simpa only [mul_comm] using hexp

private theorem integrand_deriv (β : ℝ) (φ : ℝ → ℂ) (z : ℂ) (ν : ℝ) :
    HasDerivAt (fun w => φ ν * stripKernel β w ν)
      (φ ν * stripKernel β z ν * (-Complex.I * (ν : ℂ))) z := by
  have hd := ((hasDerivAt_id z).const_mul (-Complex.I)).mul_const (ν : ℂ)
  have hp := hd.cexp
  convert hp.const_mul (φ ν * ((1 + Real.exp (β * ν))⁻¹ : ℝ)) using 1
  · funext w
    unfold stripKernel phase
    simp only [id_eq]
    ring_nf
  · unfold stripKernel phase
    simp [id]
    ring

theorem modular_kms_strip_holomorphic (β : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ) :
    DifferentiableOn ℂ (kmsStrip β φ) {z : ℂ | 0 < z.im ∧ z.im < β} := by
  intro z hz
  have h₀ : 0 < z.im := hz.1
  have hβ : z.im < β := hz.2
  let δ := min z.im (β - z.im) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let s : Set ℂ := {w | δ < w.im ∧ w.im < β - δ}
  have hs : s ∈ 𝓝 z := by
    have hopen : IsOpen s := (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
    apply hopen.mem_nhds
    refine ⟨?_, ?_⟩
    · dsimp [δ]
      linarith [min_le_left z.im (β - z.im)]
    · dsimp [δ]
      linarith [min_le_right z.im (β - z.im)]
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := s) (x₀ := z) (bound := fun ν => δ⁻¹ * ‖φ ν‖) hs
    (Eventually.of_forall (integrand_measurable β hφ))
    (modular_kms_strip_integrable β hφ z h₀.le hβ.le)
    (F' := fun w ν => φ ν * stripKernel β w ν * (-Complex.I * (ν : ℂ)))
    ?_ ?_ (hφ.norm.const_mul δ⁻¹) ?_
  · exact hD.2.differentiableAt.differentiableWithinAt
  · exact (integrand_measurable β hφ z).mul (by fun_prop)
  · filter_upwards [] with ν w hw
    have hb := derivative_bound β δ w ν hδ hw.1.le hw.2.le
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖φ ν‖ * ‖stripKernel β w ν‖ * |ν| =
          ‖φ ν‖ * (|ν| * ‖stripKernel β w ν‖) := by ring
      _ ≤ ‖φ ν‖ * δ⁻¹ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := mul_comm _ _
  · filter_upwards [] with ν w _
    exact integrand_deriv β φ w ν

private theorem lower_symbol (β t ν : ℝ) :
    stripKernel β (t : ℂ) ν = ((thermal β (-ν) : ℝ) : ℂ) * phase (t : ℂ) ν := by
  simp only [stripKernel, thermal]
  rw [show -β * -ν = β * ν by ring]

private theorem upper_symbol (β t ν : ℝ) :
    stripKernel β ((t : ℂ) + Complex.I * (β : ℂ)) ν =
      (thermal β ν : ℂ) * phase (t : ℂ) ν := by
  have he : phase ((t : ℂ) + Complex.I * (β : ℂ)) ν =
      (Real.exp (β * ν) : ℂ) * phase (t : ℂ) ν := by
    unfold phase
    rw [Complex.ofReal_exp, Complex.ofReal_mul, ← Complex.exp_add]
    congr 1
    rw [mul_add, add_mul, ← mul_assoc (-Complex.I) Complex.I]
    rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
    ring
  have hr : (1 + Real.exp (β * ν))⁻¹ * Real.exp (β * ν) = thermal β ν := by
    unfold thermal
    rw [neg_mul, Real.exp_neg]
    field_simp
    ring
  rw [stripKernel, he, ← mul_assoc, ← Complex.ofReal_mul, hr]

theorem modular_kms_lower_boundary (β : ℝ) (φ : ℝ → ℂ) (t : ℝ) :
    kmsStrip β φ t = ∫ ν, φ ν * (thermal β (-ν) : ℂ) * phase t ν := by
  unfold kmsStrip
  apply integral_congr_ae
  filter_upwards [] with ν
  rw [lower_symbol, mul_assoc]

theorem modular_kms_upper_boundary (β : ℝ) (φ : ℝ → ℂ) (t : ℝ) :
    kmsStrip β φ ((t : ℂ) + Complex.I * (β : ℂ)) =
      ∫ ν, φ ν * (thermal β ν : ℂ) * phase t ν := by
  unfold kmsStrip
  apply integral_congr_ae
  filter_upwards [] with ν
  rw [upper_symbol, mul_assoc]

private theorem thermal_memLp (β : ℝ) :
    MemLp (fun ν => (thermal β ν : ℂ)) ∞ (volume : Measure ℝ) := by
  apply memLp_top_of_bound (C := 1)
  · unfold thermal
    fun_prop
  · filter_upwards [] with ν
    have h := kms_normalized_symbol_properties β ν
    rw [Complex.norm_of_nonneg h.1.le]
    exact h.2.1.le

private theorem phase_memLp (t : ℝ) : MemLp (phase (t : ℂ)) ∞ (volume : Measure ℝ) := by
  apply memLp_top_of_bound (C := 1)
  · unfold phase
    fun_prop
  · filter_upwards [] with ν
    rw [phase_norm]
    simp

/-- The normalized bounded thermal multiplier on Lebesgue L². -/
def thermalOp (β : ℝ) : PositionL2 →L[ℂ] PositionL2 :=
  NullConeGravity.mulOp volume _ (thermal_memLp β)

/-- Real modular-time evolution in spectral coordinates. -/
def spectralFlow (t : ℝ) : PositionL2 →L[ℂ] PositionL2 :=
  NullConeGravity.mulOp volume _ (phase_memLp t)

/-- Exact two-point KMS boundary values for arbitrary square-integrable vectors. -/
theorem modular_kms_boundary_identities (β t : ℝ) (f g : PositionL2) :
    let φ := fun ν => conj (f ν) * g ν
    Integrable φ ∧
      kmsStrip β φ t = ⟪f, ((1 : PositionL2 →L[ℂ] PositionL2) - thermalOp β)
        (spectralFlow t g)⟫_ℂ ∧
      kmsStrip β φ ((t : ℂ) + Complex.I * (β : ℂ)) =
        ⟪f, thermalOp β (spectralFlow t g)⟫_ℂ := by
  dsimp only
  have hu : ⇑(spectralFlow t g) =ᵐ[volume] fun ν => phase t ν * g ν :=
    NullConeGravity.mulOp_ae volume _ _ _
  have ha : ⇑(thermalOp β (spectralFlow t g)) =ᵐ[volume] fun ν =>
      (thermal β ν : ℂ) * spectralFlow t g ν :=
    NullConeGravity.mulOp_ae volume _ _ _
  refine ⟨?_, ?_, ?_⟩
  · simpa [RCLike.inner_apply, mul_comm] using L2.integrable_inner (𝕜 := ℂ) f g
  · rw [modular_kms_lower_boundary, L2.inner_def]
    apply integral_congr_ae
    change ∀ᵐ ν ∂volume, _ =
      ⟪f ν, (spectralFlow t g - thermalOp β (spectralFlow t g)) ν⟫_ℂ
    filter_upwards [hu, ha, Lp.coeFn_sub (spectralFlow t g) (thermalOp β (spectralFlow t g))]
      with ν h₁ h₂ h₃
    rw [h₃, Pi.sub_apply, h₂, h₁, (kms_normalized_symbol_properties β ν).2.2.1]
    simp only [RCLike.inner_apply, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  · rw [modular_kms_upper_boundary, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu, ha] with ν h₁ h₂
    rw [h₂, h₁]
    simp only [RCLike.inner_apply]
    ring

private theorem thermal_strict_mono {β₁ β₂ ν : ℝ} (hβ : β₁ < β₂) (hν : 0 < ν) :
    thermal β₁ ν < thermal β₂ ν := by
  unfold thermal
  apply (inv_lt_inv₀ (denominator_pos (-β₁ * ν)) (denominator_pos (-β₂ * ν))).2
  simpa only [add_comm] using
    add_lt_add_left (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right (neg_lt_neg hβ) hν)) 1

private theorem positive_integrand (β : ℝ) {φ : ℝ → ℝ} (hφ : Integrable φ) :
    Integrable (fun ν => φ ν * thermal β ν) := by
  apply hφ.norm.mono'
  · apply hφ.aestronglyMeasurable.mul
    unfold thermal
    fun_prop
  · filter_upwards [] with ν
    rw [norm_mul, Real.norm_of_nonneg (kms_normalized_symbol_properties β ν).1.le]
    exact mul_le_of_le_one_right (norm_nonneg _) (kms_normalized_symbol_properties β ν).2.1.le

private theorem upper_zero (β : ℝ) (φ : ℝ → ℝ) :
    kmsStrip β (fun ν => (φ ν : ℂ)) (Complex.I * (β : ℂ)) =
      (↑(∫ ν, φ ν * thermal β ν) : ℂ) := by
  have h := modular_kms_upper_boundary β (fun ν => (φ ν : ℂ)) 0
  simp only [Complex.ofReal_zero, zero_add, phase, mul_zero, zero_mul, Complex.exp_zero,
    mul_one, ← Complex.ofReal_mul, integral_complex_ofReal] at h
  exact h

/-- Positive-frequency spectral weight of nonzero mass strictly identifies inverse temperature. -/
theorem kms_strip_determines_temperature {β₁ β₂ : ℝ} (_h₁ : 0 < β₁) (_h₂ : 0 < β₂)
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hn : ∀ᵐ ν ∂volume, 0 ≤ φ ν)
    (hs : ∀ᵐ ν ∂volume, ν ≤ 0 → φ ν = 0) (hm : 0 < ∫ ν, φ ν)
    (he : kmsStrip β₁ (fun ν => (φ ν : ℂ)) (Complex.I * (β₁ : ℂ)) =
      kmsStrip β₂ (fun ν => (φ ν : ℂ)) (Complex.I * (β₂ : ℂ))) : β₁ = β₂ := by
  have strict {b c : ℝ} (hbc : b < c) :
      (∫ ν, φ ν * thermal b ν) < ∫ ν, φ ν * thermal c ν := by
    have hle : (fun ν => φ ν * thermal b ν) ≤ᵐ[volume] (fun ν => φ ν * thermal c ν) := by
      filter_upwards [hn, hs] with ν hν hzero
      by_cases hp : 0 < ν
      · exact mul_le_mul_of_nonneg_left (thermal_strict_mono hbc hp).le hν
      · simp [hzero (le_of_not_gt hp)]
    have hib := positive_integrand b hφ
    have hic := positive_integrand c hφ
    apply lt_of_le_of_ne (integral_mono_ae hib hic hle)
    intro heq
    have hz := (integral_eq_iff_of_ae_le hib hic hle).mp heq
    have hzφ : φ =ᵐ[volume] 0 := by
      filter_upwards [hz, hn, hs] with ν hν hnon hzero
      by_cases hp : 0 < ν
      · by_contra hnz
        have hpos : 0 < φ ν := lt_of_le_of_ne hnon (Ne.symm hnz)
        exact (mul_lt_mul_of_pos_left (thermal_strict_mono hbc hp) hpos).ne hν
      · exact hzero (le_of_not_gt hp)
    have hzint := integral_congr_ae hzφ
    simp at hzint
    linarith
  rw [upper_zero, upper_zero, Complex.ofReal_inj] at he
  rcases lt_trichotomy β₁ β₂ with h | h | h
  · exact False.elim ((strict h).ne he)
  · exact h
  · exact False.elim ((strict h).ne he.symm)

/-- The geometric coordinate dilation in the modular pullback. -/
def boostRay (s x : ℝ) : ℝ := Real.exp (2 * Real.pi * s) * x

theorem hsmi_modular_boost_ray_map (s t a : ℝ) :
    boostRay s 0 = 0 ∧
      (∀ x, boostRay (s + t) x = boostRay s (boostRay t x)) ∧
      boostRay s ⁻¹' (Ici a) = Ici (Real.exp (-(2 * Real.pi * s)) * a) ∧
      boostRay s ⁻¹' (Ioi 0) = Ioi 0 := by
  refine ⟨by simp [boostRay], ?_, ?_, ?_⟩
  · intro x
    simp only [boostRay, mul_add, Real.exp_add, mul_assoc]
  · ext x
    change a ≤ Real.exp (2 * Real.pi * s) * x ↔ Real.exp (-(2 * Real.pi * s)) * a ≤ x
    rw [Real.exp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _), mul_comm]
  · ext x
    change 0 < Real.exp (2 * Real.pi * s) * x ↔ 0 < x
    exact mul_pos_iff_of_pos_left (Real.exp_pos _)

private theorem boost_quasiPreserving (s : ℝ) :
    QuasiMeasurePreserving (boostRay s) volume volume := by
  refine ⟨by unfold boostRay; fun_prop, ?_⟩
  unfold boostRay
  rw [Real.map_volume_mul_left (Real.exp_ne_zero _)]
  exact Measure.AbsolutelyContinuous.smul_left .rfl _

theorem hsmi_modular_boost_preserves_halfline (s : ℝ) (f : PositionL2)
    (hf : ∀ᵐ x ∂volume, x ≤ 0 → f x = 0) :
    ∀ᵐ x ∂volume, x ≤ 0 → (minusSidedAction ⟨s, 0⟩ f) x = 0 := by
  filter_upwards [minusSidedAction_ae s 0 f, (boost_quasiPreserving s).ae hf] with x hx hz hneg
  rw [hx, add_zero]
  change (Real.exp (Real.pi * s) : ℂ) * f (boostRay s x) = 0
  rw [hz (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hneg), mul_zero]

/-- Exact shift of the cut-supported subspace under modular pullback. -/
private theorem boost_cut_forward (s a : ℝ) (f : PositionL2)
    (hf : ∀ᵐ x ∂volume, x < a → f x = 0) :
    ∀ᵐ x ∂volume, x < Real.exp (-(2 * Real.pi * s)) * a →
      (minusSidedAction ⟨s, 0⟩ f) x = 0 := by
  filter_upwards [minusSidedAction_ae s 0 f, (boost_quasiPreserving s).ae hf] with x hx hz hcut
  rw [hx, add_zero]
  change (Real.exp (Real.pi * s) : ℂ) * f (boostRay s x) = 0
  have hc : boostRay s x < a := by
    have h := congrArg (fun S : Set ℝ => x ∈ S) (hsmi_modular_boost_ray_map s 0 a).2.2.1
    have ha : ¬ (a ≤ boostRay s x) := by
      intro ha
      exact hcut.not_ge (h.mp ha)
    exact lt_of_not_ge ha
  rw [hz hc, mul_zero]

theorem hsmi_modular_boost_cut (s a : ℝ) (f : PositionL2) :
    (∀ᵐ x ∂volume, x < Real.exp (-(2 * Real.pi * s)) * a →
      (minusSidedAction ⟨s, 0⟩ f) x = 0) ↔ (∀ᵐ x ∂volume, x < a → f x = 0) := by
  refine ⟨?_, boost_cut_forward s a f⟩
  intro hf
  let b := Real.exp (-(2 * Real.pi * s)) * a
  let g := minusSidedAction ⟨s, 0⟩ f
  have he : Real.exp (-(2 * Real.pi * -s)) * b = a := by
    dsimp [b]
    rw [show -(2 * Real.pi * -s) = 2 * Real.pi * s by ring, ← mul_assoc,
      ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hback := boost_cut_forward (-s) b g hf
  rw [he] at hback
  have hcancel : minusSidedAction ⟨-s, 0⟩ g = f := by
    have hgroup : (⟨-s, 0⟩ : MinusAffine) * ⟨s, 0⟩ = 1 := by
      ext <;> simp [mul_coordinates, scale, show (1 : MinusAffine).s = 0 from rfl,
        show (1 : MinusAffine).a = 0 from rfl]
    change (minusSidedAction ⟨-s, 0⟩ * minusSidedAction ⟨s, 0⟩) f = f
    rw [← map_mul, hgroup, map_one]
    rfl
  rwa [hcancel] at hback

/-- The positive modular-time shift contains the original ray for a positive cut. -/
theorem hsmi_modular_boost_cut_inclusion {s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a) :
    Ici a ⊆ boostRay s ⁻¹' (Ici a) ∧
      minusSidedAction (dilation (-2 * Real.pi) (-s)) *
        minusSidedAction (translation (-2 * Real.pi) a) *
        (minusSidedAction (dilation (-2 * Real.pi) (-s)))⁻¹ =
        minusSidedAction (translation (-2 * Real.pi) (boostRay s a)) := by
  constructor
  · rw [(hsmi_modular_boost_ray_map s 0 a).2.2.1]
    apply Ici_subset_Ici.mpr
    apply mul_le_of_le_one_left ha.le
    exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  · have hc := (minusSided_covariance (-s) a (neg_nonpos.mpr hs)).2
    simpa only [boostRay, show -2 * Real.pi * -s = 2 * Real.pi * s by ring] using hc

end NullConeGravity.NullModularKMSUniqueness
