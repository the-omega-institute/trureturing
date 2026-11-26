/- GID: D5/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/GaussianFocusingPhaseTransition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent Gaussian focusing transitions, strong multiplier limits, and Wick positivity. -/

import OmegaBuild.Commands
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace D5.S3.Quantum.Analysis.NullConeGravity.GaussianFocusingPhaseTransition

variable {Ω : Type*} [MeasurableSpace Ω] {γ : Measure Ω}
variable {X : ℕ → Ω → ℝ} {α v : ℕ → ℝ≥0}

/-- The mean energy of a single mode. -/
def a (α v : ℕ → ℝ≥0) (k : ℕ) : ℝ := (α k : ℝ) * (v k : ℝ)

/-- The total mean energy, allowing divergence. -/
def mass (α v : ℕ → ℝ≥0) : ℝ≥0∞ := ∑' k, (↑(α k * v k) : ℝ≥0∞)

private def modeEnergy (α : ℕ → ℝ≥0) (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal ((α k : ℝ) * (X k ω)^2)

/-- The energy of the first `N` modes. -/
def partialEnergy (α : ℕ → ℝ≥0) (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range N, modeEnergy α X k ω

/-- The energy of all modes, with value infinity when the series diverges. -/
def totalEnergy (α : ℕ → ℝ≥0) (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∑' k, modeEnergy α X k ω

omit [MeasurableSpace Ω] in
private theorem partialEnergy_ne_top (N : ℕ) (ω : Ω) : partialEnergy α X N ω ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top

private theorem measurable_totalEnergy (hX : ∀ k, Measurable (X k)) :
    Measurable (totalEnergy α X) := by
  unfold totalEnergy
  exact Measurable.tsum fun k => (measurable_const.mul ((hX k).pow_const 2)).ennreal_ofReal

private theorem measurable_partialEnergy (hX : ∀ k, Measurable (X k)) (N : ℕ) :
    Measurable (partialEnergy α X N) := by
  unfold partialEnergy
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_const.mul ((hX k).pow_const 2)).ennreal_ofReal

/-- Negative exponential on extended nonnegative inputs, assigning zero at infinity. -/
def expNeg (t : ℝ) (x : ℝ≥0∞) : ℝ :=
  if x = ⊤ then 0 else Real.exp (-t * x.toReal)

/-- The negative exponential of the energy, extended by zero at infinity. -/
def expNegScaledEnergy (α : ℕ → ℝ≥0) (X : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  expNeg t (totalEnergy α X ω)

private theorem measurable_expNeg (t : ℝ) : Measurable (expNeg t) :=
  measurable_const.piecewise (measurableSet_singleton _) (by fun_prop)

private theorem expNeg_nonneg (t : ℝ) (x : ℝ≥0∞) : 0 ≤ expNeg t x := by
  unfold expNeg
  split <;> positivity

private theorem expNeg_le_one {t : ℝ} (ht : 0 ≤ t) (x : ℝ≥0∞) : expNeg t x ≤ 1 := by
  unfold expNeg
  split
  · exact zero_le_one
  · exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ht x.toReal_nonneg])

private theorem tendsto_expNeg {ι : Type*} {l : Filter ι} {u : ι → ℝ≥0∞} {x : ℝ≥0∞}
    {t : ℝ} (ht : 0 < t) (hu : ∀ i, u i ≠ ⊤) (h : Tendsto u l (𝓝 x)) :
    Tendsto (fun i => expNeg t (u i)) l (𝓝 (expNeg t x)) := by
  by_cases hx : x = ⊤
  · subst x
    have hu' : Tendsto (fun i => (u i).toReal) l atTop := by
      apply ENNReal.tendsto_ofReal_nhds_top.mp
      exact h.congr (fun i => (ENNReal.ofReal_toReal (hu i)).symm)
    have hneg : Tendsto (fun i => -t * (u i).toReal) l atBot :=
      hu'.const_mul_atTop_of_neg (neg_lt_zero.mpr ht)
    simp only [expNeg, hu, ite_false, ite_true]
    exact Real.tendsto_exp_atBot.comp hneg
  · have hc := (ENNReal.tendsto_toReal hx).comp h
    simp only [expNeg, hu, hx, ite_false]
    exact Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul hc : Tendsto (fun i => -t * (u i).toReal) l (𝓝 (-t * x.toReal)))

/-- The exact quadratic Laplace transform of a centered real Gaussian, including zero variance. -/
theorem gaussian_quadratic_laplace {Y : Ω → ℝ} {s w : ℝ≥0}
    (hY : HasLaw Y (gaussianReal 0 w) γ) {t : ℝ} (ht : 0 < t) :
    ∫ ω, Real.exp (-t * (s : ℝ) * (Y ω)^2) ∂γ =
      1 / Real.sqrt (1 + 2 * t * (s : ℝ) * (w : ℝ)) := by
  rw [show (fun ω => Real.exp (-t * (s : ℝ) * (Y ω)^2)) =
      (fun x : ℝ => Real.exp (-t * (s : ℝ) * x^2)) ∘ Y from rfl,
    hY.integral_comp (by fun_prop)]
  by_cases hw : w = 0
  · subst w
    simp [gaussianReal_zero_var]
  have hw' : 0 < (w : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hw)
  let b : ℝ := (2 * (w : ℝ))⁻¹ + t * (s : ℝ)
  have hb : 0 < b := by dsimp [b]; positivity
  rw [integral_gaussianReal_eq_integral_smul hw]
  have hfun (x : ℝ) : gaussianPDFReal 0 w x • Real.exp (-t * (s : ℝ) * x^2) =
      (Real.sqrt (2 * Real.pi * (w : ℝ)))⁻¹ * Real.exp (-b * x^2) := by
    simp only [smul_eq_mul, gaussianPDFReal_def, sub_zero, mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [b]
    ring
  simp_rw [hfun]
  rw [integral_const_mul, integral_gaussian, Real.sqrt_div Real.pi_pos.le]
  have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have he : 2 * Real.pi * (w : ℝ) = Real.pi * (2 * (w : ℝ)) := by ring
  have hb' : 2 * (w : ℝ) * b = 1 + 2 * t * (s : ℝ) * (w : ℝ) := by
    dsimp [b]
    field_simp
  rw [← hb', Real.sqrt_mul (by positivity : 0 ≤ 2 * (w : ℝ)),
    he, Real.sqrt_mul Real.pi_pos.le]
  field_simp [hπ, (Real.sqrt_pos.2 hb).ne', (Real.sqrt_pos.2 (by positivity : 0 < 2 * (w : ℝ))).ne']

/-- Independence factors the Laplace transform of each finite cutoff. -/
theorem finite_gaussian_laplace (hX : ∀ k, Measurable (X k))
    (hi : iIndepFun X γ) (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ)
    (N : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ ω, Real.exp (-t * (partialEnergy α X N ω).toReal) ∂γ =
      ∏ k ∈ Finset.range N, (1 / Real.sqrt (1 + 2 * t * a α v k)) := by
  have h (ω : Ω) : Real.exp (-t * (partialEnergy α X N ω).toReal) =
      ∏ k : Fin N, Real.exp (-t * (α k : ℝ) * (X k ω)^2) := by
    rw [partialEnergy, ENNReal.toReal_sum (f := fun k => modeEnergy α X k ω)
      (fun _ _ => ENNReal.ofReal_ne_top),
      Fin.prod_univ_eq_prod_range (fun k : ℕ => Real.exp (-t * (α k : ℝ) * (X k ω)^2)) N,
      ← Real.exp_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [modeEnergy, ENNReal.toReal_ofReal (by positivity), mul_assoc]
  simp_rw [h]
  have hi' : iIndepFun (fun k : Fin N => X k) γ := hi.precomp Fin.val_injective
  rw [iIndepFun.integral_fun_prod_comp (ι := Fin N) (X := fun k : Fin N => X k)
    (f := fun k x => Real.exp (-t * (α k : ℝ) * x^2)) hi'
    (fun k => (hX k).aemeasurable) (fun _ => by fun_prop), ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k _
  simpa only [a, mul_assoc] using gaussian_quadratic_laplace (hl k) ht

omit [MeasurableSpace Ω] in
private theorem tendsto_partialEnergy (ω : Ω) :
    Tendsto (fun N => partialEnergy α X N ω) atTop (𝓝 (totalEnergy α X ω)) :=
  ENNReal.summable.hasSum.tendsto_sum_nat

/-- The finite Laplace products converge to the Laplace integral of the full energy. -/
theorem tendsto_gaussian_laplace_product [IsProbabilityMeasure γ] (hX : ∀ k, Measurable (X k))
    (hi : iIndepFun X γ) (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => ∏ k ∈ Finset.range N, (1 / Real.sqrt (1 + 2 * t * a α v k)))
      atTop (𝓝 (∫ ω, expNegScaledEnergy α X t ω ∂γ)) := by
  simp_rw [← finite_gaussian_laplace hX hi hl _ ht]
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro N
    exact (Real.measurable_exp.comp (measurable_const.mul
      (measurable_partialEnergy hX N).ennreal_toReal)).aestronglyMeasurable
  · exact integrable_const _
  · intro N
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) ENNReal.toReal_nonneg
  · exact ae_of_all _ fun ω => by
      simpa only [expNegScaledEnergy, expNeg, partialEnergy_ne_top, ite_false] using
        tendsto_expNeg ht (fun N => partialEnergy_ne_top (α := α) (X := X) N ω)
          (tendsto_partialEnergy ω)

private theorem lintegral_modeEnergy {Y : Ω → ℝ} {s w : ℝ≥0}
    (hY : HasLaw Y (gaussianReal 0 w) γ) :
    ∫⁻ ω, ENNReal.ofReal ((s : ℝ) * (Y ω)^2) ∂γ = (↑(s * w) : ℝ≥0∞) := by
  rw [hY.lintegral_comp (f := fun x => ENNReal.ofReal ((s : ℝ) * x^2)) (by fun_prop)]
  have hsq : Integrable (fun x : ℝ => x^2) (gaussianReal 0 w) :=
    (memLp_id_gaussianReal (μ := 0) (v := w) 2).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal (hsq.const_mul _) (ae_of_all _ fun _ => by positivity),
    integral_const_mul]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := w)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable,
    integral_id_gaussianReal] at hv
  simp only [sub_zero] at hv
  rw [hv, ← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal]

/-- Tonelli identifies the expectation of the full energy even when it is infinite. -/
theorem lintegral_totalEnergy (hX : ∀ k, Measurable (X k))
    (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ) :
    ∫⁻ ω, totalEnergy α X ω ∂γ = mass α v := by
  unfold totalEnergy mass
  rw [lintegral_tsum (f := modeEnergy α X) (fun k =>
    (measurable_const.mul ((hX k).pow_const 2)).ennreal_ofReal.aemeasurable)]
  exact tsum_congr fun k => lintegral_modeEnergy (hl k)

private theorem modeFactor_pos {t : ℝ} (ht : 0 < t) (k : ℕ) :
    0 < 1 + 2 * t * a α v k := by unfold a; positivity

/-- The infinite product is the exponential of minus one half the extended sum of logs. -/
theorem gaussian_laplace_eq_log_sum [IsProbabilityMeasure γ] (hX : ∀ k, Measurable (X k))
    (hi : iIndepFun X γ) (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, expNegScaledEnergy α X t ω ∂γ =
      expNeg (1 / 2) (∑' k, ENNReal.ofReal (Real.log (1 + 2 * t * a α v k))) := by
  let b := fun k => ENNReal.ofReal (Real.log (1 + 2 * t * a α v k))
  have hlog (k : ℕ) : 0 ≤ Real.log (1 + 2 * t * a α v k) := by
    apply Real.log_nonneg
    have : 0 ≤ 2 * t * a α v k := by unfold a; positivity
    linarith
  have hlim := tendsto_expNeg (t := 1 / 2) (by norm_num)
    (u := fun N => ∑ k ∈ Finset.range N, b k)
    (fun _ => ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top)
    (ENNReal.summable.hasSum.tendsto_sum_nat (f := b))
  apply tendsto_nhds_unique (tendsto_gaussian_laplace_product hX hi hl ht)
  refine hlim.congr fun N => ?_
  have hN : (∑ k ∈ Finset.range N, b k) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top
  simp only [expNeg, hN, ite_false, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top),
    b, ENNReal.toReal_ofReal (hlog _), Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro k _
  rw [show -(1 / 2 : ℝ) * Real.log (1 + 2 * t * a α v k) =
      -Real.log (Real.sqrt (1 + 2 * t * a α v k)) by
        rw [Real.log_sqrt (modeFactor_pos ht k).le]
        ring,
    Real.exp_neg, Real.exp_log (Real.sqrt_pos.2 (modeFactor_pos ht k)), one_div]

private theorem prod_one_add_ge {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) (N : ℕ) :
    1 + ∑ k ∈ Finset.range N, b k ≤ ∏ k ∈ Finset.range N, (1 + b k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hs : 0 ≤ ∑ k ∈ Finset.range N, b k := Finset.sum_nonneg fun k _ => hb k
    calc
      _ ≤ (1 + ∑ k ∈ Finset.range N, b k) * (1 + b N) := by
        nlinarith [mul_nonneg hs (hb N)]
      _ ≤ _ := mul_le_mul_of_nonneg_right ih (by linarith [hb N])

/-- Infinite total mean forces the negative Laplace transform to vanish at every positive tilt. -/
theorem gaussian_laplace_eq_zero_of_mass_eq_top [IsProbabilityMeasure γ]
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X γ)
    (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ)
    (hm : mass α v = ⊤) {t : ℝ} (ht : 0 < t) :
    ∫ ω, expNegScaledEnergy α X t ω ∂γ = 0 := by
  have hs : Tendsto (fun N => ∑ k ∈ Finset.range N, a α v k) atTop atTop := by
    apply ENNReal.tendsto_ofReal_nhds_top.mp
    have h : Tendsto (fun N => ∑ k ∈ Finset.range N, (↑(α k * v k) : ℝ≥0∞))
        atTop (𝓝 (mass α v)) := ENNReal.summable.hasSum.tendsto_sum_nat
    rw [hm] at h
    refine h.congr fun N => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by unfold a; positivity)]
    simp [a]
  have hb : Tendsto (fun N => 1 + 2 * t * ∑ k ∈ Finset.range N, a α v k) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (hs.const_mul_atTop (by positivity))
  have hbound : Tendsto (fun N => 1 / Real.sqrt (1 + 2 * t * ∑ k ∈ Finset.range N, a α v k))
      atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hb)
  refine le_antisymm (le_of_tendsto_of_tendsto' (tendsto_gaussian_laplace_product hX hi hl ht)
    hbound (fun N => ?_)) (integral_nonneg fun ω => expNeg_nonneg _ _)
  simp_rw [one_div]
  rw [Finset.prod_inv_distrib, ← Real.sqrt_prod (Finset.range N) (fun k _ => (modeFactor_pos ht k).le)]
  have ha : ∀ k, 0 ≤ a α v k := by intro k; unfold a; positivity
  have hsum : 0 ≤ ∑ k ∈ Finset.range N, a α v k := Finset.sum_nonneg fun k _ => ha k
  apply inv_anti₀ (Real.sqrt_pos.2 (by positivity))
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  exact prod_one_add_ge (fun k => by unfold a; positivity) N

/-- Truncating each mode mean at one preserves the divergence criterion. -/
theorem mass_eq_top_iff_truncated (α v : ℕ → ℝ≥0) :
    mass α v = ⊤ ↔ (∑' k, min (↑(α k * v k) : ℝ≥0∞) 1) = ⊤ := by
  let b : ℕ → ℝ≥0∞ := fun k => ↑(α k * v k)
  change (∑' k, b k) = ⊤ ↔ (∑' k, min (b k) 1) = ⊤
  refine ⟨fun hb => ?_, fun h => top_unique (h ▸ ENNReal.tsum_le_tsum (fun _ => min_le_left ..))⟩
  by_contra ht
  have hs := ENNReal.finite_const_le_of_tsum_ne_top ht one_ne_zero
  let s := hs.toFinset
  have hEq (k : ↥((↑s : Set ℕ)ᶜ)) : b k = min (b k) 1 := by
    apply (min_eq_left ?_).symm
    have hk := k.property
    change (k : ℕ) ∉ s at hk
    have hn : ¬ 1 ≤ min (b k) 1 := fun h => hk (hs.mem_toFinset.mpr h)
    exact (lt_of_not_ge fun h => hn (le_min h le_rfl)).le
  apply (show (∑' k, b k) ≠ ⊤ → False from fun h => h hb)
  rw [← ENNReal.sum_add_tsum_compl s b]
  apply ENNReal.add_ne_top.2
  refine ⟨ENNReal.sum_ne_top.2 fun _ _ => ENNReal.coe_ne_top, ?_⟩
  rw [tsum_congr hEq]
  exact ne_top_of_le_ne_top ht (ENNReal.summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
    (fun _ _ => zero_le) (fun _ => le_rfl) ENNReal.summable)

private theorem ae_totalEnergy_lt_top (hX : ∀ k, Measurable (X k))
    (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ) (hm : mass α v < ⊤) :
    ∀ᵐ ω ∂γ, totalEnergy α X ω < ⊤ :=
  ae_lt_top (measurable_totalEnergy hX) ((lintegral_totalEnergy hX hl).trans_ne hm.ne)

private theorem ae_totalEnergy_eq_top [IsProbabilityMeasure γ] (hX : ∀ k, Measurable (X k))
    (hi : iIndepFun X γ) (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ)
    (hm : mass α v = ⊤) : ∀ᵐ ω ∂γ, totalEnergy α X ω = ⊤ := by
  have h0 := gaussian_laplace_eq_zero_of_mass_eq_top hX hi hl hm zero_lt_one
  have hi' : Integrable (expNegScaledEnergy α X 1) γ :=
    Integrable.mono' (integrable_const (1 : ℝ))
      ((measurable_expNeg 1).comp (measurable_totalEnergy hX)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        change ‖expNeg 1 (totalEnergy α X ω)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (expNeg_nonneg _ _)]
        exact expNeg_le_one zero_le_one _)
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun ω => expNeg_nonneg _ _) hi').mp h0]
    with ω hω
  by_contra h
  simp [expNeg, h] at hω

private theorem vacuum_probability_lower_bound [IsProbabilityMeasure γ]
    (hX : ∀ k, Measurable (X k)) (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ)
    (hm : mass α v < ⊤) {ℓ : ℝ} (hℓ : 1 < ℓ) :
    γ.real {ω | totalEnergy α X ω ≤ ENNReal.ofReal (Real.log ℓ)} ≥
      1 - (mass α v).toReal / Real.log ℓ := by
  let c := ENNReal.ofReal (Real.log ℓ)
  have hc := Real.log_pos hℓ
  let S := {ω | totalEnergy α X ω ≤ c}
  have hS : MeasurableSet S := measurableSet_le (measurable_totalEnergy hX) measurable_const
  have hM := meas_ge_le_lintegral_div (μ := γ)
    (measurable_totalEnergy (α := α) hX).aemeasurable
    (show c ≠ 0 from (ENNReal.ofReal_pos.2 hc).ne') ENNReal.ofReal_ne_top
  rw [lintegral_totalEnergy hX hl] at hM
  have htail : γ.real Sᶜ ≤ (mass α v).toReal / Real.log ℓ := calc
    _ ≤ γ.real {ω | c ≤ totalEnergy α X ω} :=
      measureReal_mono (fun ω hω => (lt_of_not_ge (show ¬ totalEnergy α X ω ≤ c from hω)).le)
    _ ≤ _ := by
      have hh := ENNReal.toReal_mono (ENNReal.div_ne_top hm.ne (ENNReal.ofReal_pos.2 hc).ne') hM
      simpa only [measureReal_def, ENNReal.toReal_div, c, ENNReal.toReal_ofReal hc.le] using hh
  have hcomp := measureReal_add_measureReal_compl (μ := γ) hS
  rw [probReal_univ] at hcomp
  change 1 - (mass α v).toReal / Real.log ℓ ≤ γ.real S
  linarith

/-- Finite total mean gives almost-sure finiteness and a quantitative probability bound.
Infinite mean, equivalently divergence of the truncated means, gives almost-sure divergence. -/
theorem gaussian_focusing_dichotomy [IsProbabilityMeasure γ]
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X γ)
    (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ) :
    (mass α v < ⊤ →
      (∀ᵐ ω ∂γ, totalEnergy α X ω < ⊤) ∧
      (∫⁻ ω, totalEnergy α X ω ∂γ) = mass α v ∧
      ∀ ℓ : ℝ, 1 < ℓ → γ.real {ω | totalEnergy α X ω ≤ ENNReal.ofReal (Real.log ℓ)} ≥
        1 - (mass α v).toReal / Real.log ℓ) ∧
    (mass α v = ⊤ → ∀ᵐ ω ∂γ, totalEnergy α X ω = ⊤) ∧
    (mass α v = ⊤ ↔ (∑' k, min (↑(α k * v k) : ℝ≥0∞) 1) = ⊤) :=
  ⟨fun hm => ⟨ae_totalEnergy_lt_top hX hl hm, lintegral_totalEnergy hX hl,
      fun _ hℓ => vacuum_probability_lower_bound hX hl hm hℓ⟩,
    ae_totalEnergy_eq_top hX hi hl, mass_eq_top_iff_truncated α v⟩

/-- An exponential threshold in the mean energy suffices for probability at least `1 - δ`. -/
theorem vacuum_probability_ge_one_sub [IsProbabilityMeasure γ]
    (hX : ∀ k, Measurable (X k)) (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ)
    (hm : mass α v < ⊤) {ℓ δ : ℝ} (hδ : 0 < δ) (hℓ : 1 < ℓ)
    (hcut : Real.exp ((mass α v).toReal / δ) ≤ ℓ) :
    1 - δ ≤ γ.real {ω | totalEnergy α X ω ≤ ENNReal.ofReal (Real.log ℓ)} := by
  have hlog := (Real.le_log_iff_exp_le (by linarith : 0 < ℓ)).2 hcut
  have h := (div_le_iff₀ (Real.log_pos hℓ)).2
    (mul_comm δ (Real.log ℓ) ▸ (div_le_iff₀ hδ).1 hlog)
  exact (sub_le_sub_left h _).trans (vacuum_probability_lower_bound hX hl hm hℓ)

/-- Independent centered Gaussians of any prescribed variances exist on the countable product. -/
theorem exists_canonical_gaussian_focusing_space (v : ℕ → ℝ≥0) :
    let γ := Measure.infinitePi (fun k => gaussianReal 0 (v k))
    ∃ X : ℕ → (ℕ → ℝ) → ℝ, (∀ k, Measurable (X k)) ∧ iIndepFun X γ ∧
      ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ := by
  refine ⟨fun k ω => ω k, fun k => measurable_pi_apply k, ?_, fun k => ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  · exact (measurePreserving_eval_infinitePi (fun j => gaussianReal 0 (v j)) k).hasLaw

/-- An active Wick-ordered Gaussian square gives a strictly subunit exponential on a
positive-probability set, with a quantitative subunit cutoff. -/
theorem wick_normal_ordered_focusing_below_one_pos_prob {Y : Ω → ℝ} {s w : ℝ≥0}
    (hY : HasLaw Y (gaussianReal 0 w) γ) (hs : 0 < s) (hw : 0 < w) :
    0 < γ {ω | Real.exp ((s : ℝ) * ((Y ω)^2 - w)) ≤ Real.exp (-(s * (w : ℝ)) / 2)} ∧
    0 < γ {ω | Real.exp ((s : ℝ) * ((Y ω)^2 - w)) < 1} := by
  have hw' : 0 < (w : ℝ) := by exact_mod_cast hw
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  let r := Real.sqrt ((w : ℝ) / 2)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hball : 0 < gaussianReal 0 w (Icc (-r) r) := by
    apply pos_iff_ne_zero.mpr
    intro h
    rw [gaussianReal_of_var_ne_zero _ hw.ne',
      withDensity_apply_eq_zero (measurable_gaussianPDF _ _)] at h
    change volume (Function.support (gaussianPDF 0 w) ∩ Icc (-r) r) = 0 at h
    rw [support_gaussianPDF hw.ne', univ_inter, Real.volume_Icc] at h
    exact (ENNReal.ofReal_pos.2 (by linarith)).ne' h
  have hp : 0 < γ (Y ⁻¹' Icc (-r) r) := by
    rwa [← Measure.map_apply_of_aemeasurable hY.aemeasurable measurableSet_Icc, hY.map_eq]
  have hsubset : Y ⁻¹' Icc (-r) r ⊆
      {ω | Real.exp ((s : ℝ) * ((Y ω)^2 - w)) ≤ Real.exp (-(s * (w : ℝ)) / 2)} := by
    intro ω hω
    have hx : |Y ω| ≤ r := abs_le.2 hω
    have hsq : (Y ω)^2 ≤ (w : ℝ) / 2 := by
      rw [← Real.sq_sqrt (by positivity : 0 ≤ (w : ℝ) / 2), ← sq_abs (Y ω)]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    exact Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hsq hs'.le])
  have hcut := hp.trans_le (measure_mono hsubset)
  refine ⟨hcut, hcut.trans_le (measure_mono ?_)⟩
  intro ω hω
  exact lt_of_le_of_lt (mem_ofPred_eq.mp hω)
    (Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hs' hw']))

private def multiply (γ : Measure Ω) (m : Ω → ℂ) (hm : Measurable m)
    (hb : ∀ ω, ‖m ω‖ ≤ 1) : Lp ℂ 2 γ →L[ℂ] Lp ℂ 2 γ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL γ ⊤ 2 2
    ((memLp_top_of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hb)).toLp m)

private theorem multiply_ae (m : Ω → ℂ) (hm : Measurable m) (hb : ∀ ω, ‖m ω‖ ≤ 1)
    (f : Lp ℂ 2 γ) : multiply γ m hm hb f =ᵐ[γ] fun ω => m ω * f ω := by
  let h := memLp_top_of_bound (μ := γ) hm.aestronglyMeasurable 1 (ae_of_all _ hb)
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (h.toLp m) f, h.coeFn_toLp]
    with ω hω he
  change ((ContinuousLinearMap.mul ℂ ℂ).holder 2 (h.toLp m) f) ω = m ω * f ω
  simpa only [ContinuousLinearMap.mul_apply', he] using hω

private theorem tendsto_lp_multipliers {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {m : ι → Ω → ℂ} {n : Ω → ℂ} {F : ι → Lp ℂ 2 γ} {g : Lp ℂ 2 γ}
    (f : Lp ℂ 2 γ) (hm : ∀ i, Measurable (m i)) (hn : Measurable n)
    (hb : ∀ i ω, ‖m i ω‖ ≤ 1) (hc : ∀ ω, ‖n ω‖ ≤ 1)
    (hF : ∀ i, F i =ᵐ[γ] fun ω => m i ω * f ω) (hg : g =ᵐ[γ] fun ω => n ω * f ω)
    (hlim : ∀ᵐ ω ∂γ, Tendsto (fun i => m i ω) l (𝓝 (n ω))) :
    Tendsto F l (𝓝 g) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  let d (i : ι) (ω : Ω) := m i ω * f ω - n ω * f ω
  have hd (i : ι) : AEStronglyMeasurable (d i) γ :=
    ((hm i).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)).sub
      (hn.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hconv : Tendsto (fun i => ∫⁻ ω, ENNReal.ofReal (‖d i ω‖ ^ 2) ∂γ) l (𝓝 0) := by
    simpa only [lintegral_zero] using
      (tendsto_lintegral_filter_of_dominated_convergence'
        (f := fun _ => 0) (fun ω => ENNReal.ofReal (4 * ‖f ω‖ ^ 2))
        (Eventually.of_forall fun i => ((hd i).norm.aemeasurable.pow_const 2).ennreal_ofReal)
        (Eventually.of_forall fun i => ae_of_all _ fun ω => by
          apply ENNReal.ofReal_le_ofReal
          have h : ‖d i ω‖ ≤ 2 * ‖f ω‖ := calc
            _ ≤ ‖m i ω * f ω‖ + ‖n ω * f ω‖ := norm_sub_le _ _
            _ ≤ _ := by
              simp only [norm_mul]
              nlinarith [mul_le_mul_of_nonneg_right (hb i ω) (norm_nonneg (f ω)),
                mul_le_mul_of_nonneg_right (hc ω) (norm_nonneg (f ω))]
          nlinarith [pow_le_pow_left₀ (norm_nonneg _) h 2])
        (by rw [← ofReal_integral_eq_lintegral_ofReal (hf.const_mul 4)
                  (ae_of_all _ fun _ => by positivity)]; exact ENNReal.ofReal_ne_top)
        (hlim.mono fun ω hω => by
          have hzero : Tendsto (fun i => d i ω) l (𝓝 0) := by
            simpa only [d, sub_self] using (hω.mul_const (f ω)).sub_const (n ω * f ω)
          simpa only [norm_zero, zero_pow two_ne_zero, ENNReal.ofReal_zero] using
            ENNReal.tendsto_ofReal (hzero.norm.pow 2)))
  have hr := (ENNReal.continuous_rpow_const (y := 1 / 2)).continuousAt.tendsto
    (x := (0 : ℝ≥0∞))
  have hz : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  rw [hz] at hr
  refine (hr.comp hconv).congr fun i => ?_
  rw [eLpNorm_congr_ae ((hF i).sub hg)]
  change (∫⁻ ω, ENNReal.ofReal (‖d i ω‖ ^ 2) ∂γ) ^ (1 / 2 : ℝ) = eLpNorm (d i) 2 γ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top (hd i)]
  congr 2
  ext ω
  rw [show (2 : ℝ≥0∞).toReal = 2 by simp, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    ENNReal.rpow_natCast, ← ofReal_norm,
    ENNReal.ofReal_pow (norm_nonneg _) 2]

private def resolventScalar (L : ℝ) (x : ℝ≥0∞) : ℝ :=
  let z := max 0 L * expNeg 1 x
  z / (1 + z)

private theorem measurable_resolventScalar (L : ℝ) : Measurable (resolventScalar L) := by
  have h := measurable_expNeg 1
  unfold resolventScalar
  fun_prop

private theorem norm_resolventScalar_le (L : ℝ) (x : ℝ≥0∞) :
    ‖(resolventScalar L x : ℂ)‖ ≤ 1 := by
  have hz := mul_nonneg (le_max_left 0 L) (expNeg_nonneg 1 x)
  rw [resolventScalar, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hz (by linarith))]
  exact (div_le_one (by linarith)).2 (by linarith)

private theorem resolventScalar_of_ne_top {L : ℝ} (hL : 0 < L) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    resolventScalar L x = L / (L + Real.exp x.toReal) := by
  simp only [resolventScalar, max_eq_right hL.le, expNeg, hx, ite_false, neg_mul, one_mul,
    Real.exp_neg]
  field_simp [(Real.exp_pos x.toReal).ne']
  ring

/-- Multiplication by the normalized resolvent of the finite-mode exponential clock. -/
def finiteResolvent (γ : Measure Ω) (α : ℕ → ℝ≥0) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (N : ℕ) (L : ℝ) : Lp ℂ 2 γ →L[ℂ] Lp ℂ 2 γ :=
  multiply γ (fun ω => (resolventScalar L (partialEnergy α X N ω) : ℂ))
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_resolventScalar L).comp (measurable_partialEnergy hX N)))
    (fun _ => norm_resolventScalar_le _ _)

/-- Multiplication by the normalized resolvent of the full exponential clock, zero at infinity. -/
def resolventMultiplier (γ : Measure Ω) (α : ℕ → ℝ≥0) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (L : ℝ) : Lp ℂ 2 γ →L[ℂ] Lp ℂ 2 γ :=
  multiply γ (fun ω => (resolventScalar L (totalEnergy α X ω) : ℂ))
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_resolventScalar L).comp (measurable_totalEnergy hX)))
    (fun _ => norm_resolventScalar_le _ _)

private def sublevel (α : ℕ → ℝ≥0) (X : ℕ → Ω → ℝ) (ℓ : ℝ) : Set Ω :=
  {ω | 1 ≤ ℓ ∧ totalEnergy α X ω ≤ ENNReal.ofReal (Real.log ℓ)}

private theorem measurableSet_sublevel (hX : ∀ k, Measurable (X k)) (ℓ : ℝ) :
    MeasurableSet (sublevel α X ℓ) :=
  (MeasurableSet.const _).inter (measurableSet_le (measurable_totalEnergy hX) measurable_const)

omit [MeasurableSpace Ω] in
private theorem norm_indicator_one_le (S : Set Ω) (ω : Ω) :
    ‖S.indicator (fun _ => (1 : ℂ)) ω‖ ≤ 1 := by
  by_cases h : ω ∈ S <;> simp [Set.indicator, h]

/-- Multiplication by the indicator of exponential clock readings at most `ℓ`. -/
def sublevelProjection (γ : Measure Ω) (α : ℕ → ℝ≥0) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (ℓ : ℝ) : Lp ℂ 2 γ →L[ℂ] Lp ℂ 2 γ :=
  multiply γ ((sublevel α X ℓ).indicator (fun _ => 1))
    (measurable_const.indicator (measurableSet_sublevel hX ℓ))
    (norm_indicator_one_le _)

/-- At every positive regularization parameter, the finite-mode resolvents converge strongly. -/
theorem tendsto_finiteResolvent (hX : ∀ k, Measurable (X k)) (f : Lp ℂ 2 γ) (L : ℝ) :
    Tendsto (fun N => finiteResolvent γ α X hX N L f) atTop
      (𝓝 (resolventMultiplier γ α X hX L f)) := by
  unfold finiteResolvent resolventMultiplier
  refine tendsto_lp_multipliers f
    (fun N => Complex.continuous_ofReal.measurable.comp
      ((measurable_resolventScalar L).comp (measurable_partialEnergy hX N)))
    (Complex.continuous_ofReal.measurable.comp
      ((measurable_resolventScalar L).comp (measurable_totalEnergy hX)))
    (fun _ _ => norm_resolventScalar_le _ _) (fun _ => norm_resolventScalar_le _ _)
    (fun _ => multiply_ae ..) (multiply_ae ..) ?_
  exact ae_of_all _ fun ω => by
    have h := (tendsto_expNeg zero_lt_one (fun N => partialEnergy_ne_top (α := α) (X := X) N ω)
      (tendsto_partialEnergy (α := α) (X := X) ω)).const_mul (max 0 L)
    have hd : 1 + max 0 L * expNeg 1 (totalEnergy α X ω) ≠ 0 := by
      linarith [mul_nonneg (le_max_left 0 L) (expNeg_nonneg 1 (totalEnergy α X ω))]
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (h.div (h.const_add 1) hd)

private theorem tendsto_resolventScalar_atTop {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    Tendsto (fun L => (resolventScalar L x : ℂ)) atTop (𝓝 1) := by
  have hd : Tendsto (fun L : ℝ => L + Real.exp x.toReal) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have h := tendsto_const_nhds (x := (1 : ℝ)) |>.sub
    (tendsto_const_nhds (x := Real.exp x.toReal) |>.div_atTop hd)
  apply Complex.continuous_ofReal.continuousAt.tendsto.comp
    (show Tendsto (fun L => resolventScalar L x) atTop (𝓝 (1 : ℝ)) from ?_)
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [resolventScalar_of_ne_top hL hx]
  field_simp [(by positivity : 0 < L + Real.exp x.toReal).ne']
  ring

/-- Removing the regularization recovers every vector at each finite mode cutoff. -/
theorem tendsto_finiteResolvent_atTop (hX : ∀ k, Measurable (X k)) (N : ℕ) (f : Lp ℂ 2 γ) :
    Tendsto (fun L => finiteResolvent γ α X hX N L f) atTop (𝓝 f) := by
  unfold finiteResolvent
  refine tendsto_lp_multipliers (n := fun _ => 1) f
    (fun L => Complex.continuous_ofReal.measurable.comp
      ((measurable_resolventScalar L).comp (measurable_partialEnergy hX N)))
    measurable_const (fun _ _ => norm_resolventScalar_le _ _) (by simp)
    (fun _ => multiply_ae ..) (ae_of_all _ fun ω => (one_mul (f ω)).symm) ?_
  exact ae_of_all _ fun ω => tendsto_resolventScalar_atTop (partialEnergy_ne_top N ω)

/-- The squared norm of the projected constant vacuum is the measure of its clock sublevel. -/
theorem sublevelProjection_vacuum_norm_sq [IsProbabilityMeasure γ]
    (hX : ∀ k, Measurable (X k)) {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    ‖sublevelProjection γ α X hX ℓ (Lp.const 2 γ (1 : ℂ))‖ ^ 2 =
      γ.real {ω | totalEnergy α X ω ≤ ENNReal.ofReal (Real.log ℓ)} := by
  have hS := measurableSet_sublevel (α := α) hX ℓ
  have hrep : sublevelProjection γ α X hX ℓ (Lp.const 2 γ (1 : ℂ)) =
      indicatorConstLp 2 hS (measure_ne_top γ _) (1 : ℂ) := by
    unfold sublevelProjection
    apply Lp.ext
    filter_upwards [multiply_ae (sublevel α X ℓ |>.indicator (fun _ => (1 : ℂ)))
      (measurable_const.indicator hS) (norm_indicator_one_le _) (Lp.const 2 γ (1 : ℂ)),
      Lp.coeFn_const (p := 2) (μ := γ) (1 : ℂ), indicatorConstLp_coeFn (μ := γ) (p := 2)
        (hs := hS) (hμs := measure_ne_top γ _) (c := (1 : ℂ))] with ω hω hconst hind
    rw [hind]
    simpa only [hconst, Function.const_apply, mul_one] using hω
  rw [hrep, norm_indicatorConstLp (by norm_num) ENNReal.ofNat_ne_top]
  simp only [norm_one, one_mul, ENNReal.toReal_ofNat]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (measureReal_nonneg)]
  congr 1
  ext ω
  simp [sublevel, hℓ]

/-- Finite mean gives strong recovery by the resolvents and projections and the vacuum bound. -/
theorem gaussian_focusing_operators_of_mass_lt_top [IsProbabilityMeasure γ]
    (hX : ∀ k, Measurable (X k)) (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ)
    (hm : mass α v < ⊤) :
    (∀ f : Lp ℂ 2 γ, Tendsto (fun L => resolventMultiplier γ α X hX L f) atTop (𝓝 f)) ∧
    (∀ f : Lp ℂ 2 γ, Tendsto (fun ℓ => sublevelProjection γ α X hX ℓ f) atTop (𝓝 f)) ∧
    ∀ ℓ : ℝ, 1 < ℓ → 1 - (mass α v).toReal / Real.log ℓ ≤
      ‖sublevelProjection γ α X hX ℓ (Lp.const 2 γ (1 : ℂ))‖ ^ 2 := by
  have hfinite := ae_totalEnergy_lt_top hX hl hm
  refine ⟨fun f => ?_, fun f => ?_, fun ℓ hℓ => ?_⟩
  · unfold resolventMultiplier
    refine tendsto_lp_multipliers (n := fun _ => 1) f
      (fun L => Complex.continuous_ofReal.measurable.comp
        ((measurable_resolventScalar L).comp (measurable_totalEnergy hX)))
      measurable_const (fun _ _ => norm_resolventScalar_le _ _) (by simp)
      (fun _ => multiply_ae ..) (ae_of_all _ fun ω => (one_mul (f ω)).symm) ?_
    exact hfinite.mono fun ω hω => tendsto_resolventScalar_atTop hω.ne
  · unfold sublevelProjection
    refine tendsto_lp_multipliers (n := fun _ => 1) f
      (fun ℓ => measurable_const.indicator (measurableSet_sublevel hX ℓ))
      measurable_const (fun _ => norm_indicator_one_le _) (by simp)
      (fun _ => multiply_ae ..) (ae_of_all _ fun ω => (one_mul (f ω)).symm) ?_
    filter_upwards [hfinite] with ω hω
    refine tendsto_const_nhds.congr' ?_
    have ht := ENNReal.tendsto_ofReal_nhds_top.mpr Real.tendsto_log_atTop
    filter_upwards [eventually_ge_atTop (1 : ℝ), (tendsto_order.1 ht).1 _ hω] with ℓ hℓ hlt
    exact (Set.indicator_of_mem (show ω ∈ sublevel α X ℓ from ⟨hℓ, hlt.le⟩) (fun _ => (1 : ℂ))).symm
  · rw [sublevelProjection_vacuum_norm_sq hX hℓ.le]
    exact vacuum_probability_lower_bound hX hl hm hℓ

/-- Infinite mean kills the full resolvents and all finite sublevel projections. -/
theorem gaussian_focusing_operators_of_mass_eq_top [IsProbabilityMeasure γ]
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X γ)
    (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ) (hm : mass α v = ⊤) :
    (∀ L : ℝ, resolventMultiplier γ α X hX L = 0) ∧
    (∀ ℓ : ℝ, sublevelProjection γ α X hX ℓ = 0) := by
  have htop := ae_totalEnergy_eq_top hX hi hl hm
  constructor <;> intro c <;> ext1 f <;> apply Lp.ext
  · have h := multiply_ae (γ := γ) (fun ω => (resolventScalar c (totalEnergy α X ω) : ℂ))
      (Complex.continuous_ofReal.measurable.comp
        ((measurable_resolventScalar c).comp (measurable_totalEnergy hX)))
      (fun _ => norm_resolventScalar_le _ _) f
    filter_upwards [htop, h, Lp.coeFn_zero ℂ 2 γ] with ω ht hω hzero
    change _ = (0 : Lp ℂ 2 γ) ω
    rw [hzero]
    rw [resolventMultiplier, hω]
    simp [ht, resolventScalar, expNeg]
  · have h := multiply_ae (γ := γ) ((sublevel α X c).indicator (fun _ => (1 : ℂ)))
      (measurable_const.indicator (measurableSet_sublevel hX c)) (norm_indicator_one_le _) f
    filter_upwards [htop, h, Lp.coeFn_zero ℂ 2 γ] with ω ht hω hzero
    have hn : ω ∉ sublevel α X c := fun h => ENNReal.ofReal_ne_top (top_le_iff.mp (ht ▸ h.2))
    change _ = (0 : Lp ℂ 2 γ) ω
    rw [hzero]
    rw [sublevelProjection, hω]
    simp [Set.indicator_of_notMem hn]

private def clockWeight (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then ⊤ else ENNReal.ofReal (Real.exp x.toReal)

/-- The domain of the full multiplication form `∫ exp(T) ‖f‖² dγ`. -/
def focusingFormDomain (γ : Measure Ω) (α : ℕ → ℝ≥0) (X : ℕ → Ω → ℝ) : Set (Lp ℂ 2 γ) :=
  {f | (∫⁻ ω, ‖f ω‖ₑ ^ 2 * clockWeight (totalEnergy α X ω) ∂γ) < ⊤}

/-- The full multiplication form has dense domain in the finite-mean phase. -/
theorem dense_focusingFormDomain [IsProbabilityMeasure γ] (hX : ∀ k, Measurable (X k))
    (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ) (hm : mass α v < ⊤) :
    Dense (focusingFormDomain γ α X) := by
  intro f
  apply mem_closure_of_tendsto (gaussian_focusing_operators_of_mass_lt_top hX hl hm |>.2.1 f)
  apply Eventually.of_forall
  intro ℓ
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have h := multiply_ae (γ := γ) ((sublevel α X ℓ).indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator (measurableSet_sublevel hX ℓ)) (norm_indicator_one_le _) f
  change (∫⁻ ω, ‖sublevelProjection γ α X hX ℓ f ω‖ₑ ^ 2 *
    clockWeight (totalEnergy α X ω) ∂γ) < ⊤
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (max 0 ℓ * ‖f ω‖ ^ 2) ∂γ := by
      apply lintegral_mono_ae
      filter_upwards [h] with ω hω
      change sublevelProjection γ α X hX ℓ f ω = _ at hω
      rw [hω]
      by_cases hs : ω ∈ sublevel α X ℓ
      · have hT : totalEnergy α X ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs.2
        have hlog := Real.log_nonneg hs.1
        have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs.2
        rw [ENNReal.toReal_ofReal hlog] at hbound
        have he := (Real.le_log_iff_exp_le (lt_of_lt_of_le zero_lt_one hs.1)).mp hbound
        rw [Set.indicator_of_mem hs, one_mul, clockWeight, ite_eq_right hT, ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _) 2, ← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal
          (mul_comm (max 0 ℓ) (‖f ω‖ ^ 2) ▸
            mul_le_mul_of_nonneg_left (he.trans (le_max_right 0 ℓ)) (sq_nonneg _))
      · simp [Set.indicator_of_notMem hs]
    _ < ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hf.const_mul (max 0 ℓ))
        (ae_of_all _ fun _ => by positivity)]
      exact ENNReal.ofReal_lt_top

/-- The full multiplication form has only the zero vector in the infinite-mean phase. -/
theorem focusingFormDomain_eq_singleton [IsProbabilityMeasure γ] (hX : ∀ k, Measurable (X k))
    (hi : iIndepFun X γ) (hl : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) γ)
    (hm : mass α v = ⊤) : focusingFormDomain γ α X = {0} := by
  ext f
  refine ⟨fun hf => ?_, ?_⟩
  · have ha : AEMeasurable (fun ω => ‖f ω‖ₑ ^ 2 * clockWeight (totalEnergy α X ω)) γ :=
      ((Lp.aestronglyMeasurable f).aemeasurable.enorm.pow_const _).mul
        ((measurable_const.piecewise (measurableSet_singleton (⊤ : ℝ≥0∞)) (by fun_prop) :
          Measurable clockWeight).comp (measurable_totalEnergy hX)).aemeasurable
    apply mem_singleton_iff.mpr
    apply Lp.ext
    filter_upwards [ae_lt_top' ha (show _ < ⊤ from hf).ne, ae_totalEnergy_eq_top hX hi hl hm,
      Lp.coeFn_zero ℂ 2 γ] with ω hω ht hzero
    simp only [ht, clockWeight, ↓reduceIte] at hω
    rw [hzero, Pi.zero_apply]
    by_contra hn
    rw [ENNReal.mul_top (pow_ne_zero _ (enorm_ne_zero.mpr hn))] at hω
    exact lt_irrefl _ hω
  · intro hf
    rcases mem_singleton_iff.mp hf with rfl
    change (∫⁻ ω, ‖(0 : Lp ℂ 2 γ) ω‖ₑ ^ 2 * clockWeight (totalEnergy α X ω) ∂γ) < ⊤
    have hzero : (fun ω => ‖(0 : Lp ℂ 2 γ) ω‖ₑ ^ 2 * clockWeight (totalEnergy α X ω))
        =ᵐ[γ] (fun _ => 0) := (Lp.coeFn_zero ℂ 2 γ).mono fun ω hω => by
      change ‖(0 : Lp ℂ 2 γ) ω‖ₑ ^ 2 * clockWeight (totalEnergy α X ω) = 0
      rw [hω]; simp
    rw [lintegral_congr_ae hzero, lintegral_zero]
    exact ENNReal.zero_lt_top

end D5.S3.Quantum.Analysis.NullConeGravity.GaussianFocusingPhaseTransition
