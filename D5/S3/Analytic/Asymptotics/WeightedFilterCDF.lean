/- GID: D5/S3/Analytic/Asymptotics/WeightedFilterCDF
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/WeightedFilterCDF
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Probability correction for the variable Robin tail weight. -/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.CDF
import Mathlib.Tactic

/-!
# Compact probability correction for the weight `(x + 1) / x²`

The paired integral inequality orders the two exponential tilts in opposite
directions. A Stieltjes measure realizes the resulting right-continuous CDF.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped Topology

noncomputable section

namespace WeightedFilterCDF

section Pairing

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α} [IsProbabilityMeasure ρ]

/-- Integrate the paired differences in each variable. The pointwise sign can
hold on any set of full measure. -/
theorem integral_mul_integral_le_of_pairwise {S : Set α} {f k : α → ℝ}
    (hS : ∀ᵐ a ∂ρ, a ∈ S)
    (hf : Integrable f ρ) (hk : Integrable k ρ)
    (hfk : Integrable (fun a => f a * k a) ρ)
    (hpair : ∀ a ∈ S, ∀ b ∈ S, 0 ≤ (f a - f b) * (k a - k b)) :
    (∫ a, f a ∂ρ) * (∫ a, k a ∂ρ) ≤ ∫ a, f a * k a ∂ρ := by
  let A := ∫ a, f a ∂ρ
  let B := ∫ a, k a ∂ρ
  let C := ∫ a, f a * k a ∂ρ
  have inner (a : α) :
      (∫ b, (f a - f b) * (k a - k b) ∂ρ) =
        f a * k a - f a * B - A * k a + C := by
    calc
      _ = ∫ b, f a * k a - f a * k b - f b * k a + f b * k b ∂ρ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun b => by ring)
      _ = _ := by
        have h₁ : Integrable (fun b => f a * k a - f a * k b) ρ :=
          (integrable_const (f a * k a)).sub (hk.const_mul (f a))
        have h₂ : Integrable (fun b => f a * k a - f a * k b - f b * k a) ρ :=
          h₁.sub (hf.mul_const (k a))
        rw [integral_add h₂ hfk, integral_sub h₁ (hf.mul_const (k a)),
          integral_sub (integrable_const (f a * k a)) (hk.const_mul (f a)),
          integral_const, integral_const_mul, integral_mul_const]
        simp [A, B, C]
  have outer : 0 ≤ ∫ a, f a * k a - f a * B - A * k a + C ∂ρ := by
    apply integral_nonneg_of_ae
    filter_upwards [hS] with a ha
    rw [← inner a]
    apply integral_nonneg_of_ae
    filter_upwards [hS] with b hb using hpair a ha b hb
  have h₁ : Integrable (fun a => f a * k a - f a * B) ρ := hfk.sub (hf.mul_const B)
  have h₂ : Integrable (fun a => f a * k a - f a * B - A * k a) ρ :=
    h₁.sub (hk.const_mul A)
  rw [integral_add h₂ (integrable_const C), integral_sub h₁ (hk.const_mul A),
    integral_sub hfk (hf.mul_const B), integral_mul_const, integral_const_mul,
    integral_const] at outer
  change 0 ≤ C - A * B - A * B + (ρ.real univ) • C at outer
  simp at outer
  change A * B ≤ C
  linarith

end Pairing

section OrderedTilt

variable {α : Type*} [MeasurableSpace α] [LinearOrder α]
variable {ρ : Measure α} [IsProbabilityMeasure ρ] {S : Set α}

/-- An antitone observable gains expectation under an antitone exponential
tilt. All order hypotheses are confined to a set of full measure. -/
theorem integral_le_integral_tilted_of_antitone {f p : α → ℝ}
    (hS : ∀ᵐ a ∂ρ, a ∈ S)
    (hf : Integrable f ρ) (hp : Integrable (fun a => exp (p a)) ρ)
    (hfp : Integrable (fun a => f a * exp (p a)) ρ)
    (hfanti : AntitoneOn f S) (hpanti : AntitoneOn p S) :
    (∫ a, f a ∂ρ) ≤ ∫ a, f a ∂(ρ.tilted p) := by
  have hpair (a : α) (ha : a ∈ S) (b : α) (hb : b ∈ S) :
      0 ≤ (f a - f b) * (exp (p a) - exp (p b)) := by
    rcases le_total a b with hab | hba
    · exact mul_nonneg (sub_nonneg.mpr (hfanti ha hb hab))
        (sub_nonneg.mpr (exp_le_exp.mpr (hpanti ha hb hab)))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hfanti hb ha hba))
        (sub_nonpos.mpr (exp_le_exp.mpr (hpanti hb ha hba)))
  have h := integral_mul_integral_le_of_pairwise hS hf hp hfp hpair
  rw [integral_tilted]
  simp_rw [smul_eq_mul, div_mul_eq_mul_div, mul_comm (exp _) (f _), integral_div]
  exact (le_div_iff₀ (integral_exp_pos hp)).2 h

/-- An antitone observable loses expectation under a monotone exponential
tilt. -/
theorem integral_tilted_le_integral_of_antitone {f p : α → ℝ}
    (hS : ∀ᵐ a ∂ρ, a ∈ S)
    (hf : Integrable f ρ) (hp : Integrable (fun a => exp (p a)) ρ)
    (hfp : Integrable (fun a => f a * exp (p a)) ρ)
    (hfanti : AntitoneOn f S) (hpmono : MonotoneOn p S) :
    (∫ a, f a ∂(ρ.tilted p)) ≤ ∫ a, f a ∂ρ := by
  have hpair (a : α) (ha : a ∈ S) (b : α) (hb : b ∈ S) :
      0 ≤ ((-f a) - (-f b)) * (exp (p a) - exp (p b)) := by
    rcases le_total a b with hab | hba
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (neg_le_neg (hfanti ha hb hab)))
        (sub_nonpos.mpr (exp_le_exp.mpr (hpmono ha hb hab)))
    · exact mul_nonneg (sub_nonneg.mpr (neg_le_neg (hfanti hb ha hba)))
        (sub_nonneg.mpr (exp_le_exp.mpr (hpmono hb ha hba)))
  have hn : Integrable (fun a => (-f) a * exp (p a)) ρ := by
    exact hfp.neg.congr (ae_of_all _ fun a => by simp [neg_mul])
  have h := integral_mul_integral_le_of_pairwise hS hf.neg hp hn hpair
  simp only [Pi.neg_apply, integral_neg, neg_mul, neg_le_neg_iff] at h
  rw [integral_tilted]
  simp_rw [smul_eq_mul, div_mul_eq_mul_div, mul_comm (exp _) (f _), integral_div]
  exact (div_le_iff₀ (integral_exp_pos hp)).2 h

end OrderedTilt

/-- At each threshold the CDF decreases under an increasing exponential tilt. -/
theorem cdf_tilted_le_cdf {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {S : Set ℝ}
    {p : ℝ → ℝ} (hS : ∀ᵐ a ∂ρ, a ∈ S)
    (hp : Integrable (fun a => exp (p a)) ρ) (hpmono : MonotoneOn p S) (s : ℝ) :
    cdf (ρ.tilted p) s ≤ cdf ρ s := by
  let f : ℝ → ℝ := (Iic s).indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator measurableSet_Iic
  have hfi : Integrable f ρ := (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hfp : Integrable (fun a => f a * exp (p a)) ρ := by
    apply hp.mono' (hfm.aestronglyMeasurable.mul hp.aestronglyMeasurable)
    apply ae_of_all
    intro a
    by_cases ha : a ∈ Iic s <;> simp [f, ha, (exp_pos (p a)).le]
  have hfa : Antitone f := by
    intro a b hab
    by_cases hb : b ∈ Iic s
    · have ha : a ∈ Iic s := hab.trans hb
      simp [f, ha, hb]
    · by_cases ha : a ∈ Iic s <;> simp [f, ha, hb]
  have h := integral_tilted_le_integral_of_antitone hS hfi hp hfp (hfa.antitoneOn S) hpmono
  have := isProbabilityMeasure_tilted hp
  rw [cdf_eq_real, cdf_eq_real]
  simpa only [f, integral_indicator measurableSet_Iic, integral_const, smul_eq_mul,
    mul_one, measureReal_restrict_apply_univ] using h

/-- The exponential moment of the compact input law. -/
def moment (μ : Measure ℝ) (y : ℝ) : ℝ := ∫ u, exp (y * u) ∂μ

/-- The input law tilted by the parameter `y`. -/
def inputTilt (μ : Measure ℝ) (y : ℝ) : Measure ℝ :=
  μ.tilted (fun u => y * u)

private theorem integrable_exp_input {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (y : ℝ) :
    Integrable (fun u => exp (y * u)) μ := by
  apply Integrable.of_bound (by fun_prop) (exp (|y| * h))
  filter_upwards [hμ] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  exact exp_le_exp.mpr <| (mul_le_mul_of_nonneg_right (le_abs_self y) hu.1).trans
    (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg y))

private theorem moment_one_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) {y : ℝ} (hy : 0 ≤ y) : 1 ≤ moment μ y := by
  calc
    1 = ∫ _u, (1 : ℝ) ∂μ := by simp
    _ ≤ moment μ y := by
      apply integral_mono_ae (integrable_const _) (integrable_exp_input hμ y)
      filter_upwards [hμ] with u hu
      exact Real.one_le_exp (mul_nonneg hy hu.1)

private theorem measurable_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (moment μ) := by
  have hm : StronglyMeasurable (fun z : ℝ × ℝ => exp (z.1 * z.2)) := by
    exact (by fun_prop : Measurable (fun z : ℝ × ℝ => exp (z.1 * z.2))).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

private theorem inputTilt_mem {μ : Measure ℝ} {h : ℝ} (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h)
    (y : ℝ) : ∀ᵐ u ∂inputTilt μ y, u ∈ Icc 0 h :=
  (tilted_absolutelyContinuous μ _).ae_le hμ

private theorem inputTilt_cdf_eq {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (y s : ℝ) :
    cdf (inputTilt μ y) s = (∫ u in Icc 0 s, exp (y * u) ∂μ) / moment μ y := by
  have : IsProbabilityMeasure (inputTilt μ y) :=
    isProbabilityMeasure_tilted (integrable_exp_input hμ y)
  have heq : Iic s =ᵐ[μ] Icc 0 s := by
    filter_upwards [hμ] with u hu
    exact propext ⟨fun hu' => ⟨hu.1, hu'⟩, fun hu' => hu'.2⟩
  have hnn : 0 ≤ ∫ u in Iic s, exp (y * u) / moment μ y ∂μ := by
    apply integral_nonneg
    intro u
    exact div_nonneg (exp_pos _).le (integral_exp_pos (integrable_exp_input hμ y)).le
  rw [cdf_eq_real, measureReal_def, inputTilt, tilted_apply_eq_ofReal_integral'
    _ measurableSet_Iic]
  change (ENNReal.ofReal (∫ u in Iic s, exp (y * u) / moment μ y ∂μ)).toReal = _
  rw [ENNReal.toReal_ofReal hnn, integral_div, setIntegral_congr_set heq]

private theorem measurable_inputTilt_cdf {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {h : ℝ} (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (s : ℝ) :
    Measurable (fun y => cdf (inputTilt μ y) s) := by
  simp_rw [inputTilt_cdf_eq hμ]
  have hm : StronglyMeasurable (fun z : ℝ × ℝ => exp (z.1 * z.2)) := by
    exact (by fun_prop : Measurable (fun z : ℝ × ℝ => exp (z.1 * z.2))).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := μ.restrict (Icc 0 s))).measurable.div
    (measurable_moment μ)

private theorem inputTilt_cdf_antitone {μ : Measure ℝ} [IsProbabilityMeasure μ] {h : ℝ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (s : ℝ) :
    Antitone (fun y => cdf (inputTilt μ y) s) := by
  intro a b hab
  have : IsProbabilityMeasure (inputTilt μ a) :=
    isProbabilityMeasure_tilted (integrable_exp_input hμ a)
  let p : ℝ → ℝ := fun u => (b - a) * u
  have hadd : (fun u => a * u) + p = (fun u => b * u) := by
    funext u
    simp only [Pi.add_apply, p]
    ring
  have hp : Integrable (fun u => exp (p u)) (inputTilt μ a) := by
    apply (integrable_tilted_iff (integrable_exp_input hμ a) _).mpr
    simpa only [← hadd, Pi.add_apply, exp_add, smul_eq_mul] using integrable_exp_input hμ b
  have hlaw : (inputTilt μ a).tilted p = inputTilt μ b := by
    rw [inputTilt, tilted_tilted (integrable_exp_input hμ a), hadd]
    rfl
  change cdf (inputTilt μ b) s ≤ cdf (inputTilt μ a) s
  rw [← hlaw]
  exact cdf_tilted_le_cdf (inputTilt_mem hμ a) hp
    (fun u _ v _ huv => mul_le_mul_of_nonneg_left huv (sub_nonneg.mpr hab)) s

/-- The measure `(1 + y) dy` on the nonnegative half-line. -/
def tailMeasure : Measure ℝ :=
  (volume.restrict (Ici 0)).withDensity (fun y => ENNReal.ofReal (1 + y))

/-- The normalization of the Laplace tilt of `tailMeasure`. -/
def weight (x : ℝ) : ℝ := (x + 1) / x ^ 2

private theorem tailMeasure_mem : ∀ᵐ y ∂tailMeasure, y ∈ Ici (0 : ℝ) :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ici)

private theorem integrable_tail_parts {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => exp (-x * y)) (Ici 0) ∧
      IntegrableOn (fun y : ℝ => y * exp (-x * y)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hx) 0,
    by simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
        (by norm_num) (by norm_num) hx⟩

private theorem integrable_tailExp {x : ℝ} (hx : 0 < x) :
    Integrable (fun y => exp (-x * y)) tailMeasure := by
  unfold tailMeasure
  apply (integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp)).mpr
  obtain ⟨h₁, h₂⟩ := integrable_tail_parts hx
  apply (h₁.add h₂).congr
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ici (a := (0 : ℝ)))]
    with y hy
  simp only [Pi.add_apply, smul_eq_mul, ENNReal.toReal_ofReal (by linarith [mem_Ici.mp hy] :
    0 ≤ 1 + y)]
  ring

private theorem integral_tailExp {x : ℝ} (hx : 0 < x) :
    (∫ y, exp (-x * y) ∂tailMeasure) = weight x := by
  rw [tailMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  have heq : (∫ y : ℝ in Ici 0, (ENNReal.ofReal (1 + y)).toReal * exp (-x * y)) =
      ∫ y : ℝ in Ici 0, exp (-x * y) + y * exp (-x * y) := by
    apply setIntegral_congr_fun measurableSet_Ici
    intro y hy
    dsimp only
    rw [ENNReal.toReal_ofReal (by linarith [mem_Ici.mp hy])]
    ring
  obtain ⟨h₁, h₂⟩ := integrable_tail_parts hx
  simp only [smul_eq_mul]
  rw [heq, integral_add h₁ h₂, integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (neg_lt_zero.mpr hx)]
  have hgamma : Gamma (2 : ℝ) = 1 := by
    simp
  have hmoment : (∫ y : ℝ in Ioi 0, y * exp (-x * y)) = (1 / x) ^ (2 : ℕ) := by
    have H := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hx
    rw [show (2 : ℝ) - 1 = 1 by norm_num, hgamma, mul_one] at H
    simp_rw [Real.rpow_one, ← neg_mul] at H
    rw [H]
    exact Real.rpow_natCast _ 2
  rw [hmoment]
  simp only [mul_zero, exp_zero, neg_div_neg_eq]
  unfold weight
  field_simp

private instance tailMeasure_neZero : NeZero tailMeasure := by
  constructor
  intro h
  have he := integral_tailExp (x := 1) (by norm_num)
  rw [h, integral_zero_measure] at he
  norm_num [weight] at he

/-- The Laplace tilt of `tailMeasure` by `x`. -/
def tailTilt (x : ℝ) : Measure ℝ := tailMeasure.tilted (fun y => -x * y)

private theorem tailTilt_mem (x : ℝ) : ∀ᵐ y ∂tailTilt x, y ∈ Ici (0 : ℝ) :=
  (tilted_absolutelyContinuous tailMeasure _).ae_le tailMeasure_mem

private theorem tailTilt_prob {x : ℝ} (hx : 0 < x) :
    IsProbabilityMeasure (tailTilt x) :=
  isProbabilityMeasure_tilted (integrable_tailExp hx)

private instance : SigmaFinite tailMeasure := by
  unfold tailMeasure
  infer_instance

private theorem tailTilt_expectation {x : ℝ} (hx : 0 < x) (f : ℝ → ℝ) :
    (∫ y, f y ∂tailTilt x) = (∫ y, exp (-x * y) * f y ∂tailMeasure) / weight x := by
  rw [tailTilt, integral_tilted]
  simp_rw [smul_eq_mul, div_mul_eq_mul_div, integral_div, integral_tailExp hx]

private theorem integrable_of_unit_bounds {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {f : ℝ → ℝ} (hf : Measurable f) (h₀ : ∀ y, 0 ≤ f y) (h₁ : ∀ y, f y ≤ 1) :
    Integrable f ρ :=
  Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg (h₀ y)] using h₁ y)

private theorem tailTilt_expectation_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : Measurable f) (h₀ : ∀ y, 0 ≤ f y) (h₁ : ∀ y, f y ≤ 1)
    (hfa : AntitoneOn f (Ici 0)) :
    (∫ y, f y ∂tailTilt a) ≤ ∫ y, f y ∂tailTilt b := by
  have := tailTilt_prob ha
  let p : ℝ → ℝ := fun y => -(b - a) * y
  have hadd : (fun y => -a * y) + p = (fun y => -b * y) := by
    funext y
    simp only [Pi.add_apply, p]
    ring
  have hp : Integrable (fun y => exp (p y)) (tailTilt a) := by
    apply (integrable_tilted_iff (integrable_tailExp ha) _).mpr
    simpa only [← hadd, Pi.add_apply, exp_add, smul_eq_mul] using
      integrable_tailExp (ha.trans_le hab)
  have hpanti : AntitoneOn p (Ici 0) := by
    intro y _ z _ hyz
    exact mul_le_mul_of_nonpos_left hyz (neg_nonpos.mpr (sub_nonneg.mpr hab))
  have hfp : Integrable (fun y => f y * exp (p y)) (tailTilt a) := by
    apply hp.mono' (hf.aestronglyMeasurable.mul hp.aestronglyMeasurable)
    apply ae_of_all
    intro y
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h₀ y) (exp_pos _).le)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (h₁ y) (exp_pos (p y)).le
  have hlaw : (tailTilt a).tilted p = tailTilt b := by
    rw [tailTilt, tilted_tilted (integrable_tailExp ha), hadd]
    rfl
  rw [← hlaw]
  exact integral_le_integral_tilted_of_antitone (tailTilt_mem a)
    (integrable_of_unit_bounds hf h₀ h₁) hp hfp hfa hpanti

/-- The mixture of the input CDFs with the parameter-dependent Laplace tilt. -/
def correctionCDF (μ : Measure ℝ) (t s : ℝ) : ℝ :=
  ∫ y, cdf (inputTilt μ y) s ∂tailTilt (t + s)

/-- Integrating the inverse input moment against the unnormalized Laplace law. -/
def kernel (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y, exp (-x * y) / moment μ y ∂tailMeasure

/-- The kernel with the density of the half-line measure written explicitly. -/
theorem kernel_eq_integral_Ici (μ : Measure ℝ) (x : ℝ) :
    kernel μ x = ∫ y : ℝ in Ici 0, (1 + y) * exp (-x * y) / moment μ y := by
  rw [kernel, tailMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
  apply setIntegral_congr_fun measurableSet_Ici
  intro y hy
  change (ENNReal.ofReal (1 + y)).toReal * (exp (-x * y) / moment μ y) = _
  rw [ENNReal.toReal_ofReal (by linarith [mem_Ici.mp hy]), ← mul_div_assoc]

section Correction

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {h t : ℝ}
variable (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h)

omit [IsProbabilityMeasure μ] in
private theorem correctionCDF_nonneg (s : ℝ) : 0 ≤ correctionCDF μ t s :=
  integral_nonneg (fun y => cdf_nonneg (inputTilt μ y) s)

include hμ

private theorem correctionCDF_eq_zero {s : ℝ} (hs : s < 0) : correctionCDF μ t s = 0 := by
  unfold correctionCDF
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro y
  have : IsProbabilityMeasure (inputTilt μ y) :=
    isProbabilityMeasure_tilted (integrable_exp_input hμ y)
  have hs_ae : ∀ᵐ u ∂inputTilt μ y, u ∉ Iic s := by
    filter_upwards [inputTilt_mem hμ y] with u hu
    exact fun hx => (not_le_of_gt hs) (hu.1.trans hx)
  have hnull : inputTilt μ y (Iic s) = 0 := by
    have heq : {u : ℝ | ¬¬ u ∈ Iic s} = Iic s := by
      ext u
      exact not_not
    rw [← heq]
    exact ae_iff.mp hs_ae
  change cdf (inputTilt μ y) s = 0
  rw [cdf_eq_real, measureReal_def, hnull, ENNReal.toReal_zero]

private theorem correctionCDF_eq_one (ht : 0 < t) {s : ℝ} (hs : h ≤ s) :
    correctionCDF μ t s = 1 := by
  have hsn : 0 ≤ s := by
    obtain ⟨u, hu⟩ := hμ.exists
    exact hu.1.trans (hu.2.trans hs)
  have := tailTilt_prob (show 0 < t + s by linarith)
  unfold correctionCDF
  calc
    _ = ∫ _y, (1 : ℝ) ∂tailTilt (t + s) := by
      apply integral_congr_ae
      apply ae_of_all
      intro y
      have : IsProbabilityMeasure (inputTilt μ y) :=
        isProbabilityMeasure_tilted (integrable_exp_input hμ y)
      have hone : inputTilt μ y (Iic s) = 1 := by
        rw [← measure_univ (μ := inputTilt μ y),
          ← ae_mem_iff_measure_eq measurableSet_Iic.nullMeasurableSet]
        filter_upwards [inputTilt_mem hμ y] with u hu using hu.2.trans hs
      change cdf (inputTilt μ y) s = 1
      rw [cdf_eq_real, measureReal_def, hone, ENNReal.toReal_one]
    _ = 1 := by simp

/-- The CDF grows both by enlarging its interval and by tilting toward smaller parameters. -/
theorem correctionCDF_mono (ht : 0 < t) : Monotone (correctionCDF μ t) := by
  intro a b hab
  by_cases ha : 0 ≤ a
  · have ha' : 0 < t + a := by linarith
    have := tailTilt_prob ha'
    let f : ℝ → ℝ := fun y => cdf (inputTilt μ y) a
    let f' : ℝ → ℝ := fun y => cdf (inputTilt μ y) b
    calc
      correctionCDF μ t a = ∫ y, f y ∂tailTilt (t + a) := rfl
      _ ≤ ∫ y, f' y ∂tailTilt (t + a) := by
        apply integral_mono
        · exact integrable_of_unit_bounds (measurable_inputTilt_cdf hμ a)
            (fun y => cdf_nonneg _ _) (fun y => cdf_le_one _ _)
        · exact integrable_of_unit_bounds (measurable_inputTilt_cdf hμ b)
            (fun y => cdf_nonneg _ _) (fun y => cdf_le_one _ _)
        · exact fun y => monotone_cdf _ hab
      _ ≤ correctionCDF μ t b :=
        tailTilt_expectation_mono ha' (add_le_add_right hab t)
          (measurable_inputTilt_cdf hμ b) (fun y => cdf_nonneg _ _)
          (fun y => cdf_le_one _ _) ((inputTilt_cdf_antitone hμ b).antitoneOn _)
  · rw [correctionCDF_eq_zero hμ (lt_of_not_ge ha)]
    exact correctionCDF_nonneg b

theorem correctionCDF_le_one (ht : 0 < t) (s : ℝ) : correctionCDF μ t s ≤ 1 := by
  calc
    correctionCDF μ t s ≤ correctionCDF μ t (max s h) :=
      correctionCDF_mono hμ ht (le_max_left _ _)
    _ = 1 := correctionCDF_eq_one hμ ht (le_max_right _ _)

/-- Right continuity follows by domination by the Laplace weight at the base parameter. -/
theorem correctionCDF_rightContinuous (ht : 0 < t) (s : ℝ) :
    ContinuousWithinAt (correctionCDF μ t) (Ici s) s := by
  by_cases hs : s < 0
  · unfold ContinuousWithinAt
    have hnear : ∀ᶠ r in 𝓝[Ici s] s, r ∈ Iio (0 : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)
    rw [correctionCDF_eq_zero hμ hs]
    exact tendsto_const_nhds.congr' (hnear.mono fun r hr => (correctionCDF_eq_zero hμ hr).symm)
  · have hs₀ : 0 ≤ s := le_of_not_gt hs
    have hnear : ∀ᶠ r in 𝓝[Ici s] s, r ∈ Ici s := self_mem_nhdsWithin
    have hlimit :
        Tendsto (fun r => ∫ y, exp (-(t + r) * y) * cdf (inputTilt μ y) r ∂tailMeasure)
          (𝓝[Ici s] s)
          (𝓝 (∫ y, exp (-(t + s) * y) * cdf (inputTilt μ y) s ∂tailMeasure)) := by
      apply tendsto_integral_filter_of_dominated_convergence (fun y => exp (-t * y))
      · apply Eventually.of_forall
        intro r
        exact (show Measurable (fun y : ℝ => exp (-(t + r) * y)) by fun_prop).aestronglyMeasurable.mul
          (measurable_inputTilt_cdf hμ r).aestronglyMeasurable
      · filter_upwards [hnear] with r hr
        filter_upwards [tailMeasure_mem] with y hy
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le (cdf_nonneg _ _))]
        calc
          _ ≤ exp (-(t + r) * y) * 1 :=
            mul_le_mul_of_nonneg_left (cdf_le_one _ _) (exp_pos _).le
          _ ≤ exp (-t * y) := by
            rw [mul_one]
            exact exp_le_exp.mpr (mul_le_mul_of_nonneg_right
              (by linarith [mem_Ici.mp hr]) (mem_Ici.mp hy))
      · exact integrable_tailExp ht
      · apply ae_of_all
        intro y
        exact (show ContinuousWithinAt (fun r : ℝ => exp (-(t + r) * y)) (Ici s) s by
          fun_prop).tendsto.mul ((cdf (inputTilt μ y)).right_continuous s).tendsto
    have hws : weight (t + s) ≠ 0 := by unfold weight; positivity
    have hw : ContinuousWithinAt (fun r : ℝ => weight (t + r)) (Ici s) s := by
      unfold weight
      apply ContinuousWithinAt.div <;> first | fun_prop | positivity
    have hquot := hlimit.div hw.tendsto hws
    rw [← tailTilt_expectation (show 0 < t + s by linarith)] at hquot
    exact hquot.congr' (hnear.mono fun r hr =>
      (tailTilt_expectation (show 0 < t + r by linarith [mem_Ici.mp hr])
        (fun y => cdf (inputTilt μ y) r)).symm)

/-- Fubini converts the mixture into the compact weighted kernel formula. -/
theorem correctionCDF_eq_kernel (ht : 0 < t) {s : ℝ} (hs : 0 ≤ s) :
    correctionCDF μ t s = (∫ u in Icc 0 s, kernel μ (t + s - u) ∂μ) / weight (t + s) := by
  rw [correctionCDF, tailTilt_expectation (show 0 < t + s by linarith)]
  congr 1
  let f : ℝ → ℝ → ℝ := fun u y => exp (-(t + s - u) * y) / moment μ y
  have hm : Measurable (Function.uncurry f) :=
    (show Measurable (fun z : ℝ × ℝ => exp (-(t + s - z.1) * z.2)) by fun_prop).div
      ((measurable_moment μ).comp measurable_snd)
  have hbound (u y : ℝ) (hu : u ∈ Icc 0 s) (hy : y ∈ Ici 0) :
      ‖f u y‖ ≤ exp (-t * y) := by
    have hm₁ := moment_one_le hμ (mem_Ici.mp hy)
    have hm₀ : 0 < moment μ y := zero_lt_one.trans_le hm₁
    change |exp (-(t + s - u) * y) / moment μ y| ≤ _
    rw [abs_of_nonneg (div_nonneg (exp_pos _).le hm₀.le)]
    calc
      _ ≤ exp (-(t+s-u) * y) := (div_le_iff₀ hm₀).mpr <| by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hm₁ (exp_pos _).le
      _ ≤ _ := exp_le_exp.mpr <| mul_le_mul_of_nonneg_right
        (by linarith [hu.2]) (mem_Ici.mp hy)
  let μs := μ.restrict (Icc 0 s)
  have hμs : ∀ᵐ u ∂μs, u ∈ Icc 0 s := ae_restrict_mem measurableSet_Icc
  have hint : Integrable (Function.uncurry f) (μs.prod tailMeasure) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [hμs] with u hu
      apply (integrable_tailExp ht).mono'
        ((hm.comp measurable_prodMk_left) : Measurable (fun y => f u y)).aestronglyMeasurable
      filter_upwards [tailMeasure_mem] with y hy using hbound u y hu hy
    · have hmf : StronglyMeasurable (fun z : ℝ × ℝ => ‖Function.uncurry f z‖) :=
        hm.stronglyMeasurable.norm
      apply Integrable.of_bound hmf.integral_prod_right'.aestronglyMeasurable
        (∫ y, exp (-t * y) ∂tailMeasure)
      filter_upwards [hμs] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      apply integral_mono_ae
      · apply (integrable_tailExp ht).mono'
          ((hm.comp measurable_prodMk_left) :
            Measurable (fun y => f u y)).aestronglyMeasurable.norm
        filter_upwards [tailMeasure_mem] with y hy
        change ‖‖f u y‖‖ ≤ exp (-t * y)
        simpa only [norm_norm] using hbound u y hu hy
      · exact integrable_tailExp ht
      · filter_upwards [tailMeasure_mem] with y hy using hbound u y hu hy
  change _ = ∫ u, ∫ y, f u y ∂tailMeasure ∂μs
  rw [integral_integral_swap hint]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  change exp (-(t+s) * y) * cdf (inputTilt μ y) s = ∫ u, f u y ∂μs
  rw [inputTilt_cdf_eq hμ, ← mul_div_assoc, ← integral_const_mul, ← integral_div]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  change exp (-(t + s) * y) * exp (y * u) / moment μ y =
    exp (-(t + s - u) * y) / moment μ y
  rw [← exp_add]
  congr 2
  ring

/-- The compact correction measure is a probability on `[0,h]` with the stated
weighted CDF, including the lower endpoint, where the law may have an atom. -/
theorem exists_compact_probability_correction (ht : 0 < t) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Icc 0 h)ᶜ = 0 ∧
      ∀ s : ℝ, 0 ≤ s →
        ν.real (Iic s) = (∫ u in Icc 0 s, kernel μ (t + s - u) ∂μ) / weight (t + s) := by
  let F : StieltjesFunction ℝ :=
    ⟨correctionCDF μ t, correctionCDF_mono hμ ht, correctionCDF_rightContinuous hμ ht⟩
  have hbot : Tendsto F atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact (eventually_lt_atBot 0).mono fun s hs => (correctionCDF_eq_zero hμ hs).symm
  have htop : Tendsto F atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    exact (eventually_ge_atTop h).mono fun s hs => (correctionCDF_eq_one hμ ht hs).symm
  have hprob : IsProbabilityMeasure F.measure := by
    constructor
    rw [F.measure_univ hbot htop, sub_zero, ENNReal.ofReal_one]
  have hleft : F.measure (Iio 0) = 0 := by
    have hlim : Tendsto F (𝓝[Iio 0] 0) (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      have hnear : ∀ᶠ s in 𝓝[Iio 0] (0 : ℝ), s ∈ Iio (0 : ℝ) := self_mem_nhdsWithin
      exact hnear.mono fun s hs => (correctionCDF_eq_zero hμ hs).symm
    rw [F.measure_Iio hbot, leftLim_eq_of_tendsto hlim, sub_zero, ENNReal.ofReal_zero]
  have hright : F.measure (Ioi h) = 0 := by
    rw [F.measure_Ioi htop]
    change ENNReal.ofReal (1 - correctionCDF μ t h) = 0
    rw [correctionCDF_eq_one hμ ht le_rfl, sub_self, ENNReal.ofReal_zero]
  refine ⟨F.measure, hprob, ?_, ?_⟩
  · have hcompl : (Icc (0 : ℝ) h)ᶜ = Iio 0 ∪ Ioi h := by
      ext x
      simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le]
    rw [hcompl]
    exact measure_union_null hleft hright
  · intro s hs
    rw [measureReal_def, F.measure_Iic hbot, sub_zero,
      ENNReal.toReal_ofReal (correctionCDF_nonneg s)]
    exact correctionCDF_eq_kernel hμ ht hs

end Correction

section WeightedTailAverage

/-- The kernel is measurable in the start of the tail. -/
theorem measurable_kernel (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (kernel μ) := by
  have hm : Measurable (fun z : ℝ × ℝ => exp (-z.1 * z.2) / moment μ z.2) :=
    (show Measurable (fun z : ℝ × ℝ => exp (-z.1 * z.2)) by fun_prop).div
      ((measurable_moment μ).comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := tailMeasure)).measurable

/-- On the positive half-line, the compact input's kernel is bounded by the Robin weight. -/
theorem kernel_nonneg_le_weight {μ : Measure ℝ} [IsProbabilityMeasure μ] {h x : ℝ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (hx : 0 < x) :
    0 ≤ kernel μ x ∧ kernel μ x ≤ weight x := by
  let f : ℝ → ℝ := fun y => exp (-x * y) / moment μ y
  have hm : Measurable f :=
    (show Measurable (fun y : ℝ => exp (-x * y)) by fun_prop).div (measurable_moment μ)
  have hb : ∀ᵐ y ∂tailMeasure, 0 ≤ f y ∧ f y ≤ exp (-x * y) := by
    filter_upwards [tailMeasure_mem] with y hy
    have hM := moment_one_le hμ (mem_Ici.mp hy)
    have hMpos := zero_lt_one.trans_le hM
    refine ⟨div_nonneg (exp_pos _).le hMpos.le, (div_le_iff₀ hMpos).mpr ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hM (exp_pos (-x * y)).le
  have hi := integrable_tailExp hx
  have hf : Integrable f tailMeasure := by
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards [hb] with y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2
  change 0 ≤ (∫ y, f y ∂tailMeasure) ∧ (∫ y, f y ∂tailMeasure) ≤ weight x
  rw [← integral_tailExp hx]
  exact ⟨integral_nonneg_of_ae (hb.mono fun _ hy => hy.1),
    integral_mono_ae hf hi (hb.mono fun _ hy => hy.2)⟩

private theorem weight_le_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    weight b ≤ weight a := by
  have hb := ha.trans_le hab
  rw [← integral_tailExp hb, ← integral_tailExp ha]
  refine integral_mono_ae (integrable_tailExp hb) (integrable_tailExp ha) ?_
  filter_upwards [tailMeasure_mem] with y hy
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hab) (mem_Ici.mp hy))

/-- A single compact correction law gives the exact weighted average for every
measurable, absolutely integrable tail at the same base point. -/
theorem exists_compact_probability_weighted_tail_average
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {h t : ℝ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (ht : 0 < t) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Icc 0 h)ᶜ = 0 ∧
      ∀ (r : ℝ → ℝ), Measurable r → IntegrableOn r (Ici t) →
        (∫ u, (∫ a in Ici (t + u), weight a * r a) ∂ν) =
          ∫ v in Ici (0 : ℝ), kernel μ (t + v) * (∫ u, r (t + v + u) ∂μ) := by
  obtain ⟨ν, hνprob, hνsupp, hνcdf⟩ := exists_compact_probability_correction hμ ht
  refine ⟨ν, hνprob, hνsupp, ?_⟩
  letI : IsProbabilityMeasure ν := hνprob
  have hν : ∀ᵐ u ∂ν, u ∈ Icc 0 h := mem_ae_iff.mpr hνsupp
  have hμnonneg : ∀ᵐ u ∂μ, u ∈ Ici (0 : ℝ) := hμ.mono fun _ hu => hu.1
  have weight_pos (x : ℝ) (hx : 0 < x) : 0 < weight x := by
    unfold weight
    positivity
  intro r hrm hr
  let tail := (volume : Measure ℝ).restrict (Ici t)
  let triangle : Set (ℝ × ℝ) := {z | 0 ≤ z.2 ∧ t + z.2 ≤ z.1}
  have htriangle : MeasurableSet triangle := by
    change MeasurableSet ({z : ℝ × ℝ | 0 ≤ z.2} ∩ {z | t + z.2 ≤ z.1})
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le (measurable_const.add measurable_snd) measurable_fst)
  have htriangle_base : triangle ⊆ Ici t ×ˢ (univ : Set ℝ) := by
    intro z hz
    change 0 ≤ z.2 ∧ t + z.2 ≤ z.1 at hz
    exact Set.mem_prod.mpr ⟨mem_Ici.mpr (by linarith [hz.1, hz.2]), mem_univ _⟩
  let leftIntegrand : ℝ × ℝ → ℝ := fun z => weight z.1 * r z.1
  let rightIntegrand : ℝ × ℝ → ℝ := fun z => kernel μ (z.1 - z.2) * r z.1
  have hleftm : Measurable leftIntegrand :=
    ((show Measurable weight by unfold weight; fun_prop).comp measurable_fst).mul
      (hrm.comp measurable_fst)
  have hrightm : Measurable rightIntegrand :=
    ((measurable_kernel μ).comp (measurable_fst.sub measurable_snd)).mul
      (hrm.comp measurable_fst)
  have hr_tail : Integrable r tail := hr
  have integrable_cut (η : Measure ℝ) [IsFiniteMeasure η] {f : ℝ × ℝ → ℝ}
      (hf : Measurable f) (hbound : ∀ z ∈ triangle, ‖f z‖ ≤ weight t * ‖r z.1‖) :
      Integrable (triangle.indicator f) (tail.prod η) := by
    apply ((hr_tail.norm.const_mul (weight t)).comp_fst η).mono'
      (hf.indicator htriangle).aestronglyMeasurable
    apply ae_of_all
    intro z
    by_cases hz : z ∈ triangle
    · rw [indicator_of_mem hz]
      exact hbound z hz
    · rw [indicator_of_notMem hz, norm_zero]
      exact mul_nonneg (weight_pos t ht).le (norm_nonneg _)
  have hleft : Integrable (triangle.indicator leftIntegrand) (tail.prod ν) := by
    apply integrable_cut ν hleftm
    intro z hz
    have hz1 : t ≤ z.1 := (Set.mem_prod.mp (htriangle_base hz)).1
    change ‖weight z.1 * r z.1‖ ≤ weight t * ‖r z.1‖
    rw [norm_mul, Real.norm_eq_abs (weight z.1), abs_of_pos (weight_pos _ (ht.trans_le hz1))]
    exact mul_le_mul_of_nonneg_right (weight_le_of_pos ht hz1) (norm_nonneg _)
  have hright : Integrable (triangle.indicator rightIntegrand) (tail.prod μ) := by
    apply integrable_cut μ hrightm
    intro z hz
    change 0 ≤ z.2 ∧ t + z.2 ≤ z.1 at hz
    have hz1 : t ≤ z.1 - z.2 := by linarith [hz.2]
    obtain ⟨h₀, h₁⟩ := kernel_nonneg_le_weight hμ (ht.trans_le hz1)
    change ‖kernel μ (z.1 - z.2) * r z.1‖ ≤ weight t * ‖r z.1‖
    rw [norm_mul, Real.norm_eq_abs (kernel μ (z.1 - z.2)), abs_of_nonneg h₀]
    exact mul_le_mul_of_nonneg_right (h₁.trans (weight_le_of_pos ht hz1)) (norm_nonneg _)

  -- Compute the sections in each order, retaining the closed endpoints.
  have hleft_sections :
      (∫ u, (∫ a in Ici (t + u), weight a * r a) ∂ν) =
        ∫ u, ∫ a, triangle.indicator leftIntegrand (a, u) ∂tail ∂ν := by
    apply integral_congr_ae
    filter_upwards [hν] with u hu
    have hpre : (fun a : ℝ => (a, u)) ⁻¹' triangle = Ici (t + u) := by
      ext a
      change (0 ≤ u ∧ t + u ≤ a) ↔ t + u ≤ a
      simp only [hu.1, true_and]
    simp_rw [← indicator_comp_right (fun a : ℝ => (a, u)), hpre,
      integral_indicator measurableSet_Ici]
    change _ = ∫ a, weight a * r a ∂((volume.restrict (Ici t)).restrict (Ici (t + u)))
    rw [Measure.restrict_restrict_of_subset (Ici_subset_Ici.mpr (by linarith [hu.1]))]

  have hsections (a : ℝ) :
      (fun u : ℝ => (a, u)) ⁻¹' triangle = Icc 0 (a - t) := by
    ext u
    change (0 ≤ u ∧ t + u ≤ a) ↔ 0 ≤ u ∧ u ≤ a - t
    rw [le_sub_iff_add_le, add_comm u t]
  have hcdf_average :
      (∫ a, ∫ u, triangle.indicator leftIntegrand (a, u) ∂ν ∂tail) =
        ∫ a, ∫ u, triangle.indicator rightIntegrand (a, u) ∂μ ∂tail := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ici (a := t))] with a ha
    have ha' : t ≤ a := mem_Ici.mp ha
    have hνsets : Icc 0 (a - t) =ᵐ[ν] Iic (a - t) := by
      filter_upwards [hν] with u hu
      exact propext ⟨fun hu' => hu'.2, fun hu' => ⟨hu.1, hu'⟩⟩
    have hat : t + (a - t) = a := by ring
    have hcdf : ν.real (Iic (a - t)) =
        (∫ u in Icc 0 (a - t), kernel μ (a - u) ∂μ) / weight a := by
      simpa only [hat] using hνcdf (a - t) (sub_nonneg.mpr ha')
    simp_rw [← indicator_comp_right (fun u : ℝ => (a, u)), hsections]
    change (∫ u, (Icc 0 (a - t)).indicator (fun _ => weight a * r a) u ∂ν) =
      ∫ u, (Icc 0 (a - t)).indicator (fun u => kernel μ (a - u) * r a) u ∂μ
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, integral_indicator measurableSet_Icc,
      integral_mul_const, measureReal_congr hνsets, hcdf, ← mul_assoc,
      div_mul_cancel₀ _ (weight_pos _ (ht.trans_le ha')).ne']

  -- Translation by the displacement sends the half-line product to the triangle.
  let shift : ℝ × ℝ → ℝ × ℝ := fun z => (z.1 + z.2, z.2)
  have hpre_shift : shift ⁻¹' triangle = Ici t ×ˢ Ici (0 : ℝ) := by
    ext z
    change (0 ≤ z.2 ∧ t + z.2 ≤ z.1 + z.2) ↔ t ≤ z.1 ∧ 0 ≤ z.2
    rw [add_le_add_iff_right, and_comm]
  have hshift : MeasurePreserving shift (tail.prod μ) ((volume.prod μ).restrict triangle) := by
    have h := (measurePreserving_add_prod (volume : Measure ℝ) μ).restrict_preimage htriangle
    change MeasurePreserving shift ((volume.prod μ).restrict (shift ⁻¹' triangle))
      ((volume.prod μ).restrict triangle) at h
    rw [hpre_shift, ← Measure.prod_restrict,
      Measure.restrict_eq_self_of_ae_mem hμnonneg] at h
    exact h

  have hrestriction : (tail.prod μ).restrict triangle = (volume.prod μ).restrict triangle := by
    change (((volume : Measure ℝ).restrict (Ici t)).prod μ).restrict triangle = _
    rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_restrict_of_subset htriangle_base]
  have hright_triangle : Integrable rightIntegrand ((volume.prod μ).restrict triangle) := by
    rw [← hrestriction]
    exact (integrable_indicator_iff htriangle).mp hright
  have hright_shift : Integrable (rightIntegrand ∘ shift) (tail.prod μ) :=
    hshift.integrable_comp_of_integrable hright_triangle
  have htranslated :
      (∫ a, ∫ u, triangle.indicator rightIntegrand (a, u) ∂μ ∂tail) =
        ∫ b in Ici t, kernel μ b * (∫ u, r (b + u) ∂μ) := by
    calc
      _ = ∫ z, triangle.indicator rightIntegrand z ∂tail.prod μ := (integral_prod _ hright).symm
      _ = ∫ z, rightIntegrand z ∂((volume.prod μ).restrict triangle) := by
        rw [integral_indicator htriangle, hrestriction]
      _ = ∫ z, (rightIntegrand ∘ shift) z ∂tail.prod μ := by
        rw [← hshift.map_eq]
        exact integral_map_of_stronglyMeasurable hshift.measurable hrightm.stronglyMeasurable
      _ = ∫ b in Ici t, kernel μ b * (∫ u, r (b + u) ∂μ) := by
        rw [integral_prod _ hright_shift]
        simp only [rightIntegrand, shift, Function.comp_apply, add_sub_cancel_right, integral_const_mul, tail]
  let avg : ℝ → ℝ := fun b => kernel μ b * (∫ u, r (b + u) ∂μ)
  have hpre_base : (fun v : ℝ => t + v) ⁻¹' Ici t = Ici (0 : ℝ) := by
    ext v
    change t ≤ t + v ↔ 0 ≤ v
    constructor <;> intro hv <;> linarith
  have hbase :
      (∫ b in Ici t, avg b) = ∫ v in Ici (0 : ℝ), avg (t + v) := by
    have hs := (measurePreserving_add_left (volume : Measure ℝ) t).setIntegral_preimage_emb
      (Homeomorph.addLeft t).measurableEmbedding avg (Ici t)
    simpa only [hpre_base] using hs.symm

  calc
    _ = ∫ u, ∫ a, triangle.indicator leftIntegrand (a, u) ∂tail ∂ν := hleft_sections
    _ = ∫ a, ∫ u, triangle.indicator leftIntegrand (a, u) ∂ν ∂tail :=
      (integral_integral_swap
        (f := fun a u => triangle.indicator leftIntegrand (a, u)) hleft).symm
    _ = ∫ a, ∫ u, triangle.indicator rightIntegrand (a, u) ∂μ ∂tail := hcdf_average
    _ = ∫ b in Ici t, avg b := htranslated
    _ = _ := hbase

end WeightedTailAverage

end WeightedFilterCDF
