/- GID: D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/GaussianCoshAveraging
   mirror-E: none(waiver:symbolic-relative-integral-limit)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral]
   utility: none
   digest: Relative Gaussian averaging of the actual clipped cosh kernel. -/

import D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open StatLean.HypothesisTesting
open D5.S3.TotalVariation.Asymptotics.GaussianCoshKernel

namespace D5.S3.TotalVariation.Asymptotics.GaussianCoshAveraging

/-- The exact coefficient of the local three-halves-power term. -/
def coshCoefficient (q : ℝ) : ℝ :=
  4 * Real.sqrt 2 * stdNormalPDF 0 / (3 * q)

/-- The affine displacement, including the Gaussian square-completion shift. -/
def affineOffset (b τ v : ℝ) : ℝ := b * (v - τ) - b ^ 2 / 2

/-- The actual Gaussian three-halves positive-part moment. -/
def positiveMoment (b τ : ℝ) : ℝ :=
  ∫ v : ℝ, stdNormalPDF v * max (affineOffset b τ v) 0 ^ (3 / 2 : ℝ)

/-- The actual averaged Gaussian-cosh kernel. -/
def averagedCosh (q b τ : ℝ) : ℝ :=
  ∫ v : ℝ, stdNormalPDF v * gaussianCoshIntegral q (affineOffset b τ v)

private theorem phi_pos (v : ℝ) : 0 < stdNormalPDF v := by
  unfold stdNormalPDF
  positivity

private theorem coefficient_pos {q : ℝ} (hq : 0 < q) : 0 < coshCoefficient q := by
  have hphi := phi_pos 0
  unfold coshCoefficient
  exact div_pos (by positivity) (by positivity)

private theorem kernel_nonneg (q d : ℝ) : 0 ≤ gaussianCoshIntegral q d :=
  integral_nonneg fun u => mul_nonneg (phi_pos u).le (le_max_right _ _)

private theorem kernel_le_exp (q d : ℝ) : gaussianCoshIntegral q d ≤ Real.exp d := by
  calc
    _ ≤ ∫ u : ℝ, stdNormalPDF u * Real.exp d := by
      apply integral_mono (kernel_integrable q d) (integrable_stdNormalPDF.mul_const _)
      intro u
      apply mul_le_mul_of_nonneg_left _ (phi_pos u).le
      exact max_le (by linarith [Real.cosh_pos (q * u)]) (Real.exp_pos d).le
    _ = _ := by
      rw [integral_mul_const]
      simp_rw [stdNormalPDF_eq_gaussianPDFReal]
      rw [ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by norm_num), one_mul]

private theorem kernel_zero {q d : ℝ} (hd : d ≤ 0) : gaussianCoshIntegral q d = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  have he : Real.exp d ≤ 1 := by simpa using Real.exp_le_exp.mpr hd
  rw [max_eq_right (by linarith [Real.one_le_cosh (q * u)]), mul_zero]
  rfl

private theorem kernel_measurable (q : ℝ) : Measurable (gaussianCoshIntegral q) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      stdNormalPDF p.2 * max (Real.exp p.1 - Real.cosh (q * p.2)) 0) :=
    (continuous_stdNormalPDF.comp continuous_snd).mul (by fun_prop)
  exact hc.stronglyMeasurable.integral_prod_right'.measurable

private theorem moment_power_le_exp {d : ℝ} (hd : 0 ≤ d) :
    d ^ (3 / 2 : ℝ) ≤ 4 * Real.exp d := by
  have hp : d ^ (3 / 2 : ℝ) ≤ 1 + d ^ 2 := by
    by_cases h : d ≤ 1
    · exact (Real.rpow_le_one hd h (by norm_num)).trans (by nlinarith [sq_nonneg d])
    · have h1 : 1 ≤ d := le_of_lt (lt_of_not_ge h)
      calc
        _ ≤ d ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        _ ≤ _ := by rw [Real.rpow_two]; linarith
  have h := Real.add_one_le_exp (d / 2)
  have hs : (1 + d / 2) ^ 2 ≤ (Real.exp (d / 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have he : (Real.exp (d / 2)) ^ 2 = Real.exp d := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hs
  nlinarith

private theorem tilted_density_integrable (b τ : ℝ) :
    Integrable (fun v : ℝ => stdNormalPDF v * Real.exp (affineOffset b τ v)) := by
  have hi := (integrable_exp_neg_mul_sq (b := (1 / 4 : ℝ)) (by norm_num)).const_mul
    (Real.exp (b ^ 2 - b * τ - b ^ 2 / 2) / Real.sqrt (2 * Real.pi))
  refine hi.mono' ?_ ?_
  · exact (continuous_stdNormalPDF.mul (by unfold affineOffset; fun_prop)).aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (phi_pos v) (Real.exp_pos _))]
  unfold stdNormalPDF affineOffset
  rw [div_mul_eq_mul_div, ← Real.exp_add, div_mul_eq_mul_div, ← Real.exp_add]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (v / 2 - b)]

private theorem outer_integrable (q b τ : ℝ) :
    Integrable (fun v : ℝ => stdNormalPDF v * gaussianCoshIntegral q (affineOffset b τ v)) := by
  refine (tilted_density_integrable b τ).mono' ?_ ?_
  · exact (continuous_stdNormalPDF.measurable.mul
      ((kernel_measurable q).comp (by unfold affineOffset; fun_prop))).aestronglyMeasurable
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (phi_pos v).le (kernel_nonneg _ _))]
    exact mul_le_mul_of_nonneg_left (kernel_le_exp _ _) (phi_pos v).le

private theorem moment_integrable (b τ : ℝ) :
    Integrable (fun v : ℝ =>
      stdNormalPDF v * max (affineOffset b τ v) 0 ^ (3 / 2 : ℝ)) := by
  refine ((tilted_density_integrable b τ).const_mul 4).mono' ?_ ?_
  · exact (continuous_stdNormalPDF.mul (by unfold affineOffset; fun_prop)).aestronglyMeasurable
  filter_upwards [] with v
  have hphi := (phi_pos v).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hd : affineOffset b τ v ≤ 0
  · simp only [max_eq_right hd, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), mul_zero]
    positivity
  · rw [max_eq_left (le_of_lt (lt_of_not_ge hd))]
    have h := mul_le_mul_of_nonneg_left
      (moment_power_le_exp (le_of_lt (lt_of_not_ge hd))) (phi_pos v).le
    nlinarith

private theorem moment_pos {b : ℝ} (hb : 0 < b) (τ : ℝ) : 0 < positiveMoment b τ := by
  let f := fun v : ℝ => stdNormalPDF v * max (affineOffset b τ v) 0 ^ (3 / 2 : ℝ)
  have hf : Continuous f := continuous_stdNormalPDF.mul (by dsimp [f, affineOffset]; fun_prop)
  have hp : 0 < f (τ + b / 2 + 1) := by
    have hd : affineOffset b τ (τ + b / 2 + 1) = b := by unfold affineOffset; ring
    dsimp [f]
    rw [hd, max_eq_left hb.le]
    exact mul_pos (phi_pos _) (Real.rpow_pos_of_pos hb _)
  exact integral_pos_of_integrable_nonneg_nonzero hf (moment_integrable b τ)
    (fun v => mul_nonneg (phi_pos v).le (Real.rpow_nonneg (le_max_right _ _) _)) hp.ne'

/-- The exponential envelope on the actual nonlocal displacement set. -/
def nonlocalEnvelope (b τ δ : ℝ) : ℝ :=
  ∫ v in {v : ℝ | δ < affineOffset b τ v},
    stdNormalPDF v * Real.exp (affineOffset b τ v)

private theorem envelope_nonneg (b τ δ : ℝ) : 0 ≤ nonlocalEnvelope b τ δ :=
  integral_nonneg fun v => mul_nonneg (phi_pos v).le (Real.exp_pos _).le

private theorem pointwise_error {q d δ δ₀ C : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    (hδ₀ : δ ≤ δ₀) (hC : 0 ≤ C)
    (hr : ∀ d : ℝ, 0 < d → d ≤ δ₀ →
      |gaussianCoshIntegral q d - coshCoefficient q * d ^ (3 / 2 : ℝ)| ≤
        C * d ^ (5 / 2 : ℝ)) :
    |gaussianCoshIntegral q d - coshCoefficient q * max d 0 ^ (3 / 2 : ℝ)| ≤
      C * δ * max d 0 ^ (3 / 2 : ℝ) +
        (1 + 4 * coshCoefficient q) * (if δ < d then Real.exp d else 0) := by
  have hA := (coefficient_pos hq).le
  by_cases hd : d ≤ 0
  · rw [kernel_zero hd, max_eq_right hd,
      Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    simp only [mul_zero, sub_zero, abs_zero, zero_add]
    positivity
  have hp : 0 < d := lt_of_not_ge hd
  rw [max_eq_left hp.le]
  by_cases hlocal : d ≤ δ
  · rw [if_neg (not_lt.mpr hlocal), mul_zero, add_zero]
    have hpow : d ^ (5 / 2 : ℝ) = d ^ (3 / 2 : ℝ) * d := by
      calc
        _ = d ^ ((3 / 2 : ℝ) + 1) := by norm_num
        _ = _ := by rw [Real.rpow_add hp, Real.rpow_one]
    calc
      _ ≤ C * d ^ (5 / 2 : ℝ) := hr d hp (hlocal.trans hδ₀)
      _ = C * d * d ^ (3 / 2 : ℝ) := by rw [hpow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlocal hC) (Real.rpow_nonneg hp.le _)
  · rw [if_pos (lt_of_not_ge hlocal)]
    have hj := kernel_nonneg q d
    have he := kernel_le_exp q d
    have hm := mul_le_mul_of_nonneg_left (moment_power_le_exp hp.le) hA
    have ha : |gaussianCoshIntegral q d - coshCoefficient q * d ^ (3 / 2 : ℝ)| ≤
        gaussianCoshIntegral q d + coshCoefficient q * d ^ (3 / 2 : ℝ) := by
      exact abs_le.mpr ⟨by nlinarith [mul_nonneg hA (Real.rpow_nonneg hp.le (3 / 2 : ℝ))],
        by nlinarith [mul_nonneg hA (Real.rpow_nonneg hp.le (3 / 2 : ℝ))]⟩
    have hc : 0 ≤ C * δ * d ^ (3 / 2 : ℝ) := by positivity
    nlinarith

private theorem integrated_error {q b τ δ δ₀ C : ℝ} (hq : 0 < q) (hδ : 0 < δ)
    (hδ₀ : δ ≤ δ₀) (hC : 0 ≤ C)
    (hr : ∀ d : ℝ, 0 < d → d ≤ δ₀ →
      |gaussianCoshIntegral q d - coshCoefficient q * d ^ (3 / 2 : ℝ)| ≤
        C * d ^ (5 / 2 : ℝ)) :
    |averagedCosh q b τ - coshCoefficient q * positiveMoment b τ| ≤
      C * δ * positiveMoment b τ +
        (1 + 4 * coshCoefficient q) * nonlocalEnvelope b τ δ := by
  let s := {v : ℝ | δ < affineOffset b τ v}
  have hs : MeasurableSet s := by dsimp [s, affineOffset]; measurability
  have hi := (tilted_density_integrable b τ).indicator hs
  have hbound := ((moment_integrable b τ).const_mul (C * δ)).add
    (hi.const_mul (1 + 4 * coshCoefficient q))
  have heq : averagedCosh q b τ - coshCoefficient q * positiveMoment b τ =
      ∫ v : ℝ, stdNormalPDF v * (gaussianCoshIntegral q (affineOffset b τ v) -
        coshCoefficient q * max (affineOffset b τ v) 0 ^ (3 / 2 : ℝ)) := by
    unfold averagedCosh positiveMoment
    rw [← integral_const_mul, ← integral_sub (outer_integrable q b τ)
      ((moment_integrable b τ).const_mul _)]
    congr 1
    ext v
    ring
  rw [heq]
  calc
    _ ≤ ∫ v : ℝ, C * δ * (stdNormalPDF v * max (affineOffset b τ v) 0 ^ (3 / 2 : ℝ)) +
        (1 + 4 * coshCoefficient q) * s.indicator
          (fun v => stdNormalPDF v * Real.exp (affineOffset b τ v)) v := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hbound
      filter_upwards [] with v
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (phi_pos v)]
      have hh := mul_le_mul_of_nonneg_left
        (pointwise_error hq hδ hδ₀ hC hr (d := affineOffset b τ v)) (phi_pos v).le
      dsimp [s]
      by_cases hv : δ < affineOffset b τ v
      · simpa [Set.indicator, hv, mul_add, mul_assoc, mul_left_comm, mul_comm] using hh
      · simpa [Set.indicator, hv, mul_assoc, mul_left_comm, mul_comm] using hh
    _ = _ := by
      rw [integral_add ((moment_integrable b τ).const_mul (C * δ))
        (hi.const_mul _), integral_const_mul, integral_const_mul, integral_indicator hs]
      rfl

private def positiveWeight (τ z : ℝ) : ℝ := Real.exp (-z - z ^ 2 / (2 * τ ^ 2))

private def positiveDenom (b τ : ℝ) : ℝ :=
  ∫ z in Ioi (0 : ℝ), max (z - b * τ / 2) 0 ^ (3 / 2 : ℝ) * positiveWeight τ z

private def positiveTail (b τ δ : ℝ) : ℝ :=
  ∫ z in Ioi (0 : ℝ),
    if δ < (b / τ) * (z - b * τ / 2) then
      Real.exp ((b / τ) * (z - b * τ / 2)) / (b / τ) ^ (3 / 2 : ℝ) * positiveWeight τ z
    else 0

private def gammaMoment : ℝ := ∫ z in Ioi (0 : ℝ), z ^ (3 / 2 : ℝ) * Real.exp (-z)

private theorem gamma_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun z : ℝ => z ^ (3 / 2 : ℝ) * Real.exp (-a * z)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 3 / 2) (b := a) (by norm_num) (by norm_num) ha)

private theorem gamma_pos : 0 < gammaMoment := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le)
    (by simpa using gamma_integrable 1 (by norm_num))).2
  have hs : Function.support (fun z : ℝ => z ^ (3 / 2 : ℝ) * Real.exp (-z)) ∩ Ioi 0 = Ioi 0 := by
    apply inter_eq_right.mpr
    intro z hz
    exact (mul_pos (Real.rpow_pos_of_pos hz _) (Real.exp_pos _)).ne'
  rw [hs]
  exact isOpen_Ioi.measure_pos volume ⟨1, by norm_num⟩

private theorem phi_rescale {τ : ℝ} (hτ : 0 < τ) (z : ℝ) :
    stdNormalPDF (τ + z / τ) = stdNormalPDF τ * positiveWeight τ z := by
  unfold stdNormalPDF positiveWeight
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  field_simp
  ring

private theorem offset_rescale {τ : ℝ} (hτ : τ ≠ 0) (b z : ℝ) :
    affineOffset b τ (τ + z / τ) = (b / τ) * (z - b * τ / 2) := by
  unfold affineOffset
  field_simp
  ring

private theorem rescale_integral {τ : ℝ} (hτ : 0 < τ) (f : ℝ → ℝ) :
    (∫ v : ℝ, f v) = τ⁻¹ * ∫ z : ℝ, f (τ + z / τ) := by
  have h := Measure.integral_comp_inv_mul_right (fun x => f (τ + x)) τ
  rw [abs_of_pos hτ, smul_eq_mul, integral_add_left_eq_self] at h
  simp only [div_eq_mul_inv]
  rw [h]
  field_simp

private theorem moment_rescale {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ) :
    positiveMoment b τ = stdNormalPDF τ / τ * (b / τ) ^ (3 / 2 : ℝ) * positiveDenom b τ := by
  rw [positiveMoment, rescale_integral hτ]
  have hs : (∫ z in Ioi (0 : ℝ), stdNormalPDF (τ + z / τ) *
      max (affineOffset b τ (τ + z / τ)) 0 ^ (3 / 2 : ℝ)) =
      ∫ z : ℝ, stdNormalPDF (τ + z / τ) *
        max (affineOffset b τ (τ + z / τ)) 0 ^ (3 / 2 : ℝ) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hz0 : z ≤ 0 := le_of_not_gt hz
    rw [offset_rescale hτ.ne']
    have hd : (b / τ) * (z - b * τ / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (div_pos hb hτ).le (by nlinarith)
    simp [max_eq_right hd, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  rw [← hs]
  have heq : (fun z : ℝ => stdNormalPDF (τ + z / τ) *
      max (affineOffset b τ (τ + z / τ)) 0 ^ (3 / 2 : ℝ)) =
      fun z : ℝ => (stdNormalPDF τ * (b / τ) ^ (3 / 2 : ℝ)) *
        (max (z - b * τ / 2) 0 ^ (3 / 2 : ℝ) * positiveWeight τ z) := by
    ext z
    rw [phi_rescale hτ, offset_rescale hτ.ne']
    rw [show max ((b / τ) * (z - b * τ / 2)) 0 =
      (b / τ) * max (z - b * τ / 2) 0 by
        rw [mul_max_of_nonneg _ _ (div_pos hb hτ).le, mul_zero]]
    rw [Real.mul_rpow (div_pos hb hτ).le (le_max_right _ _)]
    ring
  rw [heq, integral_const_mul]
  unfold positiveDenom
  ring

private theorem envelope_rescale {b τ δ : ℝ} (hb : 0 < b) (hτ : 0 < τ) (hδ : 0 < δ) :
    nonlocalEnvelope b τ δ =
      stdNormalPDF τ / τ * (b / τ) ^ (3 / 2 : ℝ) * positiveTail b τ δ := by
  let f := fun v : ℝ => if δ < affineOffset b τ v then
    stdNormalPDF v * Real.exp (affineOffset b τ v) else 0
  have hset : nonlocalEnvelope b τ δ = ∫ v : ℝ, f v := by
    rw [nonlocalEnvelope, ← integral_indicator]
    · rfl
    · dsimp [affineOffset]; measurability
  rw [hset, rescale_integral hτ]
  have hs : (∫ z in Ioi (0 : ℝ), f (τ + z / τ)) = ∫ z : ℝ, f (τ + z / τ) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hz0 : z ≤ 0 := le_of_not_gt hz
    dsimp [f]
    rw [offset_rescale hτ.ne', if_neg]
    have hd : (b / τ) * (z - b * τ / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (div_pos hb hτ).le (by nlinarith)
    exact not_lt.mpr (hd.trans hδ.le)
  rw [← hs]
  have heq : (fun z : ℝ => f (τ + z / τ)) = fun z : ℝ =>
      (stdNormalPDF τ * (b / τ) ^ (3 / 2 : ℝ)) *
        (if δ < (b / τ) * (z - b * τ / 2) then
          Real.exp ((b / τ) * (z - b * τ / 2)) / (b / τ) ^ (3 / 2 : ℝ) * positiveWeight τ z
        else 0) := by
    ext z
    dsimp [f]
    rw [offset_rescale hτ.ne', phi_rescale hτ]
    split_ifs <;> field_simp <;> ring
  rw [heq, integral_const_mul]
  unfold positiveTail
  ring

private theorem positive_weight_limit {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop) (z : ℝ) :
    Tendsto (fun n => positiveWeight (τ n) z) atTop (𝓝 (Real.exp (-z))) := by
  have hi : Tendsto (fun n => (τ n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hτ
  have hr : Tendsto (fun n => z ^ 2 * (τ n)⁻¹ ^ 2 / 2) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := z ^ 2)).mul (hi.pow 2)).div_const 2
  have h := ((tendsto_const_nhds (x := -z)).sub hr).rexp
  convert h using 1 <;>
    simp [positiveWeight, div_eq_mul_inv, mul_inv_rev, inv_pow] <;> ring

private theorem positive_denom_limit {b τ : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hτ : Tendsto τ atTop atTop)
    (hc : Tendsto (fun n => b n * τ n) atTop (𝓝 0)) :
    Tendsto (fun n => positiveDenom (b n) (τ n)) atTop (𝓝 gammaMoment) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z : ℝ => z ^ (3 / 2 : ℝ) * Real.exp (-z))
  · exact Eventually.of_forall fun n => by dsimp [positiveWeight]; fun_prop
  · filter_upwards [hτ.eventually_gt_atTop 0] with n htn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz0 : 0 < z := hz
    have hbn := hb n
    have hc0 : 0 ≤ b n * τ n / 2 := by positivity
    have hm : max (z - b n * τ n / 2) 0 ≤ z := max_le (by linarith) hz0.le
    have hw : positiveWeight (τ n) z ≤ Real.exp (-z) := by
      unfold positiveWeight
      apply Real.exp_le_exp.mpr
      have hh : 0 ≤ z ^ 2 / (2 * τ n ^ 2) := by positivity
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold positiveWeight; positivity)]
    exact mul_le_mul (Real.rpow_le_rpow (le_max_right _ _) hm (by norm_num)) hw
      (by unfold positiveWeight; positivity) (Real.rpow_nonneg hz0.le _)
  · change IntegrableOn (fun z : ℝ => z ^ (3 / 2 : ℝ) * Real.exp (-z)) (Ioi 0)
    simpa only [neg_mul, one_mul] using gamma_integrable 1 (by norm_num)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz0 : 0 < z := hz
    have hm : Tendsto (fun n => max (z - b n * τ n / 2) 0) atTop (𝓝 z) := by
      convert (tendsto_const_nhds.sub (hc.div_const 2)).max tendsto_const_nhds using 1
      simp [max_eq_left hz0.le]
    exact (hm.rpow_const (Or.inr (by norm_num))).mul (positive_weight_limit hτ z)

private theorem positive_tail_bound {b τ δ z : ℝ}
    (hb : 0 < b) (hτ : 0 < τ) (hδ : 0 < δ) (hz : 0 < z) (hh : b / τ ≤ 1 / 2) :
    ‖if δ < (b / τ) * (z - b * τ / 2) then
      Real.exp ((b / τ) * (z - b * τ / 2)) / (b / τ) ^ (3 / 2 : ℝ) * positiveWeight τ z
    else 0‖ ≤ (δ ^ (3 / 2 : ℝ))⁻¹ * (z ^ (3 / 2 : ℝ) * Real.exp (-(1 / 2) * z)) := by
  have hp : 0 < (b / τ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (div_pos hb hτ) _
  have hδp : 0 < δ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hδ _
  split_ifs with hd
  · rw [Real.norm_eq_abs, abs_of_nonneg (by unfold positiveWeight; positivity)]
    have hdle : (b / τ) * (z - b * τ / 2) ≤ (b / τ) * z := by
      apply mul_le_mul_of_nonneg_left _ (div_pos hb hτ).le
      have : 0 ≤ b * τ / 2 := by positivity
      linarith
    have hpow : δ ^ (3 / 2 : ℝ) ≤ (b / τ) ^ (3 / 2 : ℝ) * z ^ (3 / 2 : ℝ) := by
      rw [← Real.mul_rpow (div_pos hb hτ).le hz.le]
      exact Real.rpow_le_rpow hδ.le (hd.le.trans hdle) (by norm_num)
    have he : Real.exp ((b / τ) * (z - b * τ / 2)) * positiveWeight τ z ≤
        Real.exp (-(1 / 2) * z) := by
      unfold positiveWeight
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hhz := mul_le_mul_of_nonneg_right hh hz.le
      have hs : 0 ≤ z ^ 2 / (2 * τ ^ 2) := by positivity
      linarith
    calc
      _ = (Real.exp ((b / τ) * (z - b * τ / 2)) * positiveWeight τ z) /
          (b / τ) ^ (3 / 2 : ℝ) := by ring
      _ ≤ Real.exp (-(1 / 2) * z) / (b / τ) ^ (3 / 2 : ℝ) :=
        div_le_div_of_nonneg_right he hp.le
      _ ≤ _ := by
        apply (div_le_iff₀ hp).2
        have hm := mul_le_mul_of_nonneg_right hpow
          (mul_nonneg (inv_pos.mpr hδp).le (Real.exp_pos (-(1 / 2) * z)).le)
        calc
          _ = δ ^ (3 / 2 : ℝ) *
              ((δ ^ (3 / 2 : ℝ))⁻¹ * Real.exp (-(1 / 2) * z)) := by field_simp
          _ ≤ _ := hm
          _ = _ := by ring
  · simp only [norm_zero]
    positivity

private theorem positive_tail_limit {b τ : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hb0 : Tendsto b atTop (𝓝 0)) (hτ : Tendsto τ atTop atTop)
    (hc : Tendsto (fun n => b n * τ n) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => positiveTail (b n) (τ n) δ) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => b n / τ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      hb0.mul (tendsto_inv_atTop_zero.comp hτ)
  have hlim : Tendsto (fun n => positiveTail (b n) (τ n) δ) atTop
      (𝓝 (∫ z in Ioi (0 : ℝ), (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun z : ℝ => (δ ^ (3 / 2 : ℝ))⁻¹ *
        (z ^ (3 / 2 : ℝ) * Real.exp (-(1 / 2) * z)))
    · exact Eventually.of_forall fun n => by
        apply Measurable.aestronglyMeasurable
        apply Measurable.ite
        · measurability
        · unfold positiveWeight; fun_prop
        · exact measurable_const
    · filter_upwards [hτ.eventually_gt_atTop 0, hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
        with n htn hhn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact positive_tail_bound (hb n) htn hδ hz hhn.le
    · exact (gamma_integrable (1 / 2) (by norm_num)).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have hd : Tendsto (fun n => (b n / τ n) * (z - b n * τ n / 2)) atTop (𝓝 0) := by
        simpa using hh.mul (tendsto_const_nhds.sub (hc.div_const 2))
      apply tendsto_const_nhds.congr'
      filter_upwards [hd.eventually (gt_mem_nhds hδ)] with n hn
      exact (if_neg (not_lt.mpr hn.le)).symm
  simpa using hlim

private theorem positive_relative_tail {b τ : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hb0 : Tendsto b atTop (𝓝 0)) (hτ : Tendsto τ atTop atTop)
    (hc : Tendsto (fun n => b n * τ n) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => nonlocalEnvelope (b n) (τ n) δ / positiveMoment (b n) (τ n))
      atTop (𝓝 0) := by
  have h := (positive_tail_limit hb hb0 hτ hc hδ).div
    (positive_denom_limit hb hτ hc) gamma_pos.ne'
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [hτ.eventually_gt_atTop 0] with n hn
  rw [envelope_rescale (hb n) hn hδ, moment_rescale (hb n) hn]
  have hp : 0 < stdNormalPDF (τ n) / τ n * (b n / τ n) ^ (3 / 2 : ℝ) :=
    mul_pos (div_pos (phi_pos _) hn) (Real.rpow_pos_of_pos (div_pos (hb n) hn) _)
  exact (mul_div_mul_left _ _ hp.ne').symm

private def negativeBase (b L v : ℝ) : ℝ := 1 + v / L - b / (2 * L)

private def negativeDenom (b L : ℝ) : ℝ :=
  ∫ v : ℝ, stdNormalPDF v * max (negativeBase b L v) 0 ^ (3 / 2 : ℝ)

private def negativeTail (b L δ : ℝ) : ℝ :=
  ∫ v : ℝ, if δ < b * L * negativeBase b L v then
    stdNormalPDF v * Real.exp (b * L * negativeBase b L v) / (b * L) ^ (3 / 2 : ℝ)
  else 0

private theorem offset_negative {L : ℝ} (hL : L ≠ 0) (b v : ℝ) :
    affineOffset b (-L) v = b * L * negativeBase b L v := by
  unfold affineOffset negativeBase
  field_simp
  ring

private theorem negative_power_bound {b L : ℝ} (hb : 0 ≤ b) (hL : 1 ≤ L) (v : ℝ) :
    max (negativeBase b L v) 0 ^ (3 / 2 : ℝ) ≤ 2 * (1 + v ^ 2) := by
  have hLp : 0 < L := by linarith
  have hv : v / L ≤ |v| := by
    apply (div_le_iff₀ hLp).2
    exact (le_abs_self v).trans (by nlinarith [abs_nonneg v])
  have hm : max (negativeBase b L v) 0 ≤ 1 + |v| := by
    apply max_le
    · unfold negativeBase
      have hh : 0 ≤ b / (2 * L) := by positivity
      linarith
    · positivity
  calc
    _ ≤ (1 + |v|) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (le_max_right _ _) hm (by norm_num)
    _ ≤ (1 + |v|) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v]) (by norm_num)
    _ ≤ _ := by rw [Real.rpow_two]; nlinarith [sq_nonneg (|v| - 1), sq_abs v]

private theorem exponential_moment_integrable :
    Integrable (fun v : ℝ => stdNormalPDF v * (1 + v ^ 2) * Real.exp (1 + |v|)) := by
  have h0 := integrable_exp_neg_mul_sq (b := (1 / 4 : ℝ)) (by norm_num)
  have h2 := integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 4 : ℝ))
    (s := 2) (by norm_num) (by norm_num)
  simp only [Real.rpow_two] at h2
  have hi := (h0.add h2).const_mul (Real.exp 2 / Real.sqrt (2 * Real.pi))
  refine hi.mono' ?_ ?_
  · exact ((continuous_stdNormalPDF.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with v
    have hphi := phi_pos v
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have he : stdNormalPDF v * Real.exp (1 + |v|) ≤
        (Real.exp 2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(1 / 4) * v ^ 2) := by
      unfold stdNormalPDF
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add]
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (|v| - 2), sq_abs v]
    have hh := mul_le_mul_of_nonneg_right he (show 0 ≤ 1 + v ^ 2 by positivity)
    convert hh using 1 <;> (try simp only [Pi.add_apply]) <;> ring

private theorem negative_moment_rescale {b L : ℝ} (hb : 0 < b) (hL : 0 < L) :
    positiveMoment b (-L) = (b * L) ^ (3 / 2 : ℝ) * negativeDenom b L := by
  unfold positiveMoment negativeDenom
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [offset_negative hL.ne']
  rw [show max (b * L * negativeBase b L v) 0 = b * L * max (negativeBase b L v) 0 by
    rw [mul_max_of_nonneg _ _ (mul_pos hb hL).le, mul_zero]]
  rw [Real.mul_rpow (mul_pos hb hL).le (le_max_right _ _)]
  ring

private theorem negative_envelope_rescale {b L δ : ℝ} (hb : 0 < b) (hL : 0 < L) :
    nonlocalEnvelope b (-L) δ = (b * L) ^ (3 / 2 : ℝ) * negativeTail b L δ := by
  unfold nonlocalEnvelope negativeTail
  rw [← integral_indicator, ← integral_const_mul]
  · apply integral_congr_ae
    filter_upwards [] with v
    simp only [Set.indicator, Set.mem_setOf_eq, offset_negative hL.ne']
    split_ifs <;> field_simp <;> ring
  · unfold affineOffset
    measurability

private theorem negative_denom_limit {b L : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hb0 : Tendsto b atTop (𝓝 0)) (hL : Tendsto L atTop atTop) :
    Tendsto (fun n => negativeDenom (b n) (L n)) atTop (𝓝 1) := by
  have hi : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hL
  have hbase (v : ℝ) : Tendsto (fun n => negativeBase (b n) (L n) v) atTop (𝓝 1) := by
    have h1 := (tendsto_const_nhds (x := v)).mul hi
    have h2 := hb0.mul hi |>.div_const 2
    convert ((tendsto_const_nhds (x := (1 : ℝ))).add h1).sub h2 using 1 <;>
      simp [negativeBase, div_eq_mul_inv, mul_inv_rev] <;> ring
  have hlim : Tendsto (fun n => negativeDenom (b n) (L n)) atTop (𝓝 (∫ v : ℝ, stdNormalPDF v)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun v : ℝ => 2 * (stdNormalPDF v * (1 + v ^ 2)))
    · exact Eventually.of_forall fun n =>
        (continuous_stdNormalPDF.mul (by unfold negativeBase; fun_prop)).aestronglyMeasurable
    · filter_upwards [hL.eventually_ge_atTop 1] with n hn
      filter_upwards [] with v
      have hphi := (phi_pos v).le
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hh := mul_le_mul_of_nonneg_left (negative_power_bound (hb n).le hn v) hphi
      nlinarith
    · have hi' := (integrable_stdNormalPDF.add (integrable_stdNormalPDF_mul_pow 2)).const_mul 2
      convert hi' using 1
      ext v
      simp only [Pi.add_apply]
      ring
    · filter_upwards [] with v
      have hpow := ((hbase v).max (tendsto_const_nhds (x := (0 : ℝ)))).rpow_const
        (p := 3 / 2) (Or.inr (by norm_num))
      simpa using (tendsto_const_nhds (x := stdNormalPDF v)).mul hpow
  simp_rw [stdNormalPDF_eq_gaussianPDFReal] at hlim
  rw [ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 (by norm_num)] at hlim
  exact hlim

private theorem negative_tail_bound {b L δ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hL : 1 ≤ L) (hh : b * L ≤ 1) (hδ : 0 < δ) (v : ℝ) :
    ‖if δ < b * L * negativeBase b L v then
      stdNormalPDF v * Real.exp (b * L * negativeBase b L v) / (b * L) ^ (3 / 2 : ℝ)
    else 0‖ ≤ (2 * (δ ^ (3 / 2 : ℝ))⁻¹) *
      (stdNormalPDF v * (1 + v ^ 2) * Real.exp (1 + |v|)) := by
  have hLp : 0 < L := by linarith
  have hp : 0 < (b * L) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (mul_pos hb hLp) _
  have hδp : 0 < δ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hδ _
  have hphi := phi_pos v
  split_ifs with hd
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have ha : 0 < negativeBase b L v :=
      (mul_pos_iff_of_pos_left (mul_pos hb hLp)).mp (hδ.trans hd)
    have hpow : δ ^ (3 / 2 : ℝ) ≤ (b * L) ^ (3 / 2 : ℝ) *
        max (negativeBase b L v) 0 ^ (3 / 2 : ℝ) := by
      rw [max_eq_left ha.le, ← Real.mul_rpow (mul_pos hb hLp).le ha.le]
      exact Real.rpow_le_rpow hδ.le hd.le (by norm_num)
    have hpb := negative_power_bound hb.le hL v
    have he : Real.exp (b * L * negativeBase b L v) ≤ Real.exp (1 + |v|) := by
      apply Real.exp_le_exp.mpr
      rw [← offset_negative hLp.ne']
      unfold affineOffset
      have hv : b * v ≤ |v| := by
        calc
          _ ≤ b * |v| := mul_le_mul_of_nonneg_left (le_abs_self v) hb.le
          _ ≤ _ := by nlinarith [abs_nonneg v]
      nlinarith [sq_nonneg b]
    have hpow' : δ ^ (3 / 2 : ℝ) ≤ (b * L) ^ (3 / 2 : ℝ) * (2 * (1 + v ^ 2)) :=
      hpow.trans (mul_le_mul_of_nonneg_left hpb hp.le)
    apply (div_le_iff₀ hp).2
    have hm := mul_le_mul_of_nonneg_right hpow'
      (show 0 ≤ (δ ^ (3 / 2 : ℝ))⁻¹ * (stdNormalPDF v * Real.exp (1 + |v|)) by positivity)
    have hleft := mul_le_mul_of_nonneg_left he hphi.le
    calc
      _ ≤ stdNormalPDF v * Real.exp (1 + |v|) := hleft
      _ = δ ^ (3 / 2 : ℝ) *
          ((δ ^ (3 / 2 : ℝ))⁻¹ * (stdNormalPDF v * Real.exp (1 + |v|))) := by field_simp
      _ ≤ _ := hm
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

private theorem negative_tail_limit {b L : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hb0 : Tendsto b atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hh : Tendsto (fun n => b n * L n) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => negativeTail (b n) (L n) δ) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hL
  have hlim : Tendsto (fun n => negativeTail (b n) (L n) δ) atTop (𝓝 (∫ _ : ℝ, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun v : ℝ => (2 * (δ ^ (3 / 2 : ℝ))⁻¹) *
        (stdNormalPDF v * (1 + v ^ 2) * Real.exp (1 + |v|)))
    · exact Eventually.of_forall fun n => by
        apply Measurable.aestronglyMeasurable
        apply Measurable.ite
        · unfold negativeBase; measurability
        · exact (continuous_stdNormalPDF.mul (by unfold negativeBase; fun_prop)).measurable.div_const _
        · exact measurable_const
    · filter_upwards [hL.eventually_ge_atTop 1,
        hb0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
        hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hln hbn hhn
      exact Eventually.of_forall fun v => negative_tail_bound (hb n) hbn.le hln hhn.le hδ v
    · exact exponential_moment_integrable.const_mul _
    · filter_upwards [] with v
      have hd : Tendsto (fun n => b n * L n * negativeBase (b n) (L n) v) atTop (𝓝 0) := by
        have hbase : Tendsto (fun n => negativeBase (b n) (L n) v) atTop (𝓝 1) := by
          have h1 := (tendsto_const_nhds (x := v)).mul hi
          have h2 := (hb0.mul hi).div_const 2
          convert ((tendsto_const_nhds (x := (1 : ℝ))).add h1).sub h2 using 1 <;>
            simp [negativeBase, div_eq_mul_inv, mul_inv_rev] <;> ring
        simpa using hh.mul hbase
      apply tendsto_const_nhds.congr'
      filter_upwards [hd.eventually (gt_mem_nhds hδ)] with n hn
      exact (if_neg (not_lt.mpr hn.le)).symm
  simpa using hlim

private theorem negative_relative_tail {b τ : ℕ → ℝ}
    (hb : ∀ n, 0 < b n) (hb0 : Tendsto b atTop (𝓝 0)) (hτ : Tendsto τ atTop atBot)
    (hc : Tendsto (fun n => b n * τ n) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => nonlocalEnvelope (b n) (τ n) δ / positiveMoment (b n) (τ n))
      atTop (𝓝 0) := by
  have hL : Tendsto (fun n => -τ n) atTop atTop := tendsto_neg_atBot_atTop.comp hτ
  have hh : Tendsto (fun n => b n * -τ n) atTop (𝓝 0) := by simpa using hc.neg
  have h := (negative_tail_limit hb hb0 hL hh hδ).div (negative_denom_limit hb hb0 hL) one_ne_zero
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with n hn
  have h1 := negative_envelope_rescale (hb n) hn (δ := δ)
  have h2 := negative_moment_rescale (hb n) hn
  simp only [neg_neg] at h1 h2
  rw [h1, h2]
  have hp : 0 < (b n * -τ n) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (mul_pos (hb n) hn) _
  exact (mul_div_mul_left _ _ hp.ne').symm

private theorem coefficient_limit {q : ℕ → ℝ} {Q : ℝ} (hQ : 0 < Q)
    (hq : Tendsto q atTop (𝓝 Q)) :
    Tendsto (fun n => coshCoefficient (q n)) atTop (𝓝 (coshCoefficient Q)) := by
  unfold coshCoefficient
  exact tendsto_const_nhds.div ((tendsto_const_nhds (x := (3 : ℝ))).mul hq)
    (mul_ne_zero (by norm_num) hQ.ne')

private theorem relative_from_tail {q b τ : ℕ → ℝ} {Q : ℝ}
    (hq : ∀ n, 0 < q n) (hb : ∀ n, 0 < b n) (hQ : 0 < Q)
    (hq0 : Tendsto q atTop (𝓝 Q))
    (htail : ∀ δ : ℝ, 0 < δ → Tendsto
      (fun n => nonlocalEnvelope (b n) (τ n) δ / positiveMoment (b n) (τ n)) atTop (𝓝 0)) :
    Tendsto (fun n => averagedCosh (q n) (b n) (τ n) /
      (coshCoefficient (q n) * positiveMoment (b n) (τ n))) atTop (𝓝 1) := by
  obtain ⟨δ₀, C, hδ₀, hC, hr⟩ := gaussian_cosh_uniform_remainder (Q / 2) (Q + 1) (by positivity)
  have hmem : ∀ᶠ n in atTop, q n ∈ Icc (Q / 2) (Q + 1) :=
    hq0.eventually (Icc_mem_nhds (by linarith) (by linarith))
  let a := coshCoefficient Q / 2
  let M := coshCoefficient Q + 1
  have hA0 := coefficient_pos hQ
  have ha : 0 < a := by dsimp [a]; positivity
  have hM : 0 < M := by dsimp [M]; linarith
  have hA : ∀ᶠ n in atTop, a ≤ coshCoefficient (q n) ∧ coshCoefficient (q n) ≤ M :=
    (coefficient_limit hQ hq0).eventually
      (Icc_mem_nhds (by dsimp [a]; linarith) (by dsimp [M]; linarith))
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ := min δ₀ (ε * a / (4 * (C + 1)))
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hsmall : C * δ ≤ ε * a / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * (C + 1) by positivity)).1
      (show δ ≤ ε * a / (4 * (C + 1)) from min_le_right _ _)
    nlinarith
  have htail' : ∀ᶠ n in atTop,
      nonlocalEnvelope (b n) (τ n) δ / positiveMoment (b n) (τ n) <
        ε * a / (4 * (1 + 4 * M)) :=
    (htail δ hδ).eventually (gt_mem_nhds (by positivity))
  filter_upwards [hmem, hA, htail'] with n hqn hAn htn
  have hK := moment_pos (hb n) (τ n)
  have hAnp := coefficient_pos (hq n)
  have ht0 : 0 ≤ nonlocalEnvelope (b n) (τ n) δ / positiveMoment (b n) (τ n) :=
    div_nonneg (envelope_nonneg _ _ _) hK.le
  have htest := integrated_error (hq n) hδ hδle hC (fun d hd hdd => (hr (q n) hqn d hd hdd).2)
    (b := b n) (τ := τ n)
  have htailbound : (1 + 4 * coshCoefficient (q n)) *
      (nonlocalEnvelope (b n) (τ n) δ / positiveMoment (b n) (τ n)) < ε * a / 4 := by
    calc
      _ ≤ (1 + 4 * M) *
          (nonlocalEnvelope (b n) (τ n) δ / positiveMoment (b n) (τ n)) :=
        mul_le_mul_of_nonneg_right (by linarith [hAn.2]) ht0
      _ < (1 + 4 * M) * (ε * a / (4 * (1 + 4 * M))) :=
        mul_lt_mul_of_pos_left htn (by positivity)
      _ = _ := by field_simp <;> ring
  have htotal : C * δ + (1 + 4 * coshCoefficient (q n)) *
      (nonlocalEnvelope (b n) (τ n) δ / positiveMoment (b n) (τ n)) <
        ε * coshCoefficient (q n) := by
    have hh := mul_le_mul_of_nonneg_left hAn.1 hε.le
    nlinarith
  rw [Real.dist_eq]
  have heq : |averagedCosh (q n) (b n) (τ n) /
      (coshCoefficient (q n) * positiveMoment (b n) (τ n)) - 1| =
      |averagedCosh (q n) (b n) (τ n) - coshCoefficient (q n) * positiveMoment (b n) (τ n)| /
        (coshCoefficient (q n) * positiveMoment (b n) (τ n)) := by
    rw [← div_self (mul_pos hAnp hK).ne', ← sub_div, abs_div,
      abs_of_pos (mul_pos hAnp hK)]
  rw [heq]
  apply (div_lt_iff₀ (mul_pos hAnp hK)).2
  calc
    _ ≤ C * δ * positiveMoment (b n) (τ n) +
        (1 + 4 * coshCoefficient (q n)) * nonlocalEnvelope (b n) (τ n) δ := htest
    _ = (C * δ + (1 + 4 * coshCoefficient (q n)) *
        (nonlocalEnvelope (b n) (τ n) δ / positiveMoment (b n) (τ n))) *
          positiveMoment (b n) (τ n) := by field_simp <;> ring
    _ < (ε * coshCoefficient (q n)) * positiveMoment (b n) (τ n) :=
      mul_lt_mul_of_pos_right htotal hK
    _ = _ := by ring

/-- The source normalized offset. -/
def sourceOffset (q b : ℝ) : ℝ := (Real.log 4 - q ^ 2 / 2) / b

/-- The actual relative averaging formula in both unbounded source-offset regimes,
with all-index integrability and a strictly positive normalization. -/
theorem gaussian_cosh_source_relative (q b : ℕ → ℝ)
    (hq : ∀ n, 0 < q n) (hb : ∀ n, 0 < b n)
    (hq0 : Tendsto q atTop (𝓝 (Real.sqrt (2 * Real.log 4))))
    (hb0 : Tendsto b atTop (𝓝 0))
    (hregime : Tendsto (fun n => sourceOffset (q n) (b n)) atTop atTop ∨
      Tendsto (fun n => sourceOffset (q n) (b n)) atTop atBot) :
    (∀ n, (∀ v : ℝ, Integrable (fun u : ℝ => stdNormalPDF u *
        max (Real.exp (affineOffset (b n) (sourceOffset (q n) (b n)) v) - Real.cosh (q n * u)) 0)) ∧
      Integrable (fun v : ℝ => stdNormalPDF v *
        gaussianCoshIntegral (q n) (affineOffset (b n) (sourceOffset (q n) (b n)) v)) ∧
      Integrable (fun v : ℝ => stdNormalPDF v *
        max (affineOffset (b n) (sourceOffset (q n) (b n)) v) 0 ^ (3 / 2 : ℝ)) ∧
      0 < positiveMoment (b n) (sourceOffset (q n) (b n)) ∧
      0 < coshCoefficient (q n) ∧
      0 < coshCoefficient (q n) * positiveMoment (b n) (sourceOffset (q n) (b n))) ∧
    Tendsto (fun n => averagedCosh (q n) (b n) (sourceOffset (q n) (b n)) /
      (coshCoefficient (q n) * positiveMoment (b n) (sourceOffset (q n) (b n)))) atTop (𝓝 1) := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hQ : 0 < Real.sqrt (2 * Real.log 4) := Real.sqrt_pos.2 (by positivity)
  have hc : Tendsto (fun n => b n * sourceOffset (q n) (b n)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := Real.log 4)).sub ((hq0.pow 2).div_const 2)
    convert h using 1
    · ext n
      unfold sourceOffset
      field_simp [(hb n).ne']
    · rw [Real.sq_sqrt (by positivity)]
      ring
  refine ⟨?_, relative_from_tail hq hb hQ hq0 ?_⟩
  · intro n
    exact ⟨fun v => kernel_integrable _ _, outer_integrable _ _ _, moment_integrable _ _,
      moment_pos (hb n) _, coefficient_pos (hq n),
      mul_pos (coefficient_pos (hq n)) (moment_pos (hb n) _)⟩
  · intro δ hδ
    rcases hregime with hp | hn
    · exact positive_relative_tail hb hb0 hp hc hδ
    · exact negative_relative_tail hb hb0 hn hc hδ

end D5.S3.TotalVariation.Asymptotics.GaussianCoshAveraging
