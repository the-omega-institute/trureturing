/- GID: D5/S3/Analytic/WallisRemainder/Measure
   generality: G
   mirror-B: D5/B/S3/Analytic/WallisRemainder/Measure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ZetaValues, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic, mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.SumMeasure, mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap, mathlib/module/Mathlib.MeasureTheory.Measure.Map, mathlib/module/Mathlib.Analysis.SpecialFunctions.ImproperIntegrals, mathlib/module/Mathlib.Probability.Moments.Variance]
   utility: none
   digest: An odd spectral probability mixture has exact moments and a positive size-biased law. -/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Moments.Variance

set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace D5.S3.Analytic.WallisRemainder.Measure

private lemma odd_hasSum {p : ℕ} {s : ℝ}
    (h : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ p) s) :
    HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ p) ((1 - (2 : ℝ)⁻¹ ^ p) * s) := by
  have he : HasSum (fun n : ℕ => 1 / ((2 * n : ℕ) : ℝ) ^ p) ((2 : ℝ)⁻¹ ^ p * s) := by
    convert h.mul_left ((2 : ℝ)⁻¹ ^ p) using 1
    ext n
    simp [mul_pow, mul_inv_rev, mul_comm]
  have ho : Summable (fun n : ℕ => 1 / ((2 * n + 1 : ℕ) : ℝ) ^ p) :=
    h.summable.comp_injective (by intro i j hij; dsimp at hij; omega)
  have hu := (HasSum.even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ p) he ho.hasSum).unique h
  have hv : (∑' n : ℕ, 1 / ((2 * n + 1 : ℕ) : ℝ) ^ p) =
      (1 - (2 : ℝ)⁻¹ ^ p) * s := by linarith
  convert ho.hasSum using 1
  · simp
  · exact hv.symm

private lemma odd_two : HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ 2)
    (Real.pi ^ 2 / 8) := by
  convert odd_hasSum hasSum_zeta_two using 1; ring

private lemma odd_four : HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ 4)
    (Real.pi ^ 4 / 96) := by
  convert odd_hasSum hasSum_zeta_four using 1; ring

private lemma odd_six : HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ 6)
    (Real.pi ^ 6 / 960) := by
  have h : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 6) (Real.pi ^ 6 / 945) := by
    convert (hasSum_zeta_nat (k := 3) (by norm_num)) using 1
    norm_num [show bernoulli 6 = (1/42 : ℚ) by decide +kernel]
    ring
  convert odd_hasSum h using 1; ring

private lemma odd_eight : HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ 8)
    (17 * Real.pi ^ 8 / 161280) := by
  have h : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 8) (Real.pi ^ 8 / 9450) := by
    convert (hasSum_zeta_nat (k := 4) (by norm_num)) using 1
    norm_num [show bernoulli 8 = (-1/30 : ℚ) by decide +kernel]
    ring
  convert odd_hasSum h using 1; ring

/-- The weights of the odd hyperbolic spectrum. -/
noncomputable def spectralWeight (n : ℕ) : ℝ :=
  8 / (Real.pi ^ 2 * (2 * (n : ℝ) + 1) ^ 2)

/-- The scale applied to the square of an exponential variable. -/
noncomputable def spectralScale (n : ℕ) : ℝ :=
  1 / (4 * Real.pi ^ 2 * (2 * (n : ℝ) + 1) ^ 2)

private lemma spectralWeight_pos (n : ℕ) : 0 < spectralWeight n := by
  unfold spectralWeight
  positivity

private lemma spectralScale_pos (n : ℕ) : 0 < spectralScale n := by
  unfold spectralScale
  positivity

/-- The odd spectral weights sum to one. -/
theorem hasSum_spectralWeight : HasSum spectralWeight 1 := by
  have hp : Real.pi ^ 2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  convert odd_two.mul_left (8 / Real.pi ^ 2) using 1
  · ext n
    unfold spectralWeight
    field_simp
  · field_simp

private noncomputable def exponentialLaw : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun u : ℝ => ENNReal.ofReal (Real.exp (-u)))

private lemma exponentialLaw_integral (f : ℝ → ℝ) :
    (∫ u, f u ∂exponentialLaw) = ∫ u in Ioi (0 : ℝ), Real.exp (-u) * f u := by
  rw [exponentialLaw, integral_withDensity_eq_integral_toReal_smul (by fun_prop)]
  · simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  · exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

private instance : IsProbabilityMeasure exponentialLaw where
  measure_univ := by
    rw [exponentialLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
        (Eventually.of_forall (fun _ => (Real.exp_pos _).le)), integral_exp_neg_Ioi_zero]
    norm_num

private lemma exponentialLaw_pos : ∀ᵐ u ∂exponentialLaw, 0 < u :=
  (withDensity_absolutelyContinuous _ _).ae_le (self_mem_ae_restrict measurableSet_Ioi)

/-- A probability law assembled from the odd spectral exponential components. -/
noncomputable def P : Measure ℝ := Measure.sum (fun n : ℕ =>
  ENNReal.ofReal (spectralWeight n) • exponentialLaw.map (fun u => spectralScale n * u ^ 2))

instance : IsProbabilityMeasure P where
  measure_univ := by
    rw [P, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (spectralWeight_pos n).le)
      hasSum_spectralWeight.summable, hasSum_spectralWeight.tsum_eq]
    norm_num

/-- The spectral mixture is concentrated on strictly positive values. -/
theorem P_pos : ∀ᵐ v ∂P, 0 < v := by
  rw [P, Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure
  rw [ae_map_iff (by fun_prop) (by measurability)]
  filter_upwards [exponentialLaw_pos] with u hu
  exact mul_pos (spectralScale_pos n) (sq_pos_of_pos hu)

private lemma exponentialLaw_integrable_pow (k : ℕ) :
    Integrable (fun u : ℝ => u ^ k) exponentialLaw := by
  rw [exponentialLaw, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have h := Real.GammaIntegral_convergent (show (0 : ℝ) < (k : ℝ) + 1 by positivity)
  apply h.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  rw [add_sub_cancel_right, Real.rpow_natCast]

private lemma exponentialLaw_moment (k : ℕ) :
    (∫ u, u ^ k ∂exponentialLaw) = (k.factorial : ℝ) := by
  rw [exponentialLaw_integral]
  have h := Real.Gamma_eq_integral (show (0 : ℝ) < (k : ℝ) + 1 by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  convert h.symm using 1
  congr 1
  ext u
  rw [add_sub_cancel_right, Real.rpow_natCast]

private lemma component_pos (n : ℕ) :
    ∀ᵐ v ∂exponentialLaw.map (fun u => spectralScale n * u ^ 2), 0 < v := by
  rw [ae_map_iff (by fun_prop) (by measurability)]
  filter_upwards [exponentialLaw_pos] with u hu
  exact mul_pos (spectralScale_pos n) (sq_pos_of_pos hu)

private lemma component_integrable_pow (n k : ℕ) :
    Integrable (fun v : ℝ => v ^ k)
      (exponentialLaw.map (fun u => spectralScale n * u ^ 2)) := by
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_def, mul_pow, ← pow_mul] using
    (exponentialLaw_integrable_pow (2 * k)).const_mul (spectralScale n ^ k)

private lemma component_moment (n k : ℕ) :
    (∫ v : ℝ, v ^ k ∂exponentialLaw.map (fun u => spectralScale n * u ^ 2)) =
      spectralScale n ^ k * ((2 * k).factorial : ℝ) := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow, ← pow_mul]
  rw [integral_const_mul, exponentialLaw_moment]

private lemma spectral_moment_hasSum (k : ℕ) {c : ℝ}
    (h : HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + 1) ^ (2 * k + 2)) c) :
    HasSum (fun n => spectralWeight n * spectralScale n ^ k * ((2 * k).factorial : ℝ))
      (8 * ((2 * k).factorial : ℝ) / (4 ^ k * Real.pi ^ (2 * k + 2)) * c) := by
  convert h.mul_left (8 * ((2 * k).factorial : ℝ) / (4 ^ k * Real.pi ^ (2 * k + 2))) using 1
  ext n
  have hpow (v : ℝ) : v ^ (2 * k + 2) = v ^ 2 * (v ^ 2) ^ k := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [spectralWeight, spectralScale]
  simp only [hpow, div_pow, mul_pow]
  field_simp [Real.pi_ne_zero, show (2 * (n : ℝ) + 1) ≠ 0 by positivity]
  ring

private lemma spectral_moment_one :
    HasSum (fun n => spectralWeight n * spectralScale n ^ 1 * ((2 * 1).factorial : ℝ))
      (1 / 24) := by
  convert spectral_moment_hasSum 1 odd_four using 1
  norm_num [Nat.factorial]
  field_simp
  norm_num

private lemma spectral_moment_two :
    HasSum (fun n => spectralWeight n * spectralScale n ^ 2 * ((2 * 2).factorial : ℝ))
      (1 / 80) := by
  convert spectral_moment_hasSum 2 odd_six using 1
  norm_num [Nat.factorial]
  field_simp
  norm_num

private lemma spectral_moment_three :
    HasSum (fun n => spectralWeight n * spectralScale n ^ 3 * ((2 * 3).factorial : ℝ))
      (17 / 1792) := by
  convert spectral_moment_hasSum 3 odd_eight using 1
  norm_num [Nat.factorial]
  field_simp
  norm_num

private lemma P_integrable_pow (k : ℕ)
    (hs : Summable (fun n => spectralWeight n * spectralScale n ^ k * ((2 * k).factorial : ℝ))) :
    Integrable (fun v : ℝ => v ^ k) P := by
  apply integrable_sum_measure
    (fun n => (component_integrable_pow n k).smul_measure ENNReal.ofReal_ne_top)
  convert hs using 1
  ext n
  rw [integral_smul_measure, ENNReal.toReal_ofReal (spectralWeight_pos n).le, smul_eq_mul]
  have he : (∫ v : ℝ, ‖v ^ k‖ ∂exponentialLaw.map (fun u => spectralScale n * u ^ 2)) =
      ∫ v : ℝ, v ^ k ∂exponentialLaw.map (fun u => spectralScale n * u ^ 2) := by
    apply integral_congr_ae
    filter_upwards [component_pos n] with v hv
    exact Real.norm_of_nonneg (pow_nonneg hv.le k)
  rw [he, component_moment]
  ring

private lemma P_moment (k : ℕ) {c : ℝ}
    (hs : HasSum (fun n => spectralWeight n * spectralScale n ^ k * ((2 * k).factorial : ℝ)) c) :
    (∫ v : ℝ, v ^ k ∂P) = c := by
  rw [P, integral_sum_measure (P_integrable_pow k hs.summable)]
  convert hs.tsum_eq using 1
  apply tsum_congr
  intro n
  rw [integral_smul_measure, ENNReal.toReal_ofReal (spectralWeight_pos n).le, smul_eq_mul,
    component_moment]
  ring

/-- The first moment of the spectral probability measure is finite. -/
theorem integrable_P_id : Integrable (fun v : ℝ => v) P := by
  simpa using P_integrable_pow 1 spectral_moment_one.summable

/-- The second moment of the spectral probability measure is finite. -/
theorem integrable_P_sq : Integrable (fun v : ℝ => v ^ 2) P :=
  P_integrable_pow 2 spectral_moment_two.summable

/-- The third moment of the spectral probability measure is finite. -/
theorem integrable_P_cube : Integrable (fun v : ℝ => v ^ 3) P :=
  P_integrable_pow 3 spectral_moment_three.summable

/-- The first moment of the spectral probability measure. -/
theorem integral_P_id : (∫ v : ℝ, v ∂P) = 1 / 24 := by
  simpa using P_moment 1 spectral_moment_one

/-- The second moment of the spectral probability measure. -/
theorem integral_P_sq : (∫ v : ℝ, v ^ 2 ∂P) = 1 / 80 :=
  P_moment 2 spectral_moment_two

/-- The third moment of the spectral probability measure. -/
theorem integral_P_cube : (∫ v : ℝ, v ^ 3 ∂P) = 17 / 1792 :=
  P_moment 3 spectral_moment_three

/-- The size-biased law of the spectral variable. -/
noncomputable def Q : Measure ℝ := P.withDensity (fun v => ENNReal.ofReal (24 * v))

instance : IsProbabilityMeasure Q where
  measure_univ := by
    rw [Q, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_P_id.const_mul 24)
        (P_pos.mono (fun v hv => by positivity)), integral_const_mul, integral_P_id]
    norm_num

/-- The size-biased measure is also concentrated on positive values. -/
theorem Q_pos : ∀ᵐ v ∂Q, 0 < v :=
  (withDensity_absolutelyContinuous _ _).ae_le P_pos

/-- Integration against the size-biased law. -/
theorem integral_Q (f : ℝ → ℝ) :
    (∫ v, f v ∂Q) = 24 * ∫ v, v * f v ∂P := by
  rw [Q, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [P_pos] with v hv
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  ring

/-- The first moment of the size-biased measure is finite. -/
theorem integrable_Q_id : Integrable (fun v : ℝ => v) Q := by
  rw [Q, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply (integrable_P_sq.const_mul 24).congr
  filter_upwards [P_pos] with v hv
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  ring

/-- The second moment of the size-biased measure is finite. -/
theorem integrable_Q_sq : Integrable (fun v : ℝ => v ^ 2) Q := by
  rw [Q, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply (integrable_P_cube.const_mul 24).congr
  filter_upwards [P_pos] with v hv
  rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  ring

/-- The mean of the size-biased law. -/
theorem integral_Q_id : (∫ v : ℝ, v ∂Q) = 3 / 10 := by
  rw [integral_Q]
  simp_rw [← pow_two]
  rw [integral_P_sq]
  norm_num

/-- The second moment of the size-biased law. -/
theorem integral_Q_sq : (∫ v : ℝ, v ^ 2 ∂Q) = 51 / 224 := by
  rw [integral_Q]
  have he : (fun v : ℝ => v * v ^ 2) = (fun v : ℝ => v ^ 3) := by ext v; ring
  rw [he, integral_P_cube]
  norm_num

/-- The variance of the spectral law. -/
theorem variance_P : ProbabilityTheory.variance (fun v : ℝ => v) P = 31 / 2880 := by
  rw [ProbabilityTheory.variance_eq_sub
    ((memLp_two_iff_integrable_sq (by fun_prop)).mpr integrable_P_sq)]
  change (∫ v : ℝ, v ^ 2 ∂P) - (∫ v : ℝ, v ∂P) ^ 2 = _
  rw [integral_P_sq, integral_P_id]
  norm_num

/-- The variance of the size-biased law. -/
theorem variance_Q : ProbabilityTheory.variance (fun v : ℝ => v) Q = 771 / 5600 := by
  rw [ProbabilityTheory.variance_eq_sub
    ((memLp_two_iff_integrable_sq (by fun_prop)).mpr integrable_Q_sq)]
  change (∫ v : ℝ, v ^ 2 ∂Q) - (∫ v : ℝ, v ∂Q) ^ 2 = _
  rw [integral_Q_sq, integral_Q_id]
  norm_num

end D5.S3.Analytic.WallisRemainder.Measure
