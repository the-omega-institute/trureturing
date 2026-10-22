/- GID: D5/S3/Analytic/WallisRemainder/Measure
   generality: G
   mirror-B: D5/B/S3/Analytic/WallisRemainder/Measure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp, mathlib/module/Mathlib.NumberTheory.ZetaValues, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic, mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.SumMeasure, mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap, mathlib/module/Mathlib.MeasureTheory.Measure.Map, mathlib/module/Mathlib.Analysis.SpecialFunctions.ImproperIntegrals, mathlib/module/Mathlib.Probability.Moments.Variance]
   utility: none
   digest: The Wallis logarithmic remainder is a positive spectral Stieltjes transform with exact moments. -/

import D5.S3.Analytic.WallisRemainder.Laplace
import D5.S3.Analytic.WallisRemainder.Stieltjes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
  field_simp (disch := positivity)
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


private lemma coth_hasSum {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => 1 / (u ^ 2 + Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2))
      ((Real.cosh u / Real.sinh u - 1 / u) / (2 * u)) := by
  let z : ℂ := (u / Real.pi : ℝ) * Complex.I
  have hz : z ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨z, by dsimp [z]; simpa using div_pos hu Real.pi_pos⟩
  have hc : HasSum (cotTerm z) ((Real.pi : ℂ) * Complex.cot (Real.pi * z) - 1 / z) := by
    rw [cot_series_rep' hz]
    exact (summable_cotTerm hz).hasSum
  have harg : (Real.pi : ℂ) * z = (u : ℂ) * Complex.I := by
    dsimp [z]
    push_cast
    field_simp (disch := first | assumption | positivity | norm_num [Real.pi_ne_zero])
  have hL : ((Real.pi : ℂ) * Complex.cot (Real.pi * z) - 1 / z).im =
      -Real.pi * (Real.cosh u / Real.sinh u - 1 / u) := by
    rw [harg, Complex.cot, Complex.cos_mul_I, Complex.sin_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    simp [z, Complex.div_im, Complex.normSq_apply]
    simp only [← Complex.ofReal_sinh, Complex.ofReal_re]
    field_simp (disch := first | assumption | positivity | norm_num [Real.pi_ne_zero])
    <;> ring
  have hterm (n : ℕ) : (cotTerm z n).im =
      (-2 * u * Real.pi) * (1 / (u ^ 2 + Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
    simp [cotTerm, z, one_div, Complex.inv_im, Complex.normSq_apply]
    field_simp (disch := first | assumption | positivity | norm_num [Real.pi_ne_zero])
    <;> ring
  have hh := (Complex.hasSum_im hc).div_const (-2 * u * Real.pi)
  rw [hL] at hh
  convert hh using 1
  · ext n
    rw [hterm]
    field_simp (disch := first | assumption | positivity | norm_num [Real.pi_ne_zero])
  · field_simp (disch := first | assumption | positivity | norm_num [Real.pi_ne_zero])
    <;> ring

private lemma coth_full_hasSum {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => 1 / (u ^ 2 + Real.pi ^ 2 * (n : ℝ) ^ 2))
      (1 / u ^ 2 + (Real.cosh u / Real.sinh u - 1 / u) / (2 * u)) := by
  have h := HasSum.zero_add (f := fun n : ℕ => 1 / (u ^ 2 + Real.pi ^ 2 * (n : ℝ) ^ 2))
    (by simpa only [Nat.cast_add, Nat.cast_one] using coth_hasSum hu)
  simpa using h

/-- The odd hyperbolic partial fraction expansion on the positive ray. -/
theorem tanh_div_hasSum {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => 8 / (Real.pi ^ 2 * (2 * (n : ℝ) + 1) ^ 2 + 4 * u ^ 2))
      (Real.tanh u / u) := by
  let f : ℕ → ℝ := fun n => 1 / ((2 * u) ^ 2 + Real.pi ^ 2 * (n : ℝ) ^ 2)
  have hfull : HasSum f (1 / (2 * u) ^ 2 +
      (Real.cosh (2 * u) / Real.sinh (2 * u) - 1 / (2 * u)) / (2 * (2 * u))) :=
    coth_full_hasSum (by positivity)
  have he : HasSum (fun n : ℕ => f (2 * n))
      ((1/4 : ℝ) * (1 / u ^ 2 + (Real.cosh u / Real.sinh u - 1 / u) / (2 * u))) := by
    convert (coth_full_hasSum hu).mul_left (1/4 : ℝ) using 1
    ext n
    dsimp [f]
    push_cast
    field_simp
    <;> ring
  have ho : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hfull.summable.comp_injective (by intro i j hij; dsimp at hij; omega)
  have hs := (HasSum.even_add_odd (f := f) he ho.hasSum).unique hfull
  have hodd : (∑' n : ℕ, f (2 * n + 1)) =
      (1 / (2 * u) ^ 2 +
        (Real.cosh (2 * u) / Real.sinh (2 * u) - 1 / (2 * u)) / (2 * (2 * u))) -
      (1/4 : ℝ) * (1 / u ^ 2 + (Real.cosh u / Real.sinh u - 1 / u) / (2 * u)) := by
    linarith
  convert ho.hasSum.mul_left 8 using 1
  · ext n
    dsimp [f]
    push_cast
    ring
  · rw [hodd, Real.tanh_eq_sinh_div_cosh, Real.cosh_two_mul, Real.sinh_two_mul]
    field_simp [(Real.sinh_pos_iff.mpr hu).ne', (Real.cosh_pos u).ne', hu.ne']
    <;> ring


private lemma integral_P_resolvent {x : ℝ} (hx : 0 < x) :
    (∫ v, 1 / (x ^ 2 + v) ∂P) = ∑' n : ℕ, spectralWeight n *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u) / (x ^ 2 + spectralScale n * u ^ 2) := by
  rw [P, integral_sum_measure (Stieltjes.integrable_resolvent P_pos (sq_pos_of_pos hx))]
  apply tsum_congr
  intro n
  rw [integral_smul_measure, ENNReal.toReal_ofReal (spectralWeight_pos n).le, smul_eq_mul,
    integral_map (by fun_prop)
      (show AEStronglyMeasurable (fun v : ℝ => 1 / (x ^ 2 + v)) _ from
        (show Measurable (fun v : ℝ => 1 / (x ^ 2 + v)) by fun_prop).aestronglyMeasurable),
    exponentialLaw_integral]
  simp only [mul_one_div]

private noncomputable def spectralKernel (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  spectralWeight n / 8 * (Real.exp (-x * t) / (1 + spectralScale n * t ^ 2))

private lemma spectralKernel_nonneg (x : ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ spectralKernel x n t := by
  unfold spectralKernel
  have := (spectralWeight_pos n).le
  have := (spectralScale_pos n).le
  positivity

private lemma spectralKernel_le (x : ℝ) (n : ℕ) (t : ℝ) :
    spectralKernel x n t ≤ spectralWeight n / 8 * Real.exp (-x * t) := by
  unfold spectralKernel
  apply mul_le_mul_of_nonneg_left _ (by have := spectralWeight_pos n; positivity)
  apply (div_le_iff₀ (by have := spectralScale_pos n; positivity)).mpr
  have := mul_nonneg (Real.exp_pos (-x * t)).le
    (mul_nonneg (spectralScale_pos n).le (sq_nonneg t))
  nlinarith

private lemma spectralKernel_integrable {x : ℝ} (hx : 0 < x) (n : ℕ) :
    IntegrableOn (spectralKernel x n) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (show -x < 0 by linarith) 0).const_mul
    (spectralWeight n / 8)).mono'
  · exact (show Measurable (spectralKernel x n) by unfold spectralKernel; fun_prop).aestronglyMeasurable
  · exact Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (spectralKernel_nonneg x n t)]
      exact spectralKernel_le x n t)

private lemma spectralKernel_norm_integral_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖spectralKernel x n t‖) ≤ spectralWeight n / (8 * x) := by
  simp_rw [Real.norm_of_nonneg (spectralKernel_nonneg x n _)]
  have h := integral_mono_ae (spectralKernel_integrable hx n)
    ((integrableOn_exp_mul_Ioi (show -x < 0 by linarith) 0).const_mul (spectralWeight n / 8))
    (Eventually.of_forall (spectralKernel_le x n))
  rw [integral_const_mul, integral_exp_mul_Ioi (show -x < 0 by linarith) 0] at h
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at h
  convert h using 1 <;> ring

private lemma spectralKernel_hasSum {x t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => spectralKernel x n t)
      (D5.S3.Analytic.WallisRemainder.Laplace.laplaceKernel x t) := by
  have h := (tanh_div_hasSum (show 0 < t / 4 by linarith)).mul_left (Real.exp (-x * t) / 8)
  convert h using 1
  · ext n
    unfold spectralKernel spectralWeight spectralScale
    have hn : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp (disch := first | assumption | positivity | norm_num [Real.pi_ne_zero])
    <;> ring
  · unfold D5.S3.Analytic.WallisRemainder.Laplace.laplaceKernel
    field_simp (disch := first | assumption | positivity | norm_num [Real.pi_ne_zero])
    <;> ring

private lemma component_resolvent_scale {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (x / 8) * (spectralWeight n *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u) / (x ^ 2 + spectralScale n * u ^ 2)) =
      ∫ t in Ioi (0 : ℝ), spectralKernel x n t := by
  have h := integral_comp_mul_left_Ioi'
    (fun u : ℝ => Real.exp (-u) / (x ^ 2 + spectralScale n * u ^ 2)) 0 hx
  simp only [mul_zero, smul_eq_mul] at h
  rw [← h, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    unfold spectralKernel
    have hden : 1 + spectralScale n * t ^ 2 ≠ 0 := by
      have := spectralScale_pos n
      positivity
    field_simp (disch := first | assumption | positivity | norm_num [Real.pi_ne_zero])
    <;> ring)

/-- The Wallis remainder is a Stieltjes transform of the positive spectral law. -/
theorem r_eq_stieltjes {x : ℝ} (hx : 0 < x) :
    -Real.log (D5.S3.Analytic.WallisRemainder.Defs.wallisB x) =
      x / 8 * ∫ v, 1 / (x ^ 2 + v) ∂P := by
  rw [D5.S3.Analytic.WallisRemainder.Laplace.r_eq_laplace hx, integral_P_resolvent hx]
  rw [← tsum_mul_left]
  have hsum : Summable (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖spectralKernel x n t‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
      (spectralKernel_norm_integral_le hx) (hasSum_spectralWeight.summable.div_const (8 * x))
  rw [show (fun n : ℕ => x / 8 * (spectralWeight n *
      ∫ u in Ioi (0 : ℝ), Real.exp (-u) / (x ^ 2 + spectralScale n * u ^ 2))) =
        fun n => ∫ t in Ioi (0 : ℝ), spectralKernel x n t by
      funext n; exact component_resolvent_scale hx n]
  rw [integral_tsum_of_summable_integral_norm (spectralKernel_integrable hx) hsum]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact (spectralKernel_hasSum (x := x) ht).tsum_eq.symm

end D5.S3.Analytic.WallisRemainder.Measure
