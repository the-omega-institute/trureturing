/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Fourier correction determines the optimal average of the Fejér gap polynomial. -/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The uniform Fejér argument averages `b / 2 - b²` and divides the
result by two to obtain the leading Mangoldt gap coefficient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerOptimality

open MeasureTheory Set Real
open scoped Interval

/-- The real cosine transform of the averaging measure at frequency `t`. -/
def cosineTransform (μ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ b, cos (t * b) ∂μ

private lemma hasSum_gap_correction (b : ℝ) (hb : b ∈ Icc (0 : ℝ) (1 / 2)) :
    HasSum (fun n : ℕ => cos (4 * π * n * b) / (n : ℝ) ^ 2)
      (4 * π ^ 2 * (1 / 24 - (b / 2 - b ^ 2))) := by
  have hx : 2 * b ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hs := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  change HasSum _ (((-1 : ℝ) ^ (1 + 1) * (2 * π) ^ (2 * 1) / 2 / ↑(Nat.factorial (2 * 1)))
    * bernoulliFun 2 (2 * b)) at hs
  rw [bernoulliFun_two] at hs
  convert hs using 1
  · funext n
    rw [show 4 * π * (n : ℝ) * b = 2 * π * n * (2 * b) by ring]
    simp [div_eq_mul_inv, mul_comm]
  · norm_num
    ring

private lemma hasSum_averaged_correction (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ b ∂μ, b ∈ Icc (0 : ℝ) (1 / 2)) :
    HasSum (fun n : ℕ => cosineTransform μ (4 * π * n) / (n : ℝ) ^ 2)
      (4 * π ^ 2 * (1 / 24 - ∫ b, (b / 2 - b ^ 2) ∂μ)) := by
  let F (n : ℕ) (b : ℝ) : ℝ := cos (4 * π * n * b) / (n : ℝ) ^ 2
  have hnorm (n : ℕ) (b : ℝ) : ‖F n b‖ ≤ 1 / (n : ℝ) ^ 2 := by
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
    exact div_le_div_of_nonneg_right (abs_cos_le_one _) (sq_nonneg _)
  have hint (n : ℕ) : Integrable (F n) μ := by
    have hc : Continuous (F n) := by unfold F; fun_prop
    exact Integrable.of_bound hc.aestronglyMeasurable _ (.of_forall (hnorm n))
  have hmajorant : Summable (fun n : ℕ => ∫ b, ‖F n b‖ ∂μ) := by
    apply hasSum_zeta_two.summable.of_nonneg_of_le
    · exact fun n => integral_nonneg (fun b => norm_nonneg (F n b))
    · intro n
      simpa using
        (integral_mono_ae (hint n).norm (integrable_const (1 / (n : ℝ) ^ 2))
          (.of_forall (hnorm n)))
  have hpoly : Integrable (fun b : ℝ => b / 2 - b ^ 2) μ := by
    have hc : Continuous (fun b : ℝ => b / 2 - b ^ 2) := by fun_prop
    apply Integrable.of_bound hc.aestronglyMeasurable 1
    filter_upwards [hμ] with b hb
    rw [Real.norm_eq_abs, abs_le]
    have hprod := mul_nonneg hb.1 (sub_nonneg.mpr hb.2)
    constructor <;> nlinarith [hb.1, hb.2, sq_nonneg b]
  have h := hasSum_integral_of_summable_integral_norm hint hmajorant
  have heq : (∫ b, ∑' n, F n b ∂μ) =
      4 * π ^ 2 * (1 / 24 - ∫ b, (b / 2 - b ^ 2) ∂μ) := by
    calc
      _ = ∫ b, (4 * π ^ 2 * (1 / 24 - (b / 2 - b ^ 2))) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hμ] with b hb using (hasSum_gap_correction b hb).tsum_eq
      _ = _ := by
        rw [integral_const_mul, integral_sub (integrable_const _) hpoly]
        simp
  rw [heq] at h
  convert h using 1
  funext n
  simp only [cosineTransform, F, integral_div]

/-- The deficit from `1 / 24` is an exact weighted sum of the cosine
moments at frequencies `4π n`. The zeroth term vanishes by division by zero. -/
theorem integral_gap_eq_sub_tsum (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ b ∂μ, b ∈ Icc (0 : ℝ) (1 / 2)) :
    (∫ b, (b / 2 - b ^ 2) ∂μ) =
      1 / 24 - (∑' n : ℕ, cosineTransform μ (4 * π * n) / (n : ℝ) ^ 2) / (4 * π ^ 2) := by
  rw [(hasSum_averaged_correction μ hμ).tsum_eq, mul_div_cancel_left₀ _ (by positivity)]
  ring

/-- Nonnegative lattice moments bound the average by `1 / 24`.
Equality holds exactly when all strictly positive lattice moments vanish. -/
theorem integral_gap_le_and_eq_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ b ∂μ, b ∈ Icc (0 : ℝ) (1 / 2))
    (hcos : ∀ n : ℕ, 0 < n → 0 ≤ cosineTransform μ (4 * π * n)) :
    (∫ b, (b / 2 - b ^ 2) ∂μ) ≤ 1 / 24 ∧
      ((∫ b, (b / 2 - b ^ 2) ∂μ) = 1 / 24 ↔
        ∀ n : ℕ, 0 < n → cosineTransform μ (4 * π * n) = 0) := by
  let a (n : ℕ) := cosineTransform μ (4 * π * n) / (n : ℝ) ^ 2
  have hs := hasSum_averaged_correction μ hμ
  have ha (n : ℕ) : 0 ≤ a n := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [a]
    · exact div_nonneg (hcos n hn) (sq_nonneg _)
  have htotal : 0 ≤ ∑' n, a n := tsum_nonneg ha
  have hπ : 0 < 4 * π ^ 2 := by positivity
  rw [integral_gap_eq_sub_tsum μ hμ]
  change 1 / 24 - (∑' n, a n) / (4 * π ^ 2) ≤ 1 / 24 ∧ _
  refine ⟨sub_le_self _ (div_nonneg htotal hπ.le), ?_⟩
  constructor
  · intro heq n hn
    have hdiv : (∑' n, a n) / (4 * π ^ 2) = 0 := by linarith
    have hzero : (∑' n, a n) = 0 := (div_eq_zero_iff.mp hdiv).resolve_right hπ.ne'
    have hle : a n ≤ ∑' i, a i := hs.summable.le_tsum n (fun i _ => ha i)
    have hz : a n = 0 := le_antisymm (hzero ▸ hle) (ha n)
    exact (div_eq_zero_iff.mp hz).resolve_right (by positivity)
  · intro hz
    have hzero (n : ℕ) : a n = 0 := by
      rcases n.eq_zero_or_pos with rfl | hn
      · simp [a]
      · simp [a, hz n hn]
    change 1 / 24 - (∑' n, a n) / (4 * π ^ 2) = 1 / 24
    simp [hzero]

private def triangularLaw : Measure ℝ :=
  (volume.restrict (Icc 0 (1 / 2))).withDensity (fun b => ENNReal.ofReal (4 - 8 * b))

private lemma integral_triangularLaw (g : ℝ → ℝ) :
    (∫ b, g b ∂triangularLaw) = ∫ b in (0 : ℝ)..(1 / 2), (4 - 8 * b) * g b := by
  rw [triangularLaw, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (.of_forall fun b => ENNReal.ofReal_lt_top) g,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc :
    MeasurableSet (Icc (0 : ℝ) (1 / 2)))] with b hb
  rw [ENNReal.toReal_ofReal (by linarith [hb.2]), smul_eq_mul]

private lemma triangularLaw_probability : IsProbabilityMeasure triangularLaw := by
  apply isProbabilityMeasure_iff_real.mpr
  have hmass : (∫ _ : ℝ, (1 : ℝ) ∂triangularLaw) = triangularLaw.real univ := by simp
  rw [← hmass, integral_triangularLaw]
  have hderiv (b : ℝ) : HasDerivAt (fun x : ℝ => 4 * x - 4 * x ^ 2) (4 - 8 * b) b := by
    convert (((hasDerivAt_id b).const_mul 4).sub
      (((hasDerivAt_id b).pow 2).const_mul 4)) using 1
    · ext x
      rfl
    · simp
      ring
  have hc : Continuous (fun b : ℝ => 4 - 8 * b) := by fun_prop
  simp only [mul_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun b _ => hderiv b)
    (hc.intervalIntegrable _ _)]
  norm_num

private lemma triangularLaw_cosineTransform {t : ℝ} (ht : t ≠ 0) :
    cosineTransform triangularLaw t = 8 * (1 - cos (t / 2)) / t ^ 2 := by
  rw [cosineTransform, integral_triangularLaw]
  let F (b : ℝ) := (4 - 8 * b) * sin (t * b) / t - 8 * cos (t * b) / t ^ 2
  have hderiv (b : ℝ) : HasDerivAt F ((4 - 8 * b) * cos (t * b)) b := by
    have hlinear : HasDerivAt (fun x : ℝ => 4 - 8 * x) (-8) b := by
      simpa using ((hasDerivAt_id b).const_mul (8 : ℝ)).const_sub 4
    have ht' : HasDerivAt (fun x => t * x) t b := by
      simpa using (hasDerivAt_id b).const_mul t
    convert ((hlinear.mul ht'.sin).div_const t).sub
      ((ht'.cos.const_mul 8).div_const (t ^ 2)) using 1
    field_simp
    ring
  have hc : Continuous (fun b : ℝ => (4 - 8 * b) * cos (t * b)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun b _ => hderiv b)
    (hc.intervalIntegrable _ _)]
  dsimp only [F]
  rw [show t * (1 / 2) = t / 2 by ring]
  norm_num
  ring

/-- In the full class with nonnegative cosine transform at every real frequency,
the leading coefficient obtained by halving the average has maximum `1 / 48`. -/
theorem isGreatest_fejer_averaging_coefficient :
    IsGreatest {q : ℝ | ∃ (μ : Measure ℝ), IsProbabilityMeasure μ ∧
      (∀ᵐ b ∂μ, b ∈ Icc (0 : ℝ) (1 / 2)) ∧ (∀ t : ℝ, 0 ≤ cosineTransform μ t) ∧
      (∫ b, (b / 2 - b ^ 2) ∂μ) / 2 = q} (1 / 48) := by
  refine ⟨?_, ?_⟩
  · let _ := triangularLaw_probability
    have hμ : ∀ᵐ b ∂triangularLaw, b ∈ Icc (0 : ℝ) (1 / 2) :=
      (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)
    have hcos (t : ℝ) : 0 ≤ cosineTransform triangularLaw t := by
      by_cases ht : t = 0
      · simp [cosineTransform, ht]
      · rw [triangularLaw_cosineTransform ht]
        exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (cos_le_one _))) (sq_nonneg t)
    have heq := (integral_gap_le_and_eq_iff triangularLaw hμ (fun n _ => hcos _)).2.mpr
    refine ⟨triangularLaw, inferInstance, hμ, hcos, ?_⟩
    suffices h : (∫ b, (b / 2 - b ^ 2) ∂triangularLaw) = 1 / 24 by rw [h]; norm_num
    apply heq
    intro n hn
    rw [triangularLaw_cosineTransform (by positivity),
      show 4 * π * (n : ℝ) / 2 = n * (2 * π) by ring, cos_nat_mul_two_pi]
    simp
  · rintro q ⟨μ, hprob, hμ, hcos, rfl⟩
    let _ := hprob
    linarith [(integral_gap_le_and_eq_iff μ hμ (fun n _ => hcos _)).1]

#print axioms integral_gap_eq_sub_tsum
#print axioms integral_gap_le_and_eq_iff
#print axioms isGreatest_fejer_averaging_coefficient

end D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerOptimality
