/- GID: D5/S3/Fourier/Concentration/UniformPerturbationEuclidean
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/UniformPerturbationEuclidean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Euclidean-scale interval bounds on a finite uniform perturbation law. -/

import D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
import D5.S3.Fourier.Concentration.DiffuseSincProduct
import D5.S3.Fourier.Concentration.GaussianCharacteristicWindow
import Mathlib.Probability.Independence.CharacteristicFunction

/-! Coordinate character factorization for affine sums on the perturbation law. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Finset
open scoped ENNReal Interval
open D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
open D5.S3.Fourier.Concentration.DiffuseSincProduct
open D5.S3.Fourier.Concentration.GaussianCharacteristicWindow

namespace D5.S3.Fourier.Concentration.UniformPerturbationEuclidean

private theorem gaussian_euclidean_constant {S : ℝ} (hS : 0 < S) (η : ℝ) :
    Real.exp (1 / 2) * Real.sqrt Real.pi * (Real.sqrt 2 * η) /
        (2 * Real.sqrt (S / 15)) =
      Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2) * η / Real.sqrt S := by
  rw [Real.sqrt_div hS.le, Real.sqrt_div (by positivity : 0 ≤ 15 * Real.pi),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 15)]
  field_simp [Real.sqrt_ne_zero'.mpr hS]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem charFun_intervalNoise {r : ℝ} (hr : 0 < r) (t : ℝ) :
    charFun (intervalNoise r) t = (Real.sinc (r * t) : ℂ) := by
  let _ := intervalNoise_probability hr
  by_cases ht : t = 0
  · simp [ht]
  rw [charFun_apply_real, intervalNoise, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  simp only [← Complex.ofReal_mul]
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Complex.exp (x * I)) ht]
  rw [mul_neg, ← mul_comm r t, integral_exp_mul_I_eq_sinc]
  rw [real_smul, real_smul]
  push_cast
  field_simp [hr.ne', ht]

private theorem charFun_sum_intervalNoise {J : Type*} [Fintype J] (r a : J → ℝ)
    (hr : ∀ j, 0 < r j) (t : ℝ) :
    charFun ((Measure.pi fun j => intervalNoise (r j)).map
      (fun x : J → ℝ => ∑ j, a j * x j)) t =
      ∏ j, (Real.sinc (r j * (t * a j)) : ℂ) := by
  let μ (j : J) := intervalNoise (r j)
  have (j : J) : IsProbabilityMeasure (μ j) := intervalNoise_probability (hr j)
  have hindep : ProbabilityTheory.iIndepFun (fun j (x : J → ℝ) => a j * x j)
      (Measure.pi μ) :=
    ProbabilityTheory.iIndepFun_pi (X := fun j y => a j * y) (fun j => by fun_prop)
  have hmeas (j : J) : AEMeasurable (fun x : J → ℝ => a j * x j) (Measure.pi μ) :=
    (measurable_const.mul (measurable_pi_apply j)).aemeasurable
  have hprod := congrFun (hindep.charFun_map_fun_sum_eq_prod hmeas) t
  change charFun ((Measure.pi μ).map (fun x => ∑ j, a j * x j)) t = _
  rw [hprod, Finset.prod_apply]
  refine prod_congr rfl (fun j _ => ?_)
  rw [charFun_map_mul_comp (measurable_pi_apply j).aemeasurable, (measurePreserving_eval μ j).map_eq,
    mul_comm (a j) t, charFun_intervalNoise (hr j)]

/-- The probability of a closed affine band under finite independent uniform
perturbations is bounded at the Euclidean scale of the coefficients. -/
theorem intervalNoise_pi_affine_le_euclidean {J : Type*} [Fintype J] (r a : J → ℝ)
    (hr : ∀ j, 0 < r j) (b : ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hS : 0 < ∑ j, (a j * r j) ^ 2) :
    (Measure.pi fun j => intervalNoise (r j)) {x | |(∑ j, a j * x j) + b| ≤ η} ≤
      min 1 (ENNReal.ofReal
        (Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2) * η /
          Real.sqrt (∑ j, (a j * r j) ^ 2))) := by
  classical
  let c (j : J) := a j * r j
  let S := ∑ j, c j ^ 2
  let C := Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2)
  let μ := Measure.pi fun j => intervalNoise (r j)
  let f (x : J → ℝ) := ∑ j, a j * x j
  let W : Set (J → ℝ) := {x | |f x + b| ≤ η}
  have (j : J) : IsProbabilityMeasure (intervalNoise (r j)) := intervalNoise_probability (hr j)
  change μ W ≤ min 1 (ENNReal.ofReal (C * η / Real.sqrt S))
  refine le_min ((measure_mono (subset_univ W)).trans_eq (measure_univ (μ := μ))) ?_
  rcases eq_or_lt_of_le hη with rfl | hηpos
  · obtain ⟨i, _, hi⟩ := sum_pos_iff_of_nonneg (fun j _ => sq_nonneg (c j)) |>.mp hS
    have hai : a i ≠ 0 := by
      intro ha
      simp [c, ha] at hi
    simpa [μ, W, f] using intervalNoise_pi_affine r a b 0 hr i hai
  by_cases hfourth : (∑ j, c j ^ 4) ≤ S ^ 2 / 2
  · have hf : Measurable f := by dsimp [f]; fun_prop
    have : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map_iff
      hf.aemeasurable |>.mpr inferInstance
    let V : Set ℝ := {x | |x - -b| ≤ η}
    have hV : MeasurableSet V := measurableSet_le (by fun_prop) measurable_const
    have hmap : (μ.map f) V = μ W := by
      rw [Measure.map_apply hf hV]
      simp [W, V, sub_neg_eq_add]
    have henv (t : ℝ) : ‖charFun (μ.map f) t‖ ≤ (1 + S / 15 * t ^ 2)⁻¹ := by
      rw [charFun_sum_intervalNoise r a hr, norm_prod]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      have harg (j : J) : r j * (t * a j) = c j * t := by dsimp [c]; ring
      simp_rw [harg]
      have h := diffuse_sinc_product_le univ c hfourth t
      simpa only [S, div_mul_eq_mul_div] using h
    have hreal := measureReal_closedWindow_le_of_quadratic_charFun (μ.map f) (-b) hηpos
      (by positivity : 0 < S / 15) henv
    change ((μ.map f) V).toReal ≤ _ at hreal
    rw [hmap] at hreal
    rw [gaussian_euclidean_constant hS η] at hreal
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ W)]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hlarge : ∃ i, S / 2 < c i ^ 2 := by
      by_contra! h
      apply hfourth
      calc
        _ ≤ ∑ j, (S / 2) * c j ^ 2 := by
          apply sum_le_sum
          intro j _
          simpa only [← pow_add] using mul_le_mul_of_nonneg_right (h j) (sq_nonneg (c j))
        _ = _ := by rw [← mul_sum]; change S / 2 * S = S ^ 2 / 2; ring
    obtain ⟨i, hi⟩ := hlarge
    have hai : a i ≠ 0 := by
      intro ha
      have : 0 < c i ^ 2 := (by positivity : 0 < S / 2).trans hi
      simp [c, ha] at this
    have hlocal := intervalNoise_pi_affine r a b η hr i hai
    change μ W ≤ ENNReal.ofReal (η / (|a i| * r i)) at hlocal
    refine hlocal.trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : |c i| = |a i| * r i := by dsimp [c]; rw [abs_mul, abs_of_pos (hr i)]
    have hci : 0 < |a i| * r i := mul_pos (abs_pos.mpr hai) (hr i)
    have hroot : Real.sqrt S ≤ Real.sqrt 2 * |c i| := by
      rw [← Real.sqrt_sq (abs_nonneg (c i)), ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      apply Real.sqrt_le_sqrt
      rw [sq_abs]
      linarith
    have hC : Real.sqrt 2 ≤ C := by
      have hπ : (2 : ℝ) ≤ 15 * Real.pi / 2 := by linarith [Real.pi_gt_three]
      have hexp : 1 ≤ Real.exp (1 / 2) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
      dsimp [C]
      simpa only [one_mul] using
        mul_le_mul hexp (Real.sqrt_le_sqrt hπ) (Real.sqrt_nonneg _) (Real.exp_nonneg _)
    rw [hc] at hroot
    apply (div_le_div_iff₀ hci (Real.sqrt_pos.2 hS)).mpr
    have h := hroot.trans (mul_le_mul_of_nonneg_right hC hci.le)
    nlinarith [mul_le_mul_of_nonneg_left h hηpos.le]

end D5.S3.Fourier.Concentration.UniformPerturbationEuclidean
