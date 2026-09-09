/- GID: D5/S3/Analytic/XiGlobalGrowth
   generality: I
   mirror-B: D5/B/S3/Analytic/XiGlobalGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bound the actual pole-removed xi function uniformly on the complex plane. -/

import D5.S3.Analytic.CompletedZetaMellinReconstruction
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace D5.S3.Analytic.XiGlobalGrowth

open MeasureTheory Set Filter Topology

private theorem mellin_integral_eq (s : ℂ) :
    (∫ t in Ioi (1 : ℝ), ((((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1) / 2) *
      ((t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)) / (t : ℂ)) =
      completedRiemannZeta₀ s := by
  have h := CompletedZetaMellinReconstruction.completed_zeta_mellin_reconstruction.2.1 s
  change completedRiemannZeta s = _ at h
  rw [completedRiemannZeta_eq] at h
  exact (sub_left_inj.mp (sub_left_inj.mp h)).symm

private theorem theta_tail_global :
    ∃ B p : ℝ, 0 < B ∧ 0 < p ∧ ∀ t : ℝ, 1 ≤ t →
      |HurwitzZeta.evenKernel 0 t - 1| ≤ B * Real.exp (-p * t) := by
  obtain ⟨p, hp, htail⟩ := HurwitzZeta.isBigO_atTop_evenKernel_sub 0
  obtain ⟨b, hb, hbound⟩ := htail.exists_pos
  obtain ⟨T, hT⟩ := eventually_atTop.1 hbound.bound
  have hc : ContinuousOn (fun t : ℝ => |HurwitzZeta.evenKernel 0 t - 1| *
      Real.exp (p * t)) (Icc 1 T) := by
    apply ContinuousOn.mul
    · exact ((HurwitzZeta.continuousOn_evenKernel 0).mono
        (fun t ht => lt_of_lt_of_le zero_lt_one ht.1)).sub continuousOn_const |>.abs
    · fun_prop
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨max b K, p, lt_of_lt_of_le hb (le_max_left _ _), hp, ?_⟩
  intro t ht
  by_cases htT : T ≤ t
  · have h := hT t htT
    simp only [ite_true, Real.norm_eq_abs, Real.abs_exp] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have h := hK (mem_image_of_mem _ (show t ∈ Icc 1 T from ⟨ht, (not_le.mp htT).le⟩))
    have he : Real.exp (p * t) * Real.exp (-p * t) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-p * t)).le
    rw [mul_assoc, he, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

private theorem parameter_log_bound (q : ℝ) (hq : 0 < q) :
    ∃ D : ℝ, 0 < D ∧ ∀ r t : ℝ, 1 ≤ r → 0 < t →
      r * Real.log t ≤ q * t + D * r ^ (3 / 2 : ℝ) := by
  refine ⟨3 + |Real.log q|, by positivity, ?_⟩
  intro r t hr ht
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos hq ht) hr0)
  rw [Real.log_div (mul_pos hq ht).ne' hr0.ne', Real.log_mul hq.ne' ht.ne'] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hr0.le
  have hcancel : r * (q * t / r - 1) = q * t - r := by field_simp
  rw [hcancel] at hscaled
  have hhalf := Real.log_le_rpow_div hr0.le (by norm_num : (0 : ℝ) < 1 / 2)
  have hprod : r * r ^ (1 / 2 : ℝ) = r ^ (3 / 2 : ℝ) := by
    calc
      r * r ^ (1 / 2 : ℝ) = r ^ (1 : ℝ) * r ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = r ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hr0]; norm_num
  have hlogr : r * Real.log r ≤ 2 * r ^ (3 / 2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hhalf hr0.le
    rw [div_eq_mul_inv] at h
    norm_num at h
    nlinarith [hprod]
  have hrpow : r ≤ r ^ (3 / 2 : ℝ) := by
    calc
      r = r ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hqlog := neg_abs_le (Real.log q)
  have hqmul := mul_le_mul_of_nonneg_left hqlog hr0.le
  have hqpow := mul_le_mul_of_nonneg_left hrpow (abs_nonneg (Real.log q))
  nlinarith

private theorem symmetric_power_bound (s : ℂ) (t : ℝ) (ht : 1 < t) :
    ‖(t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)‖ ≤
      2 * Real.exp ((1 + ‖s‖) * Real.log t) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hpow (z : ℂ) (hz : z.re ≤ 1 + ‖s‖) :
      ‖(t : ℂ) ^ z‖ ≤ Real.exp ((1 + ‖s‖) * Real.log t) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, Real.rpow_def_of_pos ht0]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.log_nonneg ht.le]
  have h1 := hpow (s / 2) (by
    simp only [Complex.div_ofNat_re]
    nlinarith [Complex.re_le_norm s, norm_nonneg s])
  have h2 := hpow ((1 - s) / 2) (by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    nlinarith [Complex.abs_re_le_norm s, neg_abs_le s.re, norm_nonneg s])
  exact (norm_add_le _ _).trans (by linarith)

private theorem theta_mellin_uniform_majorant :
  ∃ A p D : ℝ, 0 < A ∧ 0 < p ∧ 0 < D ∧
    ∀ s : ℂ, ∀ t : ℝ, 1 < t →
      ‖((((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1) / 2) *
        ((t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)) / (t : ℂ)‖ ≤
        A * Real.exp (D * (1 + ‖s‖) ^ (3 / 2 : ℝ)) *
          Real.exp (-(p / 2) * t) := by
  obtain ⟨B, p, hB, hp, htail⟩ := theta_tail_global
  obtain ⟨D, hD, hparam⟩ := parameter_log_bound (p / 2) (by positivity)
  refine ⟨B, p, D, hB, hp, hD, ?_⟩
  intro s t ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hnorm : ‖(((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1) / 2‖ =
      |HurwitzZeta.evenKernel 0 t - 1| / 2 := by
    rw [norm_div, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
    norm_num
  have hb := mul_le_mul (htail t ht.le) (symmetric_power_bound s t ht)
    (norm_nonneg _) (by positivity : 0 ≤ B * Real.exp (-p * t))
  have hnum : ‖(((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1) / 2‖ *
      ‖(t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)‖ ≤
      B * Real.exp (-p * t) * Real.exp ((1 + ‖s‖) * Real.log t) := by
    rw [hnorm]; nlinarith
  have hdiv : ‖((((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1) / 2) *
      ((t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)) / (t : ℂ)‖ ≤
      B * Real.exp (-p * t) * Real.exp ((1 + ‖s‖) * Real.log t) := by
    rw [norm_div, norm_mul, Complex.norm_of_nonneg ht0.le]
    exact (div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ht.le).trans hnum
  apply hdiv.trans
  rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hB.le
  apply Real.exp_le_exp.mpr
  have h := hparam (1 + ‖s‖) t (by linarith [norm_nonneg s]) ht0
  linarith

private theorem completed_integral_bound :
    ∃ K D : ℝ, 0 < K ∧ 0 < D ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤ K * Real.exp (D * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨A, p, D, hA, hp, hD, hmajor⟩ := theta_mellin_uniform_majorant
  have hpneg : -(p / 2) < 0 := by linarith
  refine ⟨A * (Real.exp (-(p / 2)) / (p / 2)), D, by positivity, hD, ?_⟩
  intro s
  rw [← mellin_integral_eq]
  have h := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi hpneg 1).const_mul
      (A * Real.exp (D * (1 + ‖s‖) ^ (3 / 2 : ℝ))))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall
      (fun t ht => hmajor s t ht)))
  refine h.trans_eq ?_
  rw [integral_const_mul, integral_exp_mul_Ioi hpneg]
  simp only [mul_one, neg_div_neg_eq]
  ring

/-- The classical pole-removed xi reading has a uniform three-halves exponential bound. -/
theorem xi_reading_norm_le_exp_three_halves :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖D5.S3.Zeros.CompletedZeta.xiReading s‖ ≤
        Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨K, D, hK, hD, hbound⟩ := completed_integral_bound
  refine ⟨D + K + 3, by positivity, ?_⟩
  intro s
  let r := 1 + ‖s‖
  let R := r ^ (3 / 2 : ℝ)
  have hr : 1 ≤ r := by dsimp [r]; linarith [norm_nonneg s]
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hrR : r ≤ R := by
    calc
      r = r ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ R := Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hR : 1 ≤ R := hr.trans hrR
  have hn : ‖s‖ ≤ r := by dsimp [r]; linarith
  have hn1 : ‖s - 1‖ ≤ r := by
    simpa [r, add_comm] using norm_sub_le s (1 : ℂ)
  have hpoly : ‖s * (s - 1)‖ ≤ Real.exp (2 * R) := by
    rw [norm_mul]
    calc
      ‖s‖ * ‖s - 1‖ ≤ r * r := mul_le_mul hn hn1 (norm_nonneg _) hr0.le
      _ ≤ Real.exp R * Real.exp R := mul_le_mul
        (hrR.trans (by linarith [Real.add_one_le_exp R] : R ≤ Real.exp R)) (hrR.trans (by linarith [Real.add_one_le_exp R] : R ≤ Real.exp R)) hr0.le
        (Real.exp_pos _).le
      _ = Real.exp (2 * R) := by rw [← Real.exp_add]; congr 1; ring
  have hprod : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤
      K * Real.exp ((D + 2) * R) := by
    rw [norm_mul]
    have h := mul_le_mul hpoly (hbound s) (norm_nonneg _) (Real.exp_pos _).le
    refine h.trans_eq ?_
    dsimp only [R, r]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have hexp : 1 ≤ Real.exp ((D + 2) * R) := Real.one_le_exp (by positivity)
  have hxi : ‖D5.S3.Zeros.CompletedZeta.xiReading s‖ ≤
      (K + 1) * Real.exp ((D + 2) * R) := by
    rw [D5.S3.Zeros.CompletedZeta.xiReading, norm_mul]
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    have h := norm_add_le (s * (s - 1) * completedRiemannZeta₀ s) (1 : ℂ)
    norm_num only [norm_one] at h
    nlinarith
  apply hxi.trans
  have hconst : K + 1 ≤ Real.exp ((K + 1) * R) :=
    (by linarith [Real.add_one_le_exp (K + 1)] : K + 1 ≤ Real.exp (K + 1)).trans (Real.exp_le_exp.mpr (by nlinarith))
  calc
    (K + 1) * Real.exp ((D + 2) * R) ≤
        Real.exp ((K + 1) * R) * Real.exp ((D + 2) * R) :=
      mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le
    _ = Real.exp ((D + K + 3) * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [R, r]
      ring

end D5.S3.Analytic.XiGlobalGrowth
