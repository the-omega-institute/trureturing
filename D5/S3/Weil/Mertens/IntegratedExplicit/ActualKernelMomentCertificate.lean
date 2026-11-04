/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full actual-K endpoint certificate and finite signed expression. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelSmallWindowBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import D5.S3.Arith.GoldenResource.RobinRationalBasis

/-! Exact scalar order arithmetic for the actual moment endpoint. -/

namespace ActualKScalarSource

noncomputable section

open Filter Topology Real

variable (C alpha D : ℝ)

private def factorial10 : ℝ := (Nat.factorial 10 : ℝ)

def B : ℝ := C * (1 + factorial10 * (2 / alpha) ^ (10 : ℕ))

def d0 : ℝ := Real.eulerMascheroniConstant - 1 + Real.log (2 * Real.pi)

def M : ℝ := Real.exp (D / 2)

def beta : ℝ :=
  M D * (1 + C * (Real.exp (-alpha * (D / 4) ^ (1 / 10 : ℝ)) +
    Real.exp (-D / 4))) + D + B C alpha

def curvature : ℝ :=
  ((9 + 4 * C + 2 * B C alpha) * M D + D + 3) / 4

def N : ℕ := Nat.ceil (max 1 (max (D * Real.sqrt (curvature C alpha D) / 2)
  ((5 * D / 4) * Real.exp (beta C alpha D + d0 + 2))))

def delta (D : ℝ) (q : ℕ) : ℝ := D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))

theorem B_ge_C (hC : 1 ≤ C) : C ≤ B C alpha := by
  have h : 0 ≤ factorial10 * (2 / alpha) ^ (10 : ℕ) := by
    unfold factorial10
    positivity
  unfold B
  nlinarith

theorem B_ge_one (hC : 1 ≤ C) : 1 ≤ B C alpha :=
  hC.trans (B_ge_C C alpha hC)

theorem one_le_M (hD : 0 < D) : 1 ≤ M D := by
  exact Real.one_le_exp (by positivity)

theorem base_lt_beta (hC : 1 ≤ C) : M D + D + B C alpha < beta C alpha D := by
  have hm : 0 < M D := Real.exp_pos _
  have he : 0 < C * (Real.exp (-alpha * (D / 4) ^ (1 / 10 : ℝ)) +
      Real.exp (-D / 4)) := mul_pos (by linarith) (add_pos (Real.exp_pos _) (Real.exp_pos _))
  unfold beta
  nlinarith [mul_pos hm he]

theorem two_le_beta (hC : 1 ≤ C) (hD : 0 < D) : 2 ≤ beta C alpha D := by
  have := base_lt_beta C alpha D hC
  have := B_ge_one C alpha hC
  have := one_le_M D hD
  linarith

theorem d0_nonneg : 0 ≤ d0 := by
  have hg := Real.one_half_lt_eulerMascheroniConstant
  have hl := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 5 by norm_num)
  have hp : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 6) hp
  norm_num at hl
  unfold d0
  linarith

theorem curvature_lt_two_beta_sq (hC : 1 ≤ C) (hD : 0 < D) :
    curvature C alpha D < 2 * (beta C alpha D) ^ 2 := by
  have hB := B_ge_one C alpha hC
  have hBC := B_ge_C C alpha hC
  have hM := one_le_M D hD
  have hbeta := base_lt_beta C alpha D hC
  have hS : 0 < M D + D + B C alpha := by linarith
  have hsq : (M D + D + B C alpha) ^ 2 < (beta C alpha D) ^ 2 := by
    nlinarith
  have h1 : 0 < M D * (8 * M D + 10 * B C alpha - 9) := by
    apply mul_pos <;> linarith
  have h2 : 0 ≤ 4 * M D * (B C alpha - C) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hBC)
  have h3 : 0 < 8 * (B C alpha) ^ 2 - 3 := by nlinarith
  have h4 : 0 ≤ D * (16 * M D - 1) := mul_nonneg hD.le (by linarith)
  have h5 : 0 ≤ 16 * B C alpha * D := by positivity
  have hexpand :
      8 * (M D + D + B C alpha) ^ 2 -
          ((9 + 4 * C + 2 * B C alpha) * M D + D + 3) =
        M D * (8 * M D + 10 * B C alpha - 9) +
          4 * M D * (B C alpha - C) + (8 * (B C alpha) ^ 2 - 3) +
          D * (16 * M D - 1) + 8 * D ^ 2 + 16 * B C alpha * D := by ring
  unfold curvature
  nlinarith [sq_nonneg D]

theorem eight_beta_le_exp (hC : 1 ≤ C) (hD : 0 < D) :
    8 * beta C alpha D ≤ Real.exp (beta C alpha D + d0 + 2) := by
  have hb := two_le_beta C alpha D hC hD
  have he := Real.two_mul_le_exp (x := beta C alpha D)
  have he2 := Real.two_mul_le_exp (x := (2 : ℝ))
  have hd : Real.exp 2 ≤ Real.exp (d0 + 2) := Real.exp_le_exp.mpr (by
    linarith [d0_nonneg])
  have hp := mul_le_mul he (show 4 ≤ Real.exp (d0 + 2) by linarith)
    (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_pos _).le
  rw [show beta C alpha D + d0 + 2 = beta C alpha D + (d0 + 2) by ring,
    Real.exp_add]
  nlinarith

theorem third_term_le_N :
    (5 * D / 4) * Real.exp (beta C alpha D + d0 + 2) ≤ (N C alpha D : ℝ) := by
  exact (le_max_right _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))

theorem one_le_N : 1 ≤ N C alpha D := by
  apply Nat.one_le_ceil_iff.mpr
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)

theorem ten_D_beta_le_N (hC : 1 ≤ C) (hD : 0 < D) :
    10 * D * beta C alpha D ≤ (N C alpha D : ℝ) := by
  have he := eight_beta_le_exp C alpha D hC hD
  have h := mul_le_mul_of_nonneg_left he (show 0 ≤ 5 * D / 4 by positivity)
  have hN := third_term_le_N C alpha D
  nlinarith

theorem log_five_fourths : (1 : ℝ) / 5 ≤ Real.log (5 / 4) := by
  have h := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  norm_num at h ⊢
  linarith

theorem q_log_lower (hD : 0 < D) :
    beta C alpha D + d0 + 2 + Real.log (5 / 4) ≤
      Real.log ((N C alpha D : ℝ) / D) := by
  have ht : (5 / 4 : ℝ) * Real.exp (beta C alpha D + d0 + 2) ≤
      (N C alpha D : ℝ) / D := by
    apply (le_div_iff₀ hD).mpr
    nlinarith [third_term_le_N C alpha D]
  have hl := Real.log_le_log (by positivity :
    0 < (5 / 4 : ℝ) * Real.exp (beta C alpha D + d0 + 2)) ht
  rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at hl
  linarith

theorem q_delta_bound (hC : 1 ≤ C) (hD : 0 < D) :
    delta D (N C alpha D) * curvature C alpha D ≤ (1 : ℝ) / 200 := by
  have hb := two_le_beta C alpha D hC hD
  have hN := ten_D_beta_le_N C alpha D hC hD
  have hq : 0 < (N C alpha D : ℝ) := by
    exact_mod_cast (show 0 < N C alpha D from lt_of_lt_of_le Nat.zero_lt_one (one_le_N C alpha D))
  have hs : (10 * D * beta C alpha D) ^ 2 ≤ (N C alpha D : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hq.le).2 hN
  have hc := mul_le_mul_of_nonneg_left
    (curvature_lt_two_beta_sq C alpha D hC hD).le (sq_nonneg D)
  have hd : 0 < 4 * (N C alpha D : ℝ) * ((N C alpha D : ℝ) + 1) := by positivity
  unfold delta
  rw [div_mul_eq_mul_div, div_le_iff₀ hd]
  nlinarith

theorem q_scalar_bounds (hC : 1 ≤ C) (hD : 0 < D) :
    1 ≤ N C alpha D ∧
      (8 : ℝ) ≤ (N C alpha D : ℝ) / D ∧
      delta D (N C alpha D) * curvature C alpha D ≤ (1 : ℝ) / 8 ∧
      beta C alpha D + d0 + 2 + (1 : ℝ) / 5 ≤
        Real.log ((N C alpha D : ℝ) / D) := by
  refine ⟨one_le_N C alpha D, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hD).mpr
    have := ten_D_beta_le_N C alpha D hC hD
    have := two_le_beta C alpha D hC hD
    nlinarith
  · exact (q_delta_bound C alpha D hC hD).trans (by norm_num)
  · linarith [q_log_lower C alpha D hD, log_five_fourths]

#print axioms q_scalar_bounds

end
end ActualKScalarSource
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

variable {I : Type u} [Fintype I]

private lemma shifted_correlation_half (D t : ℝ) (hD : 0 < D)
    (ht : 0 < t) (htD : t ≤ D) (hDt : D ≤ 2 * t)
    (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0) :
    |(∫ v : ℝ, star («prefix» x a (v + t)) * «prefix» x a v).re| ≤
      (1 / 2 : ℝ) * energy x a := by
  let F : ℝ → ℂ := «prefix» x a
  let f : ℝ → ℝ := fun v => ‖F v‖ ^ 2
  let g : ℝ → ℝ := fun v => ‖F (v + t)‖ * ‖F v‖
  have hs := shifted_hinge_prefix_energy x a ha t
  have hF : Integrable f := by simpa [f, F] using hs.2.1
  have hFshift : Integrable (fun v => f (v + t)) := hF.comp_add_right t
  have hg : Integrable g := by
    simpa only [g, F, norm_mul, norm_star] using hs.1.norm
  have hg_support : ∀ v, v ∉ Icc (0 : ℝ) (D - t) → g v = 0 := by
    intro v hv
    have hv' : v < 0 ∨ D - t < v := by
      by_cases h0 : 0 ≤ v
      · right
        exact lt_of_not_ge (fun hu => hv ⟨h0, hu⟩)
      · left
        linarith
    rcases hv' with hv0 | hvu
    · have hz := prefix_support D x a hx ha v (by simp [hv0])
      simp [g, F, hz]
    · have hvs : D < v + t := by linarith
      have hz := prefix_support D x a hx ha (v + t) (by simp [hvs])
      simp [g, F, hz]
  have hgw : (∫ v : ℝ, g v) = ∫ v in Icc (0 : ℝ) (D - t), g v := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      by_cases hv : v ∈ Icc (0 : ℝ) (D - t)
      · simp [Set.indicator, hv]
      · simp [Set.indicator, hv, hg_support v hv])
  have hAM :
      (∫ v in Icc (0 : ℝ) (D - t), g v) ≤
        (1 / 2 : ℝ) *
          ((∫ v in Icc (0 : ℝ) (D - t), f v) +
            ∫ v in Icc (0 : ℝ) (D - t), f (v + t)) := by
    have hmono := integral_mono (hg.integrableOn (s := Icc (0 : ℝ) (D - t)))
      (((hF.add hFshift).div_const 2).integrableOn (s := Icc (0 : ℝ) (D - t))) (by
        intro v
        dsimp [g, f]
        nlinarith [sq_nonneg (‖F (v + t)‖ - ‖F v‖)])
    change (∫ v in Icc (0 : ℝ) (D - t), g v) ≤
      ∫ v in Icc (0 : ℝ) (D - t), (f v + f (v + t)) / 2 at hmono
    rw [integral_div, integral_add hF.integrableOn hFshift.integrableOn] at hmono
    convert hmono using 1 <;> ring
  have hshift :
      (∫ v in Icc (0 : ℝ) (D - t), f (v + t)) =
        ∫ v in Icc t D, f v := by
    have h0 : 0 ≤ D - t := by linarith
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le htD]
    simpa [sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right (f := f) (a := (0 : ℝ))
        (b := D - t) t)
  have hA :
      (∫ v in Icc (0 : ℝ) (D - t), f v) = ∫ v in (0 : ℝ)..(D - t), f v := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hB :
      (∫ v in Icc t D, f v) = ∫ v in t..D, f v := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le htD]
  have hE : energy x a = ∫ v in (0 : ℝ)..D, f v := by
    have hE' : energy x a = ∫ v in Icc (0 : ℝ) D, f v := by
      rw [energy, ← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      exact ae_of_all _ (fun v => by
        by_cases hv : v ∈ Icc (0 : ℝ) D
        · simp [Set.indicator, hv, f, F]
        · have hz := prefix_support D x a hx ha v hv
          simp [Set.indicator, hv, f, F, hz])
    rw [hE', integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
  have hparts :
      (∫ v in (0 : ℝ)..(D - t), f v) + ∫ v in t..D, f v ≤
        ∫ v in (0 : ℝ)..D, f v := by
    have hmid : IntervalIntegrable f volume (D - t) t := hF.intervalIntegrable
    have hright : IntervalIntegrable f volume t D := hF.intervalIntegrable
    have hleft : IntervalIntegrable f volume 0 (D - t) := hF.intervalIntegrable
    have htot := intervalIntegral.integral_add_adjacent_intervals
      hleft hmid
    have hleftmid : IntervalIntegrable f volume 0 t := hleft.trans hmid
    have htot' := intervalIntegral.integral_add_adjacent_intervals
      hleftmid hright
    have hnon : 0 ≤ ∫ v in (D - t)..t, f v := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact integral_nonneg (fun _ => sq_nonneg _)
    nlinarith [htot, htot', hnon]
  have hcorr :
      |(∫ v : ℝ, star (F (v + t)) * F v).re| ≤ ∫ v : ℝ, g v := by
    have hi := norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
      (f := fun v : ℝ => star (F (v + t)) * F v)
    have hre := Complex.abs_re_le_norm (∫ v : ℝ, star (F (v + t)) * F v)
    calc
      |(∫ v : ℝ, star (F (v + t)) * F v).re| ≤
          ‖∫ v : ℝ, star (F (v + t)) * F v‖ := hre
      _ ≤ ∫ v : ℝ, ‖star (F (v + t)) * F v‖ := hi
      _ = ∫ v : ℝ, g v := by
        apply integral_congr_ae
        exact ae_of_all _ (fun v => by simp [g, norm_mul, norm_star])
  rw [hgw] at hcorr
  rw [hA, hshift, hB] at hAM
  nlinarith [hcorr, hAM, hparts, hE]

private lemma prime_quadratic_small_bound (D : ℝ) (hD0 : 0 ≤ D)
    (hD3 : D ≤ Real.log 3) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0) :
    primeQuadratic D x a ≤ (1 / 2 : ℝ) * energy x a := by
  classical
  have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
  by_cases hzero : D = 0
  · subst D
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [primeQuadratic, primes_empty_small (D := 0) (by norm_num) (by linarith)]
    simp
    nlinarith [hE]
  have hD : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hzero)
  by_cases hD2 : D < Real.log 2
  · rw [primeQuadratic, primes_empty_small hD0 hD2]
    simp
    nlinarith [hE]
  have hD2' : Real.log 2 ≤ D := le_of_not_gt hD2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le_log3 : Real.log 2 ≤ Real.log 3 := by
    have h2 := Real.log_two_lt_d9
    have h3 := Real.log_three_gt_d9
    norm_num at h2 h3 ⊢
    linarith
  have hDt : D ≤ 2 * Real.log 2 := by
    have h2 := Real.log_two_gt_d9
    have h3 := Real.log_three_lt_d9
    norm_num at h2 h3 ⊢
    linarith
  have hcorr2 :
      |(∫ v : ℝ, star («prefix» x a (v + Real.log 2)) * «prefix» x a v).re| ≤
        (1 / 2 : ℝ) * energy x a :=
    shifted_correlation_half D (Real.log 2) hD hlog2pos
      hD2' hDt x a hx ha
  have hcoef2 :
      2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2) *
          (∫ v : ℝ, star («prefix» x a (v + Real.log 2)) * «prefix» x a v).re ≤
        (1 / 2 : ℝ) * energy x a := by
    have hc := (abs_le.mp hcorr2).2
    have hw := log_two_weight_bound
    have hw0 : 0 ≤ ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 := by
      have hΛ : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
        ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
      rw [hΛ]
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hc (by positivity :
      (0 : ℝ) ≤ 2 * (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2))]
  by_cases heq : D = Real.log 3
  · subst D
    have hcorr3 :
        (∫ v : ℝ, star («prefix» x a (v + Real.log 3)) * «prefix» x a v) = 0 := by
      have hfun : (fun v : ℝ =>
          star («prefix» x a (v + Real.log 3)) * «prefix» x a v) = fun _ => 0 := by
        funext v
        by_cases hv0 : v < 0
        · have hz := prefix_support (Real.log 3) x a hx ha v (by simp [hv0])
          simp [hz]
        · have hvnonneg : 0 ≤ v := le_of_not_gt hv0
          by_cases hvpos : 0 < v
          · have hz := prefix_support (Real.log 3) x a hx ha
                (v + Real.log 3) (by
                  intro hmem
                  linarith [hmem.2])
            simp [hz]
          · have hvz : v = 0 := le_antisymm (le_of_not_gt hvpos) hvnonneg
            subst v
            have hFD : «prefix» x a (Real.log 3) = 0 := by
              unfold «prefix»
              have hxi : ∀ i, x i ≤ Real.log 3 := fun i => (hx i).2
              simp [hxi]
              exact ha
            simp [hFD]
      rw [hfun]
      simp
    have hΛ2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
    have hΛ3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 :=
      ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
    rw [primeQuadratic, primes_three_small]
    simp [hΛ2, hΛ3]
    have hcorr3re :
        (∫ v : ℝ, star («prefix» x a (v + Real.log 3)) * «prefix» x a v).re = 0 := by
      rw [hcorr3]
      simp
    have hcorr3re' :
        (∫ v : ℝ, (starRingEnd ℂ) («prefix» x a (v + Real.log 3)) *
          «prefix» x a v).re = 0 := by
      simpa using hcorr3re
    rw [hcorr3re']
    have hcoef2' :
        2 * (Real.log 2 / Real.sqrt 2) *
            (∫ v : ℝ, (starRingEnd ℂ) («prefix» x a (v + Real.log 2)) *
              «prefix» x a v).re ≤ (1 / 2 : ℝ) * energy x a := by
      simpa [hΛ2] using hcoef2
    nlinarith [hcoef2']
  · have hDlt3 : D < Real.log 3 := lt_of_le_of_ne hD3 heq
    rw [primeQuadratic, primes_two_small hD2' hDlt3]
    simp only [Finset.sum_singleton]
    nlinarith [hcoef2]

private lemma q6_mixture_head_lower (D : ℝ) (hD : 0 < D)
    (hD3 : D ≤ Real.log 3) (q : ℕ) (hq : 6 ≤ q)
    (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (2003 / 1000 : ℝ) * energy x a ≤ (quadratic x a P).re := by
  have hq1 : 1 ≤ q := by omega
  have hqR : (6 : ℝ) ≤ q := by exact_mod_cast hq
  have hD11 := small_D_upper hD3
  have hden : 0 < 4 * (q : ℝ) * ((q : ℝ) + 1) := by positivity
  have hDsq : D ^ 2 ≤ (121 / 100 : ℝ) := by nlinarith
  have hqprod : (42 : ℝ) ≤ (q : ℝ) * ((q : ℝ) + 1) := by nlinarith [sq_nonneg ((q : ℝ) - 6)]
  have hgap : D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) ≤ (1 / 138 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := complete_positive_mixture_head_gamma D hD q hq1 20 138 (by norm_num)
    hgap x a hx hm
  have hsum : (2003 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.range 20,
        trivialCoeff n * (2 * rate n / (1 + rate n ^ 2 / (138 : ℝ))) := by
    norm_num [rate, trivialCoeff, Finset.sum_range_succ]
  have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
  nlinarith

private lemma q22_mixture_head_lower (D : ℝ) (hD : 0 < D)
    (hD3 : D ≤ Real.log 3) (q : ℕ) (hq : 22 ≤ q)
    (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (293 / 100 : ℝ) * energy x a ≤ (quadratic x a P).re := by
  have hq1 : 1 ≤ q := by omega
  have hqR : (22 : ℝ) ≤ q := by exact_mod_cast hq
  have hD11 := small_D_upper hD3
  have hden : 0 < 4 * (q : ℝ) * ((q : ℝ) + 1) := by positivity
  have hDsq : D ^ 2 ≤ (121 / 100 : ℝ) := by nlinarith
  have hqprod : (506 : ℝ) ≤ (q : ℝ) * ((q : ℝ) + 1) := by nlinarith [sq_nonneg ((q : ℝ) - 22)]
  have hgap : D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) ≤ (1 / 1600 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hh := complete_positive_mixture_head_gamma D hD q hq1 20 1600 (by norm_num)
    hgap x a hx hm
  have hsum : (293 / 100 : ℝ) ≤
      ∑ n ∈ Finset.range 20,
        trivialCoeff n * (2 * rate n / (1 + rate n ^ 2 / (1600 : ℝ))) := by
    norm_num [rate, trivialCoeff, Finset.sum_range_succ]
  have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
  nlinarith

private lemma actual_K_lower_of_prime_bound (D : ℝ) (hD : 0 < D)
    (hD3 : D ≤ Real.log 3) (q : ℕ) (hq : 1 ≤ q)
    (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0)
    (hprime : primeQuadratic D x a ≤ (1 / 2 : ℝ) * energy x a) :
    (quadratic x a P).re - (959 / 500 : ℝ) * energy x a -
      (297 / 100 : ℝ) * (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * energy x a ≤
        (quadratic x a ActualKernelLocalPositivity.K).re := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have hR := actual_fullR_correlation D hD.le x a hx ha
  have hV := actual_fullR_resolvent_identity D hD.le x a ha
  have hS := actual_resolvent_control D hD q hq x a hx hm
  have hH := actual_continuum_moment_payment D hD q hq x a hx hm
  have hVabs := small_V_abs_bound D hD.le hD3 q hq x a hx hm
  have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
  have hgap0 : 0 ≤ D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) := by positivity
  have hM := small_M_upper hD.le hD3
  have hD11 := small_D_upper hD3
  have hcurv : (M D + D + 3) / 4 ≤ (117 / 80 : ℝ) := by nlinarith
  have hcont : -(117 / 80 : ℝ) *
      (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * energy x a ≤ continuum D x a := by
    have hpay := hH
    have hnon : 0 ≤ (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * energy x a :=
      mul_nonneg hgap0 hE
    nlinarith
  have hVlower : -(603 / 400 : ℝ) *
      (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * energy x a ≤ V D x a := by
    have hw := hS.2.2.1
    have hnon : 0 ≤ (603 / 100 : ℝ) := by norm_num
    have hw' := mul_le_mul_of_nonneg_left hw hnon
    have hVabslo := (abs_le.mp hVabs).1
    nlinarith [hVabslo, hw']
  have hd0lo : 0 ≤ d0 := ActualKScalarSource.d0_nonneg
  have hd0hi : d0 ≤ (709 / 500 : ℝ) := le_of_lt d0_upper_small
  have hd0 : -((709 / 500 : ℝ) * energy x a) ≤ d0 * (W D x a - energy x a) := by
    have hw := hS.1
    nlinarith
  have hsplit : (quadratic x a ActualKernelLocalPositivity.K).re =
      (quadratic x a P).re + (quadratic x a fullR).re := by
    simp only [quadratic, original_K_split, Complex.ofReal_add, mul_add,
      Finset.sum_add_distrib, Complex.add_re]
  nlinarith only [hR, hV, hsplit, hprime, hcont, hVlower, hd0]

private lemma zero_window_quadratic (q : ℕ) (hq : 1 ≤ q)
    (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 0)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    energy x a = 0 ∧ quadratic x a P = 0 ∧
      quadratic x a ActualKernelLocalPositivity.K = 0 := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have hx0 : ∀ i, x i = 0 := by
    intro i
    exact le_antisymm (by simpa using (hx i).2) (by simpa using (hx i).1)
  have hpref : ∀ v : ℝ, «prefix» x a v = 0 := by
    intro v
    by_cases hv : 0 ≤ v
    · simp [«prefix», hx0, hv, ha]
    · simp [«prefix», hx0, hv]
  have henergy : energy x a = 0 := by
    simp [energy, hpref]
  have hquad (f : ℝ → ℝ) : quadratic x a f = 0 := by
    classical
    simp only [quadratic, hx0, sub_self]
    simp [← Finset.mul_sum, ← Finset.sum_mul, ha]
  exact ⟨henergy, hquad P, hquad ActualKernelLocalPositivity.K⟩

/-- Complete actual-K coercivity on the original small window at moment order six. -/
theorem actual_kernel_q6_small_window (D : ℝ) (hD0 : 0 ≤ D)
    (hD3 : D ≤ Real.log 3) (q : ℕ) (hq : 6 ≤ q)
    (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (36 / 575 : ℝ) * energy x a ≤
      (quadratic x a ActualKernelLocalPositivity.K).re := by
  by_cases hzero : D = 0
  · subst D
    have hz := zero_window_quadratic q (by omega) x a hx hm
    rw [hz.1, hz.2.2]
    norm_num
  · have hD : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hzero)
    have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
    have hprime := prime_quadratic_small_bound D hD0 hD3 x a hx ha
    have hP := q6_mixture_head_lower D hD hD3 q hq x a hx hm
    have hK := actual_K_lower_of_prime_bound D hD hD3 q (by omega) x a hx hm hprime
    have hqR : (6 : ℝ) ≤ q := by exact_mod_cast hq
    have hden : 0 < 4 * (q : ℝ) * ((q : ℝ) + 1) := by positivity
    have hDsq : D ^ 2 ≤ (121 / 100 : ℝ) := by
      have hD11 := small_D_upper hD3
      nlinarith
    have hqprod : (42 : ℝ) ≤ (q : ℝ) * ((q : ℝ) + 1) := by
      nlinarith [sq_nonneg ((q : ℝ) - 6)]
    have hgap : D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) ≤ (1 / 138 : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
    nlinarith

/-- Complete actual-K coercivity on the original small window at moment order twenty-two. -/
theorem actual_kernel_q22_small_window (D : ℝ) (hD0 : 0 ≤ D)
    (hD3 : D ≤ Real.log 3) (q : ℕ) (hq : 22 ≤ q)
    (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (2017 / 2000 : ℝ) * energy x a ≤
        (quadratic x a ActualKernelLocalPositivity.K).re ∧
      energy x a ≤ (quadratic x a ActualKernelLocalPositivity.K).re := by
  by_cases hzero : D = 0
  · subst D
    have hz := zero_window_quadratic q (by omega) x a hx hm
    rw [hz.1, hz.2.2]
    norm_num
  · have hD : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hzero)
    have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
    have hprime := prime_quadratic_small_bound D hD0 hD3 x a hx ha
    have hP := q22_mixture_head_lower D hD hD3 q hq x a hx hm
    have hK := actual_K_lower_of_prime_bound D hD hD3 q (by omega) x a hx hm hprime
    have hqR : (22 : ℝ) ≤ q := by exact_mod_cast hq
    have hden : 0 < 4 * (q : ℝ) * ((q : ℝ) + 1) := by positivity
    have hDsq : D ^ 2 ≤ (121 / 100 : ℝ) := by
      have hD11 := small_D_upper hD3
      nlinarith
    have hqprod : (506 : ℝ) ≤ (q : ℝ) * ((q : ℝ) + 1) := by
      nlinarith [sq_nonneg ((q : ℝ) - 22)]
    have hgap : D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) ≤ (1 / 1600 : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
    constructor <;> nlinarith

private lemma d0_nonneg : 0 ≤ d0 :=
  ActualKScalarSource.d0_nonneg

/-- Full original remainder, with every H/V/b(D) correction paid. -/
private theorem actual_remainder_prefix_bound_leading_one (p : PNTConstants)
    (D : ℝ) (hD : 0 < D) (q : ℕ) (hq : 1 ≤ q)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ q → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (quadratic x a P).re -
      (d0 + beta p D + D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1)) * curvature p D) * energy x a ≤
        (quadratic x a ActualKernelLocalPositivity.K).re := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le q)
  have hT := actual_weighted_mangoldt_translation_bound p D x a hx ha
  have hR := actual_fullR_correlation D hD.le x a hx ha
  have hV := actual_fullR_resolvent_identity D hD.le x a ha
  have hS := actual_resolvent_control D hD q hq x a hx hm
  have hH := actual_continuum_moment_payment D hD q hq x a hx hm
  have hcut := actual_cutoff_resolvent_payment p D hD x a hx ha
  have hcoeff : 0 ≤ (8 + 4 * p.C + 2 * B p) * M D := by
    have hb := p.one_le_C.trans (B_ge_C p)
    have hC := p.one_le_C
    exact mul_nonneg (by linarith) (Real.exp_nonneg _)
  have hVlower : -((8 + 4 * p.C + 2 * B p) * M D *
      (D ^ 2 / (4 * (q : ℝ) * ((q : ℝ) + 1))) * energy x a / 4) ≤ V D x a := by
    have h := mul_le_mul_of_nonneg_left hS.2.2.1 hcoeff
    have hl := (abs_le.mp hcut).1
    nlinarith only [h, hl]
  have hdW : 0 ≤ d0 * W D x a := mul_nonneg d0_nonneg hS.1
  have hsplit : (quadratic x a ActualKernelLocalPositivity.K).re =
      (quadratic x a P).re + (quadratic x a fullR).re := by
    simp only [quadratic, original_K_split, Complex.ofReal_add, mul_add,
      Finset.sum_add_distrib, Complex.add_re]
  dsimp only [curvature]
  nlinarith only [hT, hR, hV, hH, hVlower, hdW, hsplit]

/-- Exact arithmetic supplied by the compiled scalar owner at the same ceiling. -/
private theorem original_order_arithmetic (p : PNTConstants) (D : ℝ) (hD : 0 < D) :
    1 ≤ order p D ∧ 8 ≤ (order p D : ℝ) / D ∧
      D ^ 2 / (4 * (order p D : ℝ) * ((order p D : ℝ) + 1)) * curvature p D ≤ (1 / 8 : ℝ) ∧
        beta p D + d0 + 2 + 1 / 5 ≤ Real.log ((order p D : ℝ) / D) := by
  exact ActualKScalarSource.q_scalar_bounds p.C p.alpha D p.one_le_C hD

/-- The original actual-K certificate at exactly the displayed N(D).
The fixed unconditional pnt witnesses precede every finite atomic family.
Atomic moments include degree N. No distinctness, nonempty type,
positive-energy or real-coefficient restriction occurs. -/
theorem actual_kernel_explicit_leading_one (D : ℝ) (hD : 0 < D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ order pnt D → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    energy x a ≤ (quadratic x a ActualKernelLocalPositivity.K).re := by
  have hq := original_order_arithmetic pnt D hD
  have hP := complete_positive_mixture_logarithmic
    D hD (order pnt D) hq.1 hq.2.1 x a hx hm
  have hR := actual_remainder_prefix_bound_leading_one
    pnt D hD (order pnt D) hq.1 x a hx hm
  have hE : 0 ≤ energy x a := integral_nonneg (fun _ => sq_nonneg _)
  have hlog := mul_le_mul_of_nonneg_right hq.2.2.2 hE
  have hpay := mul_le_mul_of_nonneg_right hq.2.2.1 hE
  nlinarith only [hP, hR, hlog, hpay, hE]

/-- Compensation for the explicitly defined finite formula only. Equality
with an independently defined original signed-J integral is an additional,
separate obligation and is not assumed or asserted here. -/
theorem actual_signed_expression_compensation (D : ℝ) (hD : 0 < D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hm : ∀ r : ℕ, r ≤ order pnt D → ∑ i, a i * (x i : ℂ) ^ r = 0) :
    (Real.log (2 * Real.pi) - 1 - Real.eulerMascheroniConstant) *
      (energy x a - W D x a) - (quadratic x a P).re + energy x a ≤ signedJExpression D x a := by
  have ha : ∑ i, a i = 0 := by simpa using hm 0 (Nat.zero_le _)
  have hK := actual_kernel_explicit_leading_one D hD x a hx hm
  have hR := actual_fullR_correlation D hD.le x a hx ha
  have hV := actual_fullR_resolvent_identity D hD.le x a ha
  have hsplit : (quadratic x a ActualKernelLocalPositivity.K).re =
      (quadratic x a P).re + (quadratic x a fullR).re := by
    simp only [quadratic, original_K_split, Complex.ofReal_add, mul_add,
      Finset.sum_add_distrib, Complex.add_re]
  dsimp only [signedJExpression, d0] at *
  linarith only [hK, hR, hV, hsplit]


end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
