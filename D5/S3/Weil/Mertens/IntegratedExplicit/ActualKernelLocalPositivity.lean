/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local positive representation of the complete arithmetic prime kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import D5.S3.Analytic.ExpRatioCM.Series
import D5.S3.Analytic.Fourier.PositiveDefinite.Closure
import D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! A positive triangle representation of the literal complete arithmetic kernel on one window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ComplexOrder
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Analytic.ExpRatioCM.Series

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

/-- The full arithmetic kernel, retaining every Mangoldt ramp and trivial zero. -/
def K (t : ℝ) : ℝ :=
  Real.exp (-|t| / 2) * (U (Real.exp |t|) - Real.log (2 * Real.pi) + trivialT |t|)

private def b : ℕ → ℝ
  | 0 => 0
  | n + 1 => trivialCoeff n

private lemma b_bound (n : ℕ) : |b n| ≤ (1 : ℝ) ^ n := by
  cases n with
  | zero => simp [b]
  | succ n =>
    rw [b, abs_of_nonneg (trivialCoeff_nonneg n), one_pow]
    unfold trivialCoeff
    apply (div_le_one (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

private lemma trivialT_eq_weighted {t : ℝ} (ht : 0 < t) : trivialT t = weightedSeries b 0 (2 * t) := by
  symm
  unfold weightedSeries
  rw [((summable_weighted (t := 2 * t) zero_lt_one b_bound 0 (by simpa using (show 0 < 2 * t by linarith))).of_norm).tsum_eq_zero_add]
  simp only [b, Nat.cast_zero, pow_zero, mul_one, zero_mul, neg_zero, Real.exp_zero,
    zero_add, Nat.cast_add, Nat.cast_one]
  congr 1
  funext n
  congr 2
  ring

private lemma mangoldtPart_exp_eq_zero {t : ℝ} (ht : t < Real.log 2) :
    mangoldtPart (Real.exp t) = 0 := by
  suffices hh : ∀ n, mangoldtRamp n (Real.exp t) = 0 by
    simp only [mangoldtPart, hh, tsum_zero]
  intro n
  rcases n with _ | _ | n
  · simp [mangoldtRamp]
  · simp [mangoldtRamp]
  · have hn : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    have he : Real.exp t < (n + 2 : ℕ) :=
      (Real.exp_lt_exp.mpr ht).trans_le (by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) n])
    rw [mangoldtRamp, max_eq_right (by
      have := (div_lt_one hn).mpr he
      linarith), mul_zero]

lemma K_eq_local {t : ℝ} (ht : 0 ≤ t) (ht2 : t < Real.log 2) :
    K t = Real.exp (-t / 2) *
      (Real.exp t * (1 + Real.eulerMascheroniConstant - t) -
        Real.log (2 * Real.pi) + trivialT t) := by
  rw [K, abs_of_nonneg ht, U_eq_complete_ramps (Real.exp_nonneg t),
    mangoldtPart_exp_eq_zero ht2, Real.log_exp]
  ring

lemma K_zero : K 0 = firstLiMass := by
  rw [K_eq_local le_rfl (Real.log_pos (by norm_num)), firstLiMass_split]
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one, sub_zero, one_mul]
  have hT : trivialT 0 = 1 - Real.log 2 := by
    simpa [trivialT] using trivialCoeff_hasSum.tsum_eq
  rw [hT, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

private lemma K_zero_pos : 0 < K 0 := by
  rw [K_zero, firstLiMass]
  linarith [D5.S3.Zeros.Endpoints.FirstLiCoefficientPositivity.first_li_coefficient_pos]

private lemma log_series {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-(n : ℝ) * (2 * t)) / (n : ℝ))
      (-Real.log (1 - Real.exp (-(2 * t)))) := by
  have he : Real.exp (-(2 * t)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log
    (z := (Real.exp (-(2 * t)) : ℂ)) (by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)] using he))
  convert hs using 1
  · funext n
    rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast,
      ← Complex.ofReal_div, Complex.ofReal_re, ← Real.exp_nat_mul]
    congr 2
    ring
  · rw [show (1 : ℂ) - (Real.exp (-(2 * t)) : ℂ) =
        ((1 - Real.exp (-(2 * t)) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log (by linarith : 0 ≤ 1 - Real.exp (-(2 * t)))]
    simp

private lemma trivialT_derivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt trivialT (trivialT t + Real.log (1 - Real.exp (-(2 * t))) / 2) t := by
  have hw (k : ℕ) := (summable_weighted (t := 2 * t) zero_lt_one b_bound k
    (by simpa using (show 0 < 2 * t by linarith))).of_norm
  have hs := (hw 0).hasSum.add ((hw 1).hasSum.mul_left 2)
  have heq : weightedSeries b 0 (2 * t) + 2 * weightedSeries b 1 (2 * t) =
      -Real.log (1 - Real.exp (-(2 * t))) / 2 := by
    apply HasSum.unique hs ?_
    convert (log_series ht).div_const 2 using 1
    funext n
    cases n with
    | zero => simp [b]
    | succ n =>
      simp only [b, pow_zero, mul_one, pow_one, Nat.cast_add, Nat.cast_one]
      unfold trivialCoeff
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn' : 2 * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
      field_simp [hn, hn']
      <;> ring
  have hd := (hasDerivAt_weighted (t := 2 * t) zero_lt_one b_bound 0
    (by simpa using (show 0 < 2 * t by linarith))).comp t
      ((hasDerivAt_id t).const_mul 2)
  have hloc : trivialT =ᶠ[𝓝 t] (fun u => weightedSeries b 0 (2 * u)) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu using trivialT_eq_weighted hu
  convert hd.congr_of_eventuallyEq hloc using 1
  rw [trivialT_eq_weighted ht]
  simp only [id_eq, Nat.zero_add, mul_one]
  linarith

def D1 (t : ℝ) : ℝ := K t / 2 - Real.exp (t / 2) +
  Real.exp (-t / 2) * (Real.log (2 * Real.pi) + Real.log (1 - Real.exp (-(2 * t))) / 2)

def D2 (t : ℝ) : ℝ := K t / 4 - Real.exp (t / 2) +
  Real.exp (-t / 2) / (Real.exp (2 * t) - 1)

lemma hasDerivAt_K {t : ℝ} (ht : 0 < t) (ht2 : t < Real.log 2) :
    HasDerivAt K (D1 t) t := by
  have hd := (((hasDerivAt_id t).neg.div_const 2).exp).mul
    ((((Real.hasDerivAt_exp t).mul
      ((hasDerivAt_const t (1 + Real.eulerMascheroniConstant)).sub (hasDerivAt_id t))).sub_const
        (Real.log (2 * Real.pi))).add (trivialT_derivative ht))
  have hloc : K =ᶠ[𝓝 t] (fun u => Real.exp (-u / 2) *
      (Real.exp u * (1 + Real.eulerMascheroniConstant - u) -
        Real.log (2 * Real.pi) + trivialT u)) := by
    filter_upwards [Ioo_mem_nhds ht ht2] with u hu using K_eq_local hu.1.le hu.2
  convert hd.congr_of_eventuallyEq hloc using 1
  rw [D1, K_eq_local ht.le ht2]
  have he : Real.exp (t / 2) = Real.exp (-t / 2) * Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  dsimp
  ring

private lemma log_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u))))
      (2 / (Real.exp (2 * t) - 1)) t := by
  have hpos : 0 < 2 * t := by linarith
  have hsmooth :=
    D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives.log_one_sub_exp_derivatives.1
  have hd := (hsmooth.differentiableOn (by norm_num)).differentiableAt
    (Ioi_mem_nhds hpos)
  have hh := hd.hasDerivAt
  rw [(D5.S3.Analytic.Interpolation.LogOneSubExpDerivatives.log_one_sub_exp_derivatives.2
    (2 * t) hpos).1] at hh
  convert hh.comp t ((hasDerivAt_id t).const_mul 2) using 1
  · rfl
  · ring

lemma hasDerivAt_D1 {t : ℝ} (ht : 0 < t) (ht2 : t < Real.log 2) :
    HasDerivAt D1 (D2 t) t := by
  have hd := (((hasDerivAt_K ht ht2).div_const 2).sub
    (((hasDerivAt_id t).div_const 2).exp)).add
      ((((hasDerivAt_id t).neg.div_const 2).exp).mul
        ((hasDerivAt_const t (Real.log (2 * Real.pi))).add
          ((log_hasDerivAt ht).div_const 2)))
  convert hd using 1
  · rfl
  · dsimp only [D1, D2]
    dsimp
    ring

lemma K_continuous : Continuous K := by
  have hT : Continuous (fun t : ℝ => trivialT |t|) :=
    trivialT_continuousOn.comp_continuous continuous_abs (fun t => abs_nonneg t)
  exact (show Continuous (fun t : ℝ => Real.exp (-|t| / 2)) by fun_prop).mul
    (((U_exp_continuous.comp continuous_abs).sub continuous_const).add hT)

private lemma exp_ratio_limit :
    Tendsto (fun t : ℝ => t / (Real.exp (2 * t) - 1)) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul 2).exp).tendsto_slope_zero_right
  have hh : Tendsto (fun t : ℝ => (Real.exp (2 * t) - 1) / t) (𝓝[>] 0) (𝓝 2) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  convert hh.inv₀ (by norm_num : (2 : ℝ) ≠ 0) using 1 <;> simp [one_div]

lemma log_argument_ratio_limit :
    Tendsto (fun t : ℝ => t / (1 - Real.exp (-(2 * t)))) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hd := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
    (((hasDerivAt_id (0 : ℝ)).const_mul (-2)).exp)).tendsto_slope_zero_right
  have hh : Tendsto (fun t : ℝ => (1 - Real.exp (-(2 * t))) / t) (𝓝[>] 0) (𝓝 2) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
  convert hh.inv₀ (by norm_num : (2 : ℝ) ≠ 0) using 1 <;> simp [one_div]

private lemma weighted_log_limit :
    Tendsto (fun t : ℝ => t * Real.log (1 - Real.exp (-(2 * t))))
      (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun t : ℝ => 1 - Real.exp (-(2 * t))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (show ContinuousAt (fun t : ℝ => 1 - Real.exp (-(2 * t))) 0 by
      fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  have hm := log_argument_ratio_limit.mul (Real.continuous_mul_log.continuousAt.tendsto.comp hc)
  simp only [Real.log_zero, mul_zero] at hm
  apply hm.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hne : 1 - Real.exp (-(2 * t)) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith : -(2 * t) < 0))).ne'
  dsimp only [Function.comp_def]
  rw [← mul_assoc, div_mul_cancel₀ _ hne]

lemma D1_atBot : Tendsto D1 (𝓝[>] 0) atBot := by
  have hc : Tendsto (fun t : ℝ => 1 - Real.exp (-(2 * t))) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (show ContinuousAt (fun t : ℝ => 1 - Real.exp (-(2 * t))) 0 by
        fun_prop).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith : -(2 * t) < 0))
  have hl := Real.tendsto_log_nhdsGT_zero.comp hc
  have he : Tendsto (fun t : ℝ => Real.exp (-t / 2) / 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
    simpa using (show ContinuousAt (fun t : ℝ => Real.exp (-t / 2) / 2) 0 by
      fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  have hbase : Continuous (fun t : ℝ => K t / 2 - Real.exp (t / 2) +
      Real.exp (-t / 2) * Real.log (2 * Real.pi)) :=
    ((K_continuous.div_const 2).sub (by fun_prop)).add (by fun_prop)
  have hb : Tendsto (fun t : ℝ => K t / 2 - Real.exp (t / 2) +
      Real.exp (-t / 2) * Real.log (2 * Real.pi)) (𝓝[>] 0)
      (𝓝 (K 0 / 2 - 1 + Real.log (2 * Real.pi))) := by
    simpa using (hbase.tendsto 0).mono_left nhdsWithin_le_nhds
  convert hb.add_atBot (he.pos_mul_atBot (by norm_num) hl) using 1
  ext t
  dsimp [D1]
  ring

private lemma weighted_D1_limit :
    Tendsto (fun t : ℝ => t * D1 t) (𝓝[>] 0) (𝓝 0) := by
  have hb : Continuous (fun t : ℝ => K t / 2 - Real.exp (t / 2) +
      Real.exp (-t / 2) * Real.log (2 * Real.pi)) :=
    ((K_continuous.div_const 2).sub (by fun_prop)).add (by fun_prop)
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 := ht.mul ((hb.tendsto 0).mono_left nhdsWithin_le_nhds)
  have he : Continuous (fun t : ℝ => Real.exp (-t / 2) / 2) := by fun_prop
  have h2 := ((he.tendsto 0).mono_left nhdsWithin_le_nhds).mul weighted_log_limit
  convert h1.add h2 using 1
  · ext t; dsimp [D1]; ring
  · simp

private lemma weighted_D2_limit :
    Tendsto (fun t : ℝ => t * D2 t) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have hK : Tendsto K (𝓝[>] 0) (𝓝 (K 0)) :=
    (K_continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have he (c : ℝ) : Tendsto (fun t : ℝ => Real.exp (c * t)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (c * t)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  convert ((ht.mul hK).div_const 4 |>.sub (ht.mul (he (1/2)))).add
    ((he (-1/2)).mul exp_ratio_limit) using 1
  · ext t; dsimp [D2]; ring
  · norm_num

private lemma D2_continuousOn : ContinuousOn D2 (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hden : Real.exp (2 * t) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))).ne'
  exact (((K_continuous.continuousAt.div_const 4).sub (by fun_prop)).add
    ((show ContinuousAt (fun t : ℝ => Real.exp (-t / 2)) t by fun_prop).div
      (by fun_prop) hden)).continuousWithinAt

private lemma choose_window : ∃ δ : ℝ, 0 < δ ∧ δ < Real.log 2 ∧
    (∀ t ∈ Ioc 0 δ, 0 < K t ∧ D1 t < 0 ∧ 0 < D2 t ∧ t * D2 t < 1) ∧
    IntegrableOn (fun t : ℝ => t * D2 t) (Ioc 0 δ) := by
  have hK : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < K t :=
    (K_continuous.continuousAt.eventually (lt_mem_nhds K_zero_pos)).filter_mono
      nhdsWithin_le_nhds
  have hD1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), D1 t < 0 :=
    D1_atBot.eventually (eventually_lt_atBot 0)
  have hD2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t * D2 t ∧ t * D2 t < 1 :=
    weighted_D2_limit.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hlog : ∀ᶠ t : ℝ in 𝓝 0, t < Real.log 2 :=
    Iio_mem_nhds (Real.log_pos (by norm_num))
  have hwin : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t < Real.log 2 ∧ 0 < K t ∧ D1 t < 0 ∧ 0 < t * D2 t ∧ t * D2 t < 1 := by
    filter_upwards [hlog.filter_mono nhdsWithin_le_nhds, hK, hD1, hD2] with t ht hkt hd1 hd2
    exact ⟨ht, hkt, hd1, hd2⟩
  obtain ⟨δ, hδ, hall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hwin
  have hsδ := hall (show δ ∈ Ioc 0 δ from ⟨hδ, le_rfl⟩)
  have hpos (t : ℝ) (ht : t ∈ Ioc 0 δ) : 0 < D2 t :=
    (mul_pos_iff_of_pos_left ht.1).mp (hall ht).2.2.2.1
  refine ⟨δ, hδ, hsδ.1, (fun t ht =>
    ⟨(hall ht).2.1, (hall ht).2.2.1, hpos t ht, (hall ht).2.2.2.2⟩), ?_⟩
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 δ) :=
    (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  apply hi.mono'
  · exact ((continuousOn_id.mul D2_continuousOn).mono
      (fun _ ht => ht.1)).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (hall ht).2.2.2.1]
    exact (hall ht).2.2.2.2.le

private lemma triangle_integrable {δ u : ℝ} (hu : 0 ≤ u)
    (hpos : ∀ t ∈ Ioc 0 δ, 0 < D2 t)
    (hi : IntegrableOn (fun t : ℝ => t * D2 t) (Ioc 0 δ)) :
    IntegrableOn (fun t : ℝ => max (t - u) 0 * D2 t) (Ioc 0 δ) := by
  apply hi.mono'
  · have hc : ContinuousOn (fun t : ℝ => max (t - u) 0 * D2 t) (Ioi 0) :=
      (show Continuous (fun t : ℝ => max (t - u) 0) by fun_prop).continuousOn.mul
        D2_continuousOn
    exact (hc.mono (fun _ ht => ht.1)).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (hpos t ht).le)]
    exact mul_le_mul_of_nonneg_right (max_le (by linarith) ht.1.le) (hpos t ht).le

private lemma zero_endpoint_integral {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < Real.log 2)
    (hi : IntegrableOn (fun t : ℝ => t * D2 t) (Ioc 0 δ)) :
    (∫ t : ℝ in Ioc 0 δ, t * D2 t) = δ * D1 δ - K δ + K 0 := by
  have hd (t : ℝ) (ht : t ∈ Ioo 0 δ) :
      HasDerivAt (fun s : ℝ => s * D1 s - K s) (t * D2 t) t := by
    convert ((hasDerivAt_id t).mul (hasDerivAt_D1 ht.1 (ht.2.trans hδ2))).sub
      (hasDerivAt_K ht.1 (ht.2.trans hδ2)) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hleft : Tendsto (fun t : ℝ => t * D1 t - K t) (𝓝[>] 0) (𝓝 (-K 0)) := by
    simpa using weighted_D1_limit.sub ((K_continuous.tendsto 0).mono_left nhdsWithin_le_nhds)
  have hcont : ContinuousAt (fun t : ℝ => t * D1 t - K t) δ :=
    (continuousAt_id.mul (hasDerivAt_D1 hδ hδ2).continuousAt).sub
      K_continuous.continuousAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hδ hd
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).mpr hi) hleft
    (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  rw [intervalIntegral.integral_of_le hδ.le] at hh
  simpa only [sub_neg_eq_add] using hh

private lemma positive_endpoint_integral {δ u : ℝ} (hu : 0 < u) (huδ : u ≤ δ)
    (hδ2 : δ < Real.log 2) :
    (∫ t : ℝ in Ioc u δ, (t - u) * D2 t) = (δ - u) * D1 δ - K δ + K u := by
  have hd (t : ℝ) (ht : t ∈ Icc u δ) :
      HasDerivAt (fun s : ℝ => (s - u) * D1 s - K s) ((t - u) * D2 t) t := by
    have ht0 := hu.trans_le ht.1
    have ht2 := ht.2.trans_lt hδ2
    convert (((hasDerivAt_id t).sub_const u).mul (hasDerivAt_D1 ht0 ht2)).sub
      (hasDerivAt_K ht0 ht2) using 1
    · rfl
    · dsimp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      ring
  have hc : ContinuousOn (fun t : ℝ => (t - u) * D2 t) (Icc u δ) :=
    (continuous_id.sub continuous_const).continuousOn.mul
      (D2_continuousOn.mono (fun _ ht => hu.trans_le ht.1))
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le huδ] using ht))
    (hc.intervalIntegrable_of_Icc huδ)
  rw [intervalIntegral.integral_of_le huδ] at hh
  simpa using hh

private lemma triangle_integral {δ u : ℝ} (hδ : 0 < δ) (hδ2 : δ < Real.log 2)
    (hu : 0 ≤ u) (huδ : u ≤ δ) (hpos : ∀ t ∈ Ioc 0 δ, 0 < D2 t)
    (hi : IntegrableOn (fun t : ℝ => t * D2 t) (Ioc 0 δ)) :
    (∫ t : ℝ in Ioc 0 δ, max (t - u) 0 * D2 t) =
      (δ - u) * D1 δ - K δ + K u := by
  rcases eq_or_lt_of_le hu with rfl | hu0
  · simp only [sub_zero]
    rw [← zero_endpoint_integral hδ hδ2 hi]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [max_eq_left ht.1.le]
  have hfi := triangle_integrable hu hpos hi
  have hfu : IntervalIntegrable (fun t : ℝ => max (t - u) 0 * D2 t) volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hu).mpr
      (hfi.mono_set (fun t ht => ⟨ht.1, ht.2.trans huδ⟩))
  have hfuδ : IntervalIntegrable (fun t : ℝ => max (t - u) 0 * D2 t) volume u δ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huδ).mpr
      (hfi.mono_set (fun t ht => ⟨hu0.trans ht.1, ht.2⟩))
  have hz : (∫ t : ℝ in (0 : ℝ)..u, max (t - u) 0 * D2 t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    exact ae_of_all _ (fun t ht => by
      rw [uIoc_of_le hu] at ht
      rw [max_eq_right (by linarith [ht.2]), zero_mul])
  have he : (∫ t : ℝ in u..δ, max (t - u) 0 * D2 t) =
      ∫ t : ℝ in Ioc u δ, (t - u) * D2 t := by
    rw [intervalIntegral.integral_of_le huδ]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [max_eq_left (sub_nonneg.mpr ht.1.le)]
  have hh := intervalIntegral.integral_add_adjacent_intervals hfu hfuδ
  rw [hz, zero_add, he, intervalIntegral.integral_of_le hδ.le] at hh
  rw [← hh]
  exact positive_endpoint_integral hu0 huδ hδ2

/-- The positive mixing density is weighted by the triangle height at the singular endpoint. -/
private lemma actual_positive_representer : ∃ δ r L : ℝ,
    0 < δ ∧ δ < Real.log 2 ∧ 0 < r ∧ δ < L ∧
    (∀ s ∈ Ioc 0 δ, 0 < D2 s) ∧
    IntegrableOn (fun s : ℝ => s * D2 s) (Ioc 0 δ) ∧
    (∀ t : ℝ, |t| ≤ δ →
      IntegrableOn (fun s : ℝ => max (s - |t|) 0 * D2 s) (Ioc 0 δ) ∧
      K t = (∫ s : ℝ in Ioc 0 δ, max (s - |t|) 0 * D2 s) + r * max (L - |t|) 0) := by
  obtain ⟨δ, hδ, hδ2, hsign, hi⟩ := choose_window
  let r : ℝ := -D1 δ
  have hr : 0 < r := neg_pos.mpr (hsign δ ⟨hδ, le_rfl⟩).2.1
  let L : ℝ := δ + K δ / r
  have hL : δ < L := lt_add_of_pos_right _ (div_pos (hsign δ ⟨hδ, le_rfl⟩).1 hr)
  have hpos : ∀ s ∈ Ioc 0 δ, 0 < D2 s := fun s hs => (hsign s hs).2.2.1
  refine ⟨δ, r, L, hδ, hδ2, hr, hL, hpos, hi, ?_⟩
  intro t ht
  refine ⟨triangle_integrable (abs_nonneg t) hpos hi, ?_⟩
  rw [triangle_integral hδ hδ2 (abs_nonneg t) ht hpos hi,
    max_eq_left (sub_nonneg.mpr (ht.trans hL.le))]
  have heven : K |t| = K t := by simp only [K, abs_abs]
  rw [heven]
  have hD1ne : D1 δ ≠ 0 := by
    exact (hsign δ ⟨hδ, le_rfl⟩).2.1.ne
  dsimp [L, r]
  field_simp [hD1ne]
  <;> ring

private def intervalVector (s a u : ℝ) : ℂ := (Icc a (a + s)).indicator (fun _ => 1) u

private lemma intervalVector_conj (s a u : ℝ) :
    star (intervalVector s a u) = intervalVector s a u := by
  by_cases h : u ∈ Icc a (a + s) <;> simp [intervalVector, h]

private lemma interval_overlap (s a b : ℝ) :
    Integrable (fun u : ℝ => intervalVector s a u * intervalVector s b u) ∧
    (∫ u : ℝ, intervalVector s a u * intervalVector s b u) =
      (max (s - |a - b|) 0 : ℝ) := by
  have he : (fun u : ℝ => intervalVector s a u * intervalVector s b u) =
      (Icc (max a b) (min (a + s) (b + s))).indicator (fun _ => (1 : ℂ)) := by
    ext u
    rw [← Icc_inter_Icc]
    by_cases ha : u ∈ Icc a (a + s) <;>
      by_cases hb : u ∈ Icc b (b + s) <;> simp [intervalVector, ha, hb]
  rw [he]
  refine ⟨(integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (by simp [Real.volume_Icc])), ?_⟩
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc,
    Complex.real_smul, mul_one]
  congr 2
  by_cases hab : a ≤ b
  · rw [min_eq_left (show a + s ≤ b + s by linarith), max_eq_right hab,
      abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · have hba := le_of_not_ge hab
    rw [min_eq_right (show b + s ≤ a + s by linarith), max_eq_left hba,
      abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

private lemma triangle_quadratic {n : ℕ} (s : ℝ) (x : Fin n → ℝ) (c : Fin n → ℂ) :
    Integrable (fun u : ℝ => Complex.normSq (∑ i, intervalVector s (x i) u * c i)) ∧
    (∫ u : ℝ, (Complex.normSq (∑ i, intervalVector s (x i) u * c i) : ℂ)) =
      star c ⬝ᵥ ((fun i j => ((max (s - |x i - x j|) 0 : ℝ) : ℂ)) *ᵥ c) := by
  have he (u : ℝ) :
      (Complex.normSq (∑ i, intervalVector s (x i) u * c i) : ℂ) =
      ∑ i, ∑ j, star (c i) *
        (intervalVector s (x i) u * intervalVector s (x j) u) * c j := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, starRingEnd_apply, intervalVector_conj]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi (i j : Fin n) : Integrable (fun u : ℝ =>
      star (c i) * (intervalVector s (x i) u * intervalVector s (x j) u) * c j) :=
    ((interval_overlap s (x i) (x j)).1.const_mul _).mul_const _
  have his : Integrable (fun u : ℝ => ∑ i, ∑ j, star (c i) *
      (intervalVector s (x i) u * intervalVector s (x j) u) * c j) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  have hic : Integrable (fun u : ℝ =>
      (Complex.normSq (∑ i, intervalVector s (x i) u * c i) : ℂ)) :=
    his.congr (ae_of_all _ (fun u => (he u).symm))
  refine ⟨?_, ?_⟩
  · simpa using hic.re
  · simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_mul_const,
      integral_const_mul, (interval_overlap s _ _).2]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]

private lemma triangle_hermitian {n : ℕ} (s : ℝ) (x : Fin n → ℝ) :
    Matrix.IsHermitian (fun i j => ((max (s - |x i - x j|) 0 : ℝ) : ℂ)) := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [Complex.star_def, Complex.conj_ofReal, abs_sub_comm]

private lemma triangle_posSemidef {n : ℕ} (s : ℝ) (x : Fin n → ℝ) :
    Matrix.PosSemidef (fun i j => ((max (s - |x i - x j|) 0 : ℝ) : ℂ)) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (triangle_hermitian s x)
  intro c
  rw [← (triangle_quadratic s x c).2, integral_complex_ofReal]
  exact_mod_cast (integral_nonneg (fun u => Complex.normSq_nonneg _))

private lemma triangle_posDef {n : ℕ} {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ)
    (hx : Function.Injective x) :
    Matrix.PosDef (fun i j => ((max (s - |x i - x j|) 0 : ℝ) : ℂ)) := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (triangle_hermitian s x)
  intro c hc
  have hn : ({i : Fin n | c i ≠ 0} : Set (Fin n)).Nonempty := by
    by_contra h
    apply hc
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i₀, hi₀, hmin⟩ :=
    Set.exists_min_image ({i : Fin n | c i ≠ 0}) x (Set.toFinite _) hn
  have hterm (i : Fin n) : ∀ᶠ u in 𝓝[>] (x i₀),
      intervalVector s (x i) u * c i = if i = i₀ then c i₀ else 0 := by
    by_cases hi : i = i₀
    · subst i
      have hupp : ∀ᶠ u : ℝ in 𝓝 (x i₀), u < x i₀ + s :=
        Iio_mem_nhds (lt_add_of_pos_right (x i₀) hs)
      filter_upwards [self_mem_nhdsWithin, hupp.filter_mono nhdsWithin_le_nhds]
        with u hu hu'
      rw [if_pos rfl, intervalVector, indicator_of_mem (show u ∈ Icc (x i₀) (x i₀ + s)
        from ⟨hu.le, hu'.le⟩), one_mul]
    · by_cases hci : c i = 0
      · exact Filter.Eventually.of_forall (fun u => by simp [hi, hci])
      · have hxi : x i₀ < x i := lt_of_le_of_ne (hmin i hci)
          (fun e => hi (hx e.symm))
        have hupp : ∀ᶠ u : ℝ in 𝓝 (x i₀), u < x i := Iio_mem_nhds hxi
        filter_upwards [hupp.filter_mono nhdsWithin_le_nhds] with u hu
        simp only [if_neg hi, intervalVector,
          indicator_of_notMem (show u ∉ Icc (x i) (x i + s) from fun h =>
            (not_lt_of_ge h.1) hu), zero_mul]
  have hsum : ∀ᶠ u in 𝓝[>] (x i₀), ∑ i, intervalVector s (x i) u * c i = c i₀ := by
    filter_upwards [Filter.eventually_all.mpr hterm] with u hu
    simp_rw [hu]
    simp
  have hsupport : ∀ᶠ u in 𝓝[>] (x i₀),
      u ∈ Function.support (fun u : ℝ => Complex.normSq (∑ i, intervalVector s (x i) u * c i)) :=
    hsum.mono (fun u hu => by
      change Complex.normSq (∑ i, intervalVector s (x i) u * c i) ≠ 0
      rw [hu]
      exact (Complex.normSq_pos.mpr hi₀).ne')
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hsupport
  have hvol : 0 < volume (Ioc (x i₀) b) := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hb)
  have hq : 0 < ∫ u : ℝ, Complex.normSq (∑ i, intervalVector s (x i) u * c i) :=
    (integral_pos_iff_support_of_nonneg (fun u => Complex.normSq_nonneg _)
      (triangle_quadratic s x c).1).mpr (hvol.trans_le (measure_mono hsub))
  rw [← (triangle_quadratic s x c).2, integral_complex_ofReal]
  exact_mod_cast hq

/-- One arithmetic window works for every finite family of distinct real nodes and complex coefficients. -/
theorem exists_window_posDef : ∃ δ : ℝ, 0 < δ ∧ δ < Real.log 2 ∧
    ∀ n : ℕ, 1 ≤ n → ∀ x : Fin n → ℝ, Function.Injective x →
      (∀ i j, |x i - x j| ≤ δ) →
      Matrix.PosDef (fun i j => (K (x i - x j) : ℂ)) := by
  obtain ⟨δ, r, L, hδ, hδ2, hr, hL, hpos, hi, hrep⟩ := actual_positive_representer
  refine ⟨δ, hδ, hδ2, ?_⟩
  intro n _hn x hx hdiam
  have hPD : D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite
      (fun t : ℝ => ∫ s : ℝ in Ioc 0 δ,
        ((max (s - |t|) 0 * D2 s : ℝ) : ℂ)) := by
    apply D5.S3.Analytic.Fourier.PositiveDefinite.Closure.integral
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro m y
      have heq : (fun i j : Fin m => ((max (s - |y j - y i|) 0 * D2 s : ℝ) : ℂ)) =
          D2 s • (fun i j : Fin m => ((max (s - |y i - y j|) 0 : ℝ) : ℂ)) := by
        ext i j
        simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul, abs_sub_comm]
        ring
      rw [heq]
      exact (triangle_posSemidef s y).smul (hpos s hs).le
    · intro t
      exact (triangle_integrable (abs_nonneg t) hpos hi).ofReal
  have hmix : Matrix.PosSemidef (fun i j =>
      ((∫ s : ℝ in Ioc 0 δ, max (s - |x i - x j|) 0 * D2 s : ℝ) : ℂ)) := by
    simpa only [integral_complex_ofReal, abs_sub_comm] using hPD n x
  have hwide := (triangle_posDef (hδ.trans hL) x hx).smul hr
  have heq : (fun i j : Fin n => (K (x i - x j) : ℂ)) =
      r • (fun i j : Fin n => ((max (L - |x i - x j|) 0 : ℝ) : ℂ)) +
        (fun i j : Fin n =>
          ((∫ s : ℝ in Ioc 0 δ, max (s - |x i - x j|) 0 * D2 s : ℝ) : ℂ)) := by
    ext i j
    rw [(hrep (x i - x j) (hdiam i j)).2]
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_add,
      Complex.ofReal_mul]
    ring
  rw [heq]
  exact hwide.add_posSemidef hmix

#print axioms exists_window_posDef

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
