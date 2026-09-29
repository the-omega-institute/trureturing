/- GID: D5/S3/Fourier/Asymptotics/CosineNormalizedRemainder
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/CosineNormalizedRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform finite cosine-sum error estimate uses the actual cosine-integral tail and its Euler constant normalization. -/

import D5.S3.Fourier.Asymptotics.CosineIntegralLattice
import D5.S3.Weil.ZetaPntBase.EulerMaclaurin
import D5.S3.Arith.GoldenResource.RobinRationalBasis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.NumberTheory.Harmonic.Bounds
import D5.S3.Weil.Mertens.Gamma
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Harmonic.GammaDeriv

open MeasureTheory Set Filter
open scoped Topology BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder

open D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)

theorem result : ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ N : ℕ, 1 ≤ N →
    |(∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) / (k : ℝ)) -
      (-Real.log θ + cosineIntegral ((N : ℝ) * θ))| ≤
      C * (1 / (N : ℝ) + θ * (1 + max 0 (Real.log ((N : ℝ) * θ)))) := by
  refine ⟨6, by norm_num, ?_⟩
  intro θ hθ hθone N hN
  have hmain :
      |(∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) / (k : ℝ)) -
        (Real.eulerMascheroniConstant + Real.log (N : ℝ) +
          ∫ t in (0 : ℝ)..((N : ℝ) * θ), (Real.cos t - 1) / t)| ≤
        6 * (1 / (N : ℝ) + θ * (1 + max 0 (Real.log ((N : ℝ) * θ)))) := by
    have hquad :
        |(∑ k ∈ Finset.Icc 1 N, (Real.cos (θ * (k : ℝ)) - 1) / (k : ℝ)) -
          ∫ t in (0 : ℝ)..(N : ℝ), (Real.cos (θ * t) - 1) / t| ≤
            5 * θ * (1 + max 0 (Real.log ((N : ℝ) * θ))) := by
      let g : ℝ → ℝ := fun t => (Real.cos (θ * t) - 1) / t
      let d : ℝ → ℝ := fun t => -θ * Real.sin (θ * t) / t -
        (Real.cos (θ * t) - 1) / t ^ 2
      have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hn0 : (0 : ℝ) < N := by linarith
      have hgcont : Continuous g := by
        have heq : g = fun t => -θ * Real.sin (θ * t / 2) * Real.sinc (θ * t / 2) := by
          funext t
          by_cases ht : t = 0
          · simp [g, ht]
          · rw [Real.sinc_of_ne_zero (by positivity : θ * t / 2 ≠ 0)]
            have hc := Real.cos_two_mul_eq_one_sub (θ * t / 2)
            rw [show 2 * (θ * t / 2) = θ * t by ring] at hc
            dsimp [g]
            rw [hc]
            field_simp
            ring
        rw [heq]
        fun_prop
      have hd (t : ℝ) (ht : 0 < t) : HasDerivAt g (d t) t := by
        have hh := (((Real.hasDerivAt_cos (θ * t)).comp t
          ((hasDerivAt_id t).const_mul θ)).sub_const 1).div (hasDerivAt_id t) ht.ne'
        apply hh.congr_deriv
        dsimp [d]
        field_simp
      have hdcont : ContinuousOn (deriv g) (Set.uIcc 1 (N : ℝ)) := by
        rw [Set.uIcc_of_le hn]
        have hdc : ContinuousOn d (Set.Icc 1 (N : ℝ)) := by
          intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          apply ContinuousAt.continuousWithinAt
          dsimp [d]
          fun_prop (disch := positivity)
        exact hdc.congr (fun t ht => (hd t (by linarith [ht.1])).deriv)
      have hgsmall (t : ℝ) : |g t| ≤ θ := by
        by_cases ht : t = 0
        · simp [g, ht, hθ.le]
        · have hc := Real.abs_cos_sub_cos_le (θ * t) 0
          simp only [Real.cos_zero, sub_zero, abs_mul, abs_of_pos hθ] at hc
          dsimp [g]
          rw [abs_div]
          exact (div_le_iff₀ (abs_pos.mpr ht)).mpr hc
      have hdmajor (t : ℝ) (ht : 0 < t) : |d t| ≤ 6 * θ ^ 2 / (1 + θ * t) := by
        have hz : 0 < θ * t := mul_pos hθ ht
        have hden : 0 < 1 + θ * t := by positivity
        have hab : |d t| ≤ θ * |Real.sin (θ * t)| / t +
            (1 - Real.cos (θ * t)) / t ^ 2 := by
          calc
            |d t| ≤ |-θ * Real.sin (θ * t) / t| +
                |(Real.cos (θ * t) - 1) / t ^ 2| := abs_sub _ _
            _ = _ := by
              rw [abs_div, abs_div, abs_mul, abs_neg, abs_of_pos hθ, abs_of_pos ht,
                abs_of_nonneg (sq_nonneg t), abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
              ring
        by_cases hz1 : θ * t ≤ 1
        · have hs : |Real.sin (θ * t)| ≤ θ * t := by
            simpa [abs_of_pos hz] using (Real.abs_sin_le_abs (x := θ * t))
          have hc : 1 - Real.cos (θ * t) ≤ (θ * t) ^ 2 / 2 := by
            linarith [Real.one_sub_sq_div_two_le_cos (x := θ * t)]
          have hbound : |d t| ≤ 3 * θ ^ 2 / 2 := by
            calc
              |d t| ≤ θ * (θ * t) / t + ((θ * t) ^ 2 / 2) / t ^ 2 :=
                hab.trans (add_le_add (div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hs hθ.le) ht.le)
                  (div_le_div_of_nonneg_right hc (sq_nonneg t)))
              _ = 3 * θ ^ 2 / 2 := by field_simp; ring
          apply hbound.trans
          rw [le_div_iff₀ hden]
          nlinarith [sq_nonneg θ, mul_le_mul_of_nonneg_left hz1 (sq_nonneg θ)]
        · have hz1' : 1 ≤ θ * t := le_of_not_ge hz1
          have hs := Real.abs_sin_le_one (θ * t)
          have hc : 1 - Real.cos (θ * t) ≤ 2 := by linarith [Real.neg_one_le_cos (θ * t)]
          have hbound : |d t| ≤ θ / t + 2 / t ^ 2 := by
            calc
              |d t| ≤ θ * 1 / t + 2 / t ^ 2 :=
                hab.trans (add_le_add (div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hs hθ.le) ht.le)
                  (div_le_div_of_nonneg_right hc (sq_nonneg t)))
              _ = _ := by ring
          apply hbound.trans
          apply (le_div_iff₀ hden).mpr
          field_simp
          nlinarith [sq_nonneg (θ * t - 1)]
      have hformula := sum_eq_integral_add_integral_deriv (f := g)
        (a := 1) (b := N) (by norm_num) hn
        (fun t ht => (hd t (by linarith [ht.1])).differentiableAt) hdcont
      have hbern : ∀ t : ℝ, 0 ≤ t → |B1 t| ≤ 1 / 2 := fun _ ht => abs_B1_le_half ht
      have hweightcont : ContinuousOn (fun t : ℝ => 3 * θ ^ 2 / (1 + θ * t))
          (Set.uIcc 1 (N : ℝ)) := by
        rw [Set.uIcc_of_le hn]
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        apply ContinuousAt.continuousWithinAt
        fun_prop (disch := positivity)
      have hderivint : |∫ t in (1 : ℝ)..(N : ℝ), deriv g t * B1 t| ≤
          ∫ t in (1 : ℝ)..(N : ℝ), 3 * θ ^ 2 / (1 + θ * t) := by
        rw [← Real.norm_eq_abs]
        apply intervalIntegral.norm_integral_le_of_norm_le hn
        · apply Filter.Eventually.of_forall
          intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          rw [(hd t ht0).deriv, Real.norm_eq_abs, abs_mul]
          calc
            |d t| * |B1 t| ≤ (6 * θ ^ 2 / (1 + θ * t)) * (1 / 2) :=
              mul_le_mul (hdmajor t ht0) (hbern t ht0.le) (abs_nonneg _)
                (by positivity)
            _ = 3 * θ ^ 2 / (1 + θ * t) := by ring
        · exact hweightcont.intervalIntegrable
      have hweight : (∫ t in (1 : ℝ)..(N : ℝ), 3 * θ ^ 2 / (1 + θ * t)) =
          3 * θ * (Real.log (1 + θ * N) - Real.log (1 + θ)) := by
        have hdlog (t : ℝ) (ht : t ∈ Set.uIcc 1 (N : ℝ)) :
            HasDerivAt (fun u : ℝ => 3 * θ * Real.log (1 + θ * u))
              (3 * θ ^ 2 / (1 + θ * t)) t := by
          rw [Set.uIcc_of_le hn] at ht
          have ht0 : 0 < t := by linarith [ht.1]
          have hp : 0 < 1 + θ * t := by positivity
          apply (((((hasDerivAt_id t).const_mul θ).const_add 1).log hp.ne').const_mul (3 * θ)).congr_deriv
          simp only [id_eq]
          ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hdlog hweightcont.intervalIntegrable]
        simp only [mul_one]
        ring
      have hlog (x : ℝ) (hx : 0 < x) : Real.log (1 + x) ≤ 1 + max 0 (Real.log x) := by
        by_cases hx1 : x ≤ 1
        · have hb := Real.log_le_sub_one_of_pos (show 0 < 1 + x by positivity)
          have hm := le_max_left 0 (Real.log x)
          linarith
        · have h1x : 1 ≤ x := le_of_not_ge hx1
          have hb := Real.log_le_log (show 0 < 1 + x by positivity) (show 1 + x ≤ 2 * x by linarith)
          rw [Real.log_mul (by norm_num) hx.ne'] at hb
          have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          have hm := le_max_right 0 (Real.log x)
          linarith
      have herror : |∫ t in (1 : ℝ)..(N : ℝ), deriv g t * B1 t| ≤
          3 * θ * (1 + max 0 (Real.log ((N : ℝ) * θ))) := by
        rw [hweight] at hderivint
        have hpos := Real.log_nonneg (show 1 ≤ 1 + θ by linarith)
        have hb := hlog (θ * N) (mul_pos hθ hn0)
        rw [mul_comm θ (N : ℝ)] at hb hderivint
        nlinarith
      have hfirst : |∫ t in (0 : ℝ)..1, g t| ≤ θ := by
        have hb := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := 1) (C := θ) (f := g)
          (fun t _ => by simpa [Real.norm_eq_abs] using hgsmall t)
        simpa [Real.norm_eq_abs] using hb
      have hsum : (∑ k ∈ Finset.Icc 1 N, g k) = g 1 + ∑ k ∈ Finset.Ioc 1 N, g k := by
        rw [Finset.Icc_eq_cons_Ioc hN, Finset.sum_cons, Nat.cast_one]
      have hB (k : ℕ) : B1 k = -(1 / 2 : ℝ) := by simp [B1]
      simp only [Nat.floor_one, Nat.floor_natCast, RCLike.ofReal_real_eq_id, id_eq] at hformula
      have hsplit : (∫ t in (0 : ℝ)..1, g t) + (∫ t in (1 : ℝ)..(N : ℝ), g t) =
          ∫ t in (0 : ℝ)..(N : ℝ), g t :=
        intervalIntegral.integral_add_adjacent_intervals
          (hgcont.intervalIntegrable 0 1) (hgcont.intervalIntegrable 1 (N : ℝ))
      have heq : (∑ k ∈ Finset.Icc 1 N, g k) - ∫ t in (0 : ℝ)..(N : ℝ), g t =
          g 1 / 2 + g N / 2 + (∫ t in (1 : ℝ)..(N : ℝ), deriv g t * B1 t) -
            ∫ t in (0 : ℝ)..1, g t := by
        rw [hsum, hformula, show B1 1 = -(1 / 2 : ℝ) by norm_num [B1], hB,
          ← hsplit]
        ring
      change |(∑ k ∈ Finset.Icc 1 N, g k) - ∫ t in (0 : ℝ)..(N : ℝ), g t| ≤ _
      rw [heq]
      have hg1 := hgsmall 1
      have hgN := hgsmall N
      have hm := le_max_left 0 (Real.log ((N : ℝ) * θ))
      calc
        _ ≤ |g 1 / 2 + g N / 2 + ∫ t in (1 : ℝ)..(N : ℝ), deriv g t * B1 t| +
            |∫ t in (0 : ℝ)..1, g t| := abs_sub _ _
        _ ≤ |g 1 / 2| + |g N / 2| + |∫ t in (1 : ℝ)..(N : ℝ), deriv g t * B1 t| +
            |∫ t in (0 : ℝ)..1, g t| := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ 5 * θ * (1 + max 0 (Real.log ((N : ℝ) * θ))) := by
          simp only [abs_div, abs_two]
          nlinarith
  
    have hn0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hscale : (∫ t in (0 : ℝ)..(N : ℝ), (Real.cos (θ * t) - 1) / t) =
        ∫ t in (0 : ℝ)..((N : ℝ) * θ), (Real.cos t - 1) / t := by
      have heq : (fun t : ℝ => (Real.cos (θ * t) - 1) / t) =
          fun t => θ * ((Real.cos (θ * t) - 1) / (θ * t)) := by
        funext t
        by_cases ht : t = 0
        · simp [ht]
        · field_simp
      rw [heq, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_mul_left (fun t : ℝ => (Real.cos t - 1) / t) hθ.ne']
      simp [smul_eq_mul, hθ.ne', mul_comm θ (N : ℝ)]
    rw [hscale] at hquad
    have hsum : (∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) / (k : ℝ)) =
        (harmonic N : ℝ) +
          ∑ k ∈ Finset.Icc 1 N, (Real.cos (θ * (k : ℝ)) - 1) / (k : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Rat.cast_inv, Rat.cast_natCast, mul_comm θ (k : ℝ)]
      ring
    have hhar := D5.S3.Arith.GoldenResource.RobinRationalBasis.eulerMascheroni_remainder_bounds N hN
    have hrem : |(harmonic N : ℝ) - Real.log (N : ℝ) - Real.eulerMascheroniConstant| ≤
        1 / (2 * (N : ℝ)) := by
      have hpos : 0 ≤ (harmonic N : ℝ) - Real.log (N : ℝ) - Real.eulerMascheroniConstant :=
        le_trans (by positivity) hhar.1.le
      rw [abs_of_nonneg hpos]
      exact hhar.2.le
    calc
      _ = |((∑ k ∈ Finset.Icc 1 N, (Real.cos (θ * (k : ℝ)) - 1) / (k : ℝ)) -
          ∫ t in (0 : ℝ)..((N : ℝ) * θ), (Real.cos t - 1) / t) +
            ((harmonic N : ℝ) - Real.log (N : ℝ) - Real.eulerMascheroniConstant)| := by
        rw [hsum]
        congr 1
        ring
      _ ≤ |(∑ k ∈ Finset.Icc 1 N, (Real.cos (θ * (k : ℝ)) - 1) / (k : ℝ)) -
          ∫ t in (0 : ℝ)..((N : ℝ) * θ), (Real.cos t - 1) / t| +
            |(harmonic N : ℝ) - Real.log (N : ℝ) - Real.eulerMascheroniConstant| := abs_add_le _ _
      _ ≤ 5 * θ * (1 + max 0 (Real.log ((N : ℝ) * θ))) + 1 / (2 * (N : ℝ)) :=
        add_le_add hquad hrem
      _ ≤ 6 * (1 / (N : ℝ) + θ * (1 + max 0 (Real.log ((N : ℝ) * θ)))) := by
        have hlog := le_max_left 0 (Real.log ((N : ℝ) * θ))
        have hinv : 0 < 1 / (N : ℝ) := by positivity
        have heq : 1 / (2 * (N : ℝ)) = (1 / (N : ℝ)) / 2 := by ring
        rw [heq]
        nlinarith

  let q : ℝ → ℝ := fun t => (Real.cos t - 1) / t
  have hqint (a b : ℝ) : IntervalIntegrable q volume a b := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' ?_ ?_
    · exact ((Real.measurable_cos.sub measurable_const).div measurable_id).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro t
      change ‖q t‖ ≤ 1
      rw [Real.norm_eq_abs]
      by_cases ht : t = 0
      · simp [q, ht]
      · have hb := Real.abs_cos_sub_cos_le t 0
        simp only [Real.cos_zero, sub_zero] at hb
        dsimp [q]
        rw [abs_div]
        exact (div_le_one (abs_pos.mpr ht)).mpr hb
  have htail (a : ℝ) (ha : 0 < a) :
      IntegrableOn (fun t : ℝ => Real.sin t / t ^ 2) (Ioi a) := by
    have hp := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha
    have hm := hp.mul_bdd (c := (1 : ℝ)) Real.continuous_sin.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one t))
    refine hm.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ha.trans ht
    rw [Real.rpow_neg ht0.le, Real.rpow_two]
    ring
  have hCi (x : ℝ) (hx : 0 < x) :
      cosineIntegral x = cosineIntegral 1 + Real.log x +
        (∫ t in (0 : ℝ)..x, q t) - ∫ t in (0 : ℝ)..1, q t := by
    have hpos (t : ℝ) (ht : t ∈ Set.uIcc 1 x) : 0 < t := by
      rw [Set.mem_uIcc] at ht
      rcases ht with ht | ht <;> linarith [ht.1]
    have hcoscont : ContinuousOn (fun t : ℝ => Real.cos t / t) (Set.uIcc 1 x) := by
      intro t ht
      have ht0 := hpos t ht
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity)
    have hsincont : ContinuousOn (fun t : ℝ => Real.sin t / t ^ 2) (Set.uIcc 1 x) := by
      intro t ht
      have ht0 := hpos t ht
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity)
    have hinvcont : ContinuousOn (fun t : ℝ => 1 / t) (Set.uIcc 1 x) := by
      intro t ht
      have ht0 := hpos t ht
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity)
    have hd (t : ℝ) (ht : t ∈ Set.uIcc 1 x) :
        HasDerivAt (fun u : ℝ => Real.sin u / u)
          (Real.cos t / t - Real.sin t / t ^ 2) t := by
      have ht0 := hpos t ht
      apply ((Real.hasDerivAt_sin t).div (hasDerivAt_id t) ht0.ne').congr_deriv
      simp only [id_eq]
      field_simp
    have hparts := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hcoscont.intervalIntegrable.sub hsincont.intervalIntegrable)
    rw [intervalIntegral.integral_sub hcoscont.intervalIntegrable hsincont.intervalIntegrable,
      div_one] at hparts
    have hlog : (∫ t in (1 : ℝ)..x, Real.cos t / t) =
        (∫ t in (1 : ℝ)..x, q t) + Real.log x := by
      calc
        _ = ∫ t in (1 : ℝ)..x, (q t + 1 / t) := by
          apply intervalIntegral.integral_congr
          intro t ht
          dsimp [q]
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add (hqint 1 x) hinvcont.intervalIntegrable,
            integral_one_div_of_pos zero_lt_one hx, div_one]
    have hsplit : (∫ t in (0 : ℝ)..1, q t) + (∫ t in (1 : ℝ)..x, q t) =
        ∫ t in (0 : ℝ)..x, q t :=
      intervalIntegral.integral_add_adjacent_intervals (hqint 0 1) (hqint 1 x)
    have ht := intervalIntegral.integral_Ioi_sub_Ioi' (htail 1 zero_lt_one) (htail x hx)
    dsimp [cosineIntegral]
    simp only [div_one]
    linarith
  have hnorm : cosineIntegral 1 = Real.eulerMascheroniConstant +
      ∫ t in (0 : ℝ)..1, q t := by
    let Q : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, q s
    have hdamped (a : ℝ) (ha : 0 < a) :
        (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * ((Real.cos t - 1) / t)) =
          Real.log a - Real.log (a ^ 2 + 1) / 2 := by
      let q : ℝ → ℝ := fun t => (Real.cos t - 1) / t
      let F : ℝ → ℝ := fun b => ∫ t in Ioi (0 : ℝ), Real.exp (-b * t) * q t
      have hq (t : ℝ) : |q t| ≤ 1 := by
        by_cases ht : t = 0
        · simp [q, ht]
        · have h := Real.abs_cos_sub_cos_le t 0
          simp only [Real.cos_zero, sub_zero] at h
          dsimp [q]
          rw [abs_div]
          exact (div_le_one (abs_pos.mpr ht)).mpr h
      have heint (b : ℝ) (hb : 0 < b) :
          IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Ioi 0) :=
        integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0
      have hFint (b : ℝ) (hb : 0 < b) :
          IntegrableOn (fun t : ℝ => Real.exp (-b * t) * q t) (Ioi 0) := by
        apply (heint b hb).mul_bdd (c := 1)
        · exact ((Real.measurable_cos.sub measurable_const).div measurable_id).aestronglyMeasurable
        · exact Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hq t
      have hFderiv (b : ℝ) (hb : 0 < b) :
          HasDerivAt F (1 / b - b / (b ^ 2 + 1)) b := by
        let G : ℝ → ℝ → ℝ := fun c t => Real.exp (-c * t) * q t
        let G' : ℝ → ℝ → ℝ := fun c t => Real.exp (-c * t) * (1 - Real.cos t)
        have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
          (μ := volume.restrict (Ioi (0 : ℝ))) (F := G) (F' := G')
          (bound := fun t => 2 * Real.exp (-(b / 2) * t))
          (Ioi_mem_nhds (show b / 2 < b by linarith))
          (Eventually.of_forall fun c => by dsimp [G, q]; fun_prop)
          (hFint b hb) (by dsimp [G']; fun_prop) ?_
          ((heint (b / 2) (by linarith)).const_mul 2) ?_
        · have he := integral_exp_mul_Ioi (a := -b) (neg_neg_of_pos hb) 0
          have hc := D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos
            (c := b) (t := 1) hb
          have hcos : IntegrableOn (fun t : ℝ => Real.exp (-b * t) * Real.cos t) (Ioi 0) := by
            refine (heint b hb).mul_bdd (c := 1) (by fun_prop) ?_
            exact Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one t
          have hv : (∫ t in Ioi (0 : ℝ), G' b t) = 1 / b - b / (b ^ 2 + 1) := by
            simp only [one_mul, one_pow] at hc
            simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at he
            simp only [G', mul_sub, mul_one]
            rw [integral_sub (heint b hb) hcos, he, hc]
          rw [hv] at hd
          exact hd.2
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          intro c hc
          have hp : 0 < Real.exp (-c * t) := Real.exp_pos _
          have hco : 0 ≤ 1 - Real.cos t := sub_nonneg.mpr (Real.cos_le_one t)
          change ‖Real.exp (-c * t) * (1 - Real.cos t)‖ ≤ _
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.le hco)]
          have hexp : Real.exp (-c * t) ≤ Real.exp (-(b / 2) * t) :=
            Real.exp_le_exp.mpr (by have hc0 : b / 2 < c := hc; have ht0 : 0 < t := ht; nlinarith)
          nlinarith [Real.neg_one_le_cos t, Real.exp_pos (-(b / 2) * t)]
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          intro c hc
          have ht0 : t ≠ 0 := ne_of_gt ht
          apply ((((hasDerivAt_id c).neg.mul_const t).exp).mul_const (q t)).congr_deriv
          dsimp [G', q]
          field_simp
          ring
      have hlogderiv (b : ℝ) (hb : 0 < b) :
          HasDerivAt (fun c : ℝ => Real.log c - Real.log (c ^ 2 + 1) / 2)
            (1 / b - b / (b ^ 2 + 1)) b := by
        have hd := (Real.hasDerivAt_log hb.ne').sub
          (((((hasDerivAt_id b).pow 2).add_const 1).log (show b ^ 2 + 1 ≠ 0 by positivity)).div_const 2)
        apply hd.congr_deriv
        simp only [id_eq, Pi.pow_apply]
        ring
      have hconstant (b : ℝ) (hb : 0 < b) :
          F b - (Real.log b - Real.log (b ^ 2 + 1) / 2) =
            F a - (Real.log a - Real.log (a ^ 2 + 1) / 2) := by
        apply isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
          (fun x hx => ((hFderiv x hx).sub (hlogderiv x hx)).differentiableAt.differentiableWithinAt)
          (fun x hx => by rw [((hFderiv x hx).sub (hlogderiv x hx)).deriv]; simp) hb ha
      have hFbound (b : ℝ) (hb : 0 < b) : |F b| ≤ 1 / b := by
        have hm := (norm_integral_le_integral_norm (fun t => Real.exp (-b * t) * q t)
          (μ := volume.restrict (Ioi (0 : ℝ)))).trans
          (integral_mono_ae (hFint b hb).norm (heint b hb) ?_)
        · have he := integral_exp_mul_Ioi (a := -b) (neg_neg_of_pos hb) 0
          simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at he
          rw [he] at hm
          simpa only [F, Real.norm_eq_abs] using hm
        · filter_upwards with t
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact mul_le_of_le_one_right (Real.exp_pos _).le (hq t)
      have hFlim : Tendsto F atTop (𝓝 0) := by
        have hi : Tendsto (fun b : ℝ => 1 / b) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
        apply squeeze_zero_norm' _ hi
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
        simpa [Real.norm_eq_abs] using hFbound b hb
      have hloglim : Tendsto (fun b : ℝ => Real.log b - Real.log (b ^ 2 + 1) / 2) atTop (𝓝 0) := by
        have hlim : Tendsto (fun b : ℝ => -Real.log (1 + (1 / b) ^ 2) / 2) atTop (𝓝 0) := by
          have hi : Tendsto (fun b : ℝ => 1 / b) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
          have h := ((tendsto_const_nhds.add (hi.pow 2)).log
            (by norm_num : (1 : ℝ) + 0 ^ 2 ≠ 0)).neg.div_const 2
          simpa using h
        apply hlim.congr'
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
        have he : b ^ 2 + 1 = b ^ 2 * (1 + (1 / b) ^ 2) := by field_simp
        rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
        ring
      have hlim := hFlim.sub hloglim
      simp only [sub_self] at hlim
      have hc : Tendsto (fun _ : ℝ => F a - (Real.log a - Real.log (a ^ 2 + 1) / 2))
          atTop (𝓝 0) := by
        apply hlim.congr'
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
        exact hconstant b hb
      have hz := tendsto_nhds_unique hc tendsto_const_nhds
      change F a = _
      linarith
    have hgamma (a : ℝ) (ha : 0 < a) :
        IntegrableOn (fun t : ℝ => Real.exp (-a * t) * Real.log t) (Ioi 0) ∧
        a * (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * Real.log t) =
          -Real.eulerMascheroniConstant - Real.log a := by
      have hbase : (∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t)) =
          -Real.eulerMascheroniConstant := by
        rw [integral_log_mul_exp_neg_eq_deriv_Gamma, Real.eulerMascheroniConstant_eq_neg_deriv]
        ring
      have hbaseint : IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioi 0) := by
        by_contra h
        rw [integral_undef h] at hbase
        have := Real.one_half_lt_eulerMascheroniConstant
        linarith
      have hscaled : IntegrableOn (fun t : ℝ => Real.log (a * t) * Real.exp (-(a * t))) (Ioi 0) := by
        apply (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => Real.log t * Real.exp (-t)) 0 ha).mpr
        simpa using hbaseint
      have hexp : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi 0) :=
        integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0
      have heq : (fun t : ℝ => Real.log (a * t) * Real.exp (-(a * t))) =ᵐ[volume.restrict (Ioi 0)]
          fun t => Real.exp (-a * t) * Real.log t + Real.log a * Real.exp (-a * t) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.log_mul ha.ne' (ne_of_gt ht)]
        ring
      have hi : IntegrableOn (fun t : ℝ => Real.exp (-a * t) * Real.log t) (Ioi 0) := by
        have hh := (hscaled.congr heq).sub (hexp.const_mul (Real.log a))
        apply hh.congr
        filter_upwards with t
        dsimp
        ring
      refine ⟨hi, ?_⟩
      have hc := integral_comp_mul_left_Ioi' (fun t : ℝ => Real.log t * Real.exp (-t)) 0 ha
      rw [integral_congr_ae heq, integral_add hi (hexp.const_mul (Real.log a)),
        integral_const_mul, mul_zero, hbase] at hc
      have he := integral_exp_mul_Ioi (a := -a) (by linarith : -a < 0) 0
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at he
      rw [he, smul_eq_mul] at hc
      have hcancel : a * (1 / a) = 1 := by field_simp
      have hc2 : a * (Real.log a * (1 / a)) = Real.log a := by field_simp
      rw [mul_add, hc2] at hc
      linarith
    have hprimitive (a : ℝ) (ha : 0 < a) :
        IntegrableOn (fun t : ℝ => Real.exp (-a * t) * (∫ s in (0 : ℝ)..t, (Real.cos s - 1) / s)) (Ioi 0) ∧
        a * (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * (∫ s in (0 : ℝ)..t, (Real.cos s - 1) / s)) =
          ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * ((Real.cos t - 1) / t) := by
      let q : ℝ → ℝ := fun t => (Real.cos t - 1) / t
      let Q : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, q s
      have hq (t : ℝ) : |q t| ≤ 1 := by
        by_cases ht : t = 0
        · simp [q, ht]
        · have h := Real.abs_cos_sub_cos_le t 0
          simp only [Real.cos_zero, sub_zero] at h
          dsimp [q]
          rw [abs_div]
          exact (div_le_one (abs_pos.mpr ht)).mpr h
      have hqm : Measurable q := (Real.measurable_cos.sub measurable_const).div measurable_id
      have hqint (b c : ℝ) : IntervalIntegrable q volume b c := by
        refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hqm.aestronglyMeasurable ?_
        exact Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hq t
      have hQc : Continuous Q := intervalIntegral.continuous_primitive hqint 0
      have hQbound (t : ℝ) : |Q t| ≤ |t| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := t) (C := 1) (f := q)
          (fun s _ => by simpa [Real.norm_eq_abs] using hq s)
        simpa [Real.norm_eq_abs, Q] using h
      have hQd (t : ℝ) (ht : 0 < t) : HasDerivAt Q (q t) t := by
        apply intervalIntegral.integral_hasDerivAt_right (hqint 0 t)
          hqm.aestronglyMeasurable.stronglyMeasurableAtFilter
        dsimp [q]
        fun_prop (disch := positivity)
      have heint : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi 0) :=
        integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0
      have htint : IntegrableOn (fun t : ℝ => t * Real.exp (-a * t)) (Ioi 0) := by
        simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
          (s := (1 : ℝ)) (p := (1 : ℝ)) (by norm_num) (by norm_num) ha
      have hQint : IntegrableOn (fun t : ℝ => Real.exp (-a * t) * Q t) (Ioi 0) := by
        refine htint.mono' (by fun_prop) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h : |Q t| ≤ t := (hQbound t).trans_eq (abs_of_pos ht)
        nlinarith [Real.exp_pos (-a * t)]
      have hqexp : IntegrableOn (fun t : ℝ => q t * Real.exp (-a * t)) (Ioi 0) := by
        apply (heint.mul_bdd hqm.aestronglyMeasurable
          (c := 1) (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hq t)).congr
        filter_upwards with t
        exact mul_comm _ _
      have hzero : Tendsto (fun t : ℝ => Q t * Real.exp (-a * t)) (𝓝[>] 0) (𝓝 0) := by
        have h := hQc.continuousAt.mul (show ContinuousAt (fun t : ℝ => Real.exp (-a * t)) 0 by fun_prop)
        change ContinuousAt (fun t => Q t * Real.exp (-a * t)) 0 at h
        simpa [Q] using h.tendsto.mono_left nhdsWithin_le_nhds
      have hinfty : Tendsto (fun t : ℝ => Q t * Real.exp (-a * t)) atTop (𝓝 0) := by
        have ht : Tendsto (fun t : ℝ => t * Real.exp (-a * t)) atTop (𝓝 0) := by
          simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) a ha
        apply squeeze_zero_norm' _ ht
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht0
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h : |Q t| ≤ t := (hQbound t).trans_eq (abs_of_pos ht0)
        exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      have hparts := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ))
        (u := Q) (u' := q) (v := fun t => Real.exp (-a * t))
        (v' := fun t => -a * Real.exp (-a * t))
        (fun t ht => hQd t ht)
        (fun t _ => by
          apply (((hasDerivAt_id t).const_mul (-a)).exp).congr_deriv
          dsimp
          ring)
        (by
          apply (hQint.const_mul (-a)).congr
          filter_upwards with t
          change -a * (Real.exp (-a * t) * Q t) = Q t * (-a * Real.exp (-a * t))
          ring)
        hqexp hzero hinfty
      refine ⟨hQint, ?_⟩
      have heq : (fun t : ℝ => Q t * (-a * Real.exp (-a * t))) =
          fun t => -a * (Real.exp (-a * t) * Q t) := by funext t; ring
      rw [heq, integral_const_mul] at hparts
      simp only [sub_self, zero_sub] at hparts
      change a * (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * Q t) = _
      have heq2 : (∫ t in Ioi (0 : ℝ), q t * Real.exp (-a * t)) =
          ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * q t := by congr 1; funext t; ring
      rw [heq2] at hparts
      linarith
    have hQc : Continuous Q := intervalIntegral.continuous_primitive hqint 0
    have hm : AEStronglyMeasurable cosineIntegral (volume.restrict (Ioi (0 : ℝ))) := by
      have hm0 : AEStronglyMeasurable
          (fun t : ℝ => cosineIntegral 1 + Real.log t + Q t - Q 1)
          (volume.restrict (Ioi (0 : ℝ))) := by
        exact (((measurable_const.add Real.measurable_log).add hQc.measurable).sub
          measurable_const).aestronglyMeasurable
      apply hm0.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hCi t ht).symm
    have hLaplace :
        (∀ a : ℝ, 0 < a → IntegrableOn (fun t => Real.exp (-a * t) * cosineIntegral t) (Ioi 0)) ∧
        Tendsto (fun a : ℝ => a * ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * cosineIntegral t)
          (𝓝[>] 0) (𝓝 0) := by
      obtain ⟨C, hC, hlat⟩ := D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result
      have hpoint (t : ℝ) (ht : 0 < t) : |cosineIntegral t| ≤ Real.sqrt C * t ^ (-(1 / 2 : ℝ)) := by
        have hs := (hlat t ht).1.le_tsum 0 (fun n _ => sq_nonneg (cosineIntegral (t * (n + 1))))
        simp only [Nat.cast_zero, zero_add, mul_one] at hs
        have hb : t * cosineIntegral t ^ 2 ≤ C :=
          (mul_le_mul_of_nonneg_left hs ht.le).trans (hlat t ht).2
        have hp : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
        have hsq := Real.sq_sqrt ht.le
        have hsqC := Real.sq_sqrt hC.le
        have hbound : |cosineIntegral t| ≤ Real.sqrt C / Real.sqrt t := by
          apply (le_div_iff₀ hp).mpr
          have hab := sq_abs (cosineIntegral t)
          have hn : 0 ≤ |cosineIntegral t| * Real.sqrt t := by positivity
          have he : (|cosineIntegral t| * Real.sqrt t) ^ 2 = t * cosineIntegral t ^ 2 := by
            rw [mul_pow, sq_abs, hsq]
            ring
          nlinarith [Real.sqrt_nonneg C]
        calc
          |cosineIntegral t| ≤ Real.sqrt C / Real.sqrt t := hbound
          _ = Real.sqrt C * t ^ (-(1 / 2 : ℝ)) := by
            rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
            rfl
      have hpowint (a : ℝ) (ha : 0 < a) :
          IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-a * t)) (Ioi 0) := by
        simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
          (s := -(1 / 2 : ℝ)) (p := (1 : ℝ)) (by norm_num) (by norm_num) ha
      have hmajor (a : ℝ) : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          ‖Real.exp (-a * t) * cosineIntegral t‖ ≤
            Real.sqrt C * (t ^ (-(1 / 2 : ℝ)) * Real.exp (-a * t)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h := mul_le_mul_of_nonneg_left (hpoint t ht) (Real.exp_pos (-a * t)).le
        nlinarith
      have hint (a : ℝ) (ha : 0 < a) :
          IntegrableOn (fun t => Real.exp (-a * t) * cosineIntegral t) (Ioi 0) := by
        exact ((hpowint a ha).const_mul (Real.sqrt C)).mono'
          ((by fun_prop : AEStronglyMeasurable (fun t : ℝ => Real.exp (-a * t))
            (volume.restrict (Ioi 0))).mul hm) (hmajor a)
      refine ⟨hint, ?_⟩
      have hb (a : ℝ) (ha : 0 < a) :
          |a * ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * cosineIntegral t| ≤
            Real.sqrt C * Real.sqrt a * Real.Gamma (1 / 2) := by
        have hi := (norm_integral_le_integral_norm
          (fun t => Real.exp (-a * t) * cosineIntegral t)
          (μ := volume.restrict (Ioi (0 : ℝ)))).trans
          (integral_mono_ae (hint a ha).norm ((hpowint a ha).const_mul (Real.sqrt C)) (hmajor a))
        rw [integral_const_mul] at hi
        have hv := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 / 2 : ℝ)) (r := a)
          (by norm_num) ha
        norm_num only at hv
        have hv' : (∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * Real.exp (-a * t)) =
            (1 / a) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2) := by
          convert hv using 1 <;> ring
        rw [hv'] at hi
        have hid : a * (1 / a) ^ (1 / 2 : ℝ) = Real.sqrt a := by
          rw [one_div, Real.inv_rpow ha.le, ← Real.sqrt_eq_rpow]
          have hp : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
          field_simp
          exact (Real.sq_sqrt ha.le).symm
        rw [abs_mul, abs_of_pos ha]
        rw [Real.norm_eq_abs] at hi
        calc
          a * |∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * cosineIntegral t| ≤
              a * (Real.sqrt C * ((1 / a) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2))) :=
            mul_le_mul_of_nonneg_left hi ha.le
          _ = Real.sqrt C * Real.sqrt a * Real.Gamma (1 / 2) := by
            calc
              _ = Real.sqrt C * (a * (1 / a) ^ (1 / 2 : ℝ)) * Real.Gamma (1 / 2) := by ring
              _ = _ := by rw [hid]
      have hlim : Tendsto (fun a : ℝ => Real.sqrt C * Real.sqrt a * Real.Gamma (1 / 2))
          (𝓝[>] 0) (𝓝 0) := by
        have h := ((Real.continuous_sqrt.tendsto 0).const_mul (Real.sqrt C)).mul_const (Real.Gamma (1 / 2))
        simpa using h.mono_left nhdsWithin_le_nhds
      apply squeeze_zero_norm' _ hlim
      filter_upwards [self_mem_nhdsWithin] with a ha
      simpa only [Real.norm_eq_abs] using hb a ha
    have hformula (a : ℝ) (ha : 0 < a) :
        a * (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * cosineIntegral t) =
          cosineIntegral 1 - Q 1 - Real.eulerMascheroniConstant - Real.log (a ^ 2 + 1) / 2 := by
      have hg := hgamma a ha
      have hp := hprimitive a ha
      have heint : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi 0) :=
        integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0
      have he := integral_exp_mul_Ioi (a := -a) (by linarith : -a < 0) 0
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at he
      have hrep : (fun t : ℝ => Real.exp (-a * t) * cosineIntegral t) =ᵐ[volume.restrict (Ioi 0)]
          fun t => ((cosineIntegral 1 - Q 1) * Real.exp (-a * t) +
            Real.exp (-a * t) * Real.log t) + Real.exp (-a * t) * Q t := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [hCi t ht]
        dsimp [Q]
        ring
      have hconst : IntegrableOn (fun t : ℝ => (cosineIntegral 1 - Q 1) * Real.exp (-a * t)) (Ioi 0) :=
        heint.const_mul _
      have hboth : IntegrableOn (fun t : ℝ => (cosineIntegral 1 - Q 1) * Real.exp (-a * t) +
          Real.exp (-a * t) * Real.log t) (Ioi 0) := hconst.add hg.1
      have hpint : IntegrableOn (fun t : ℝ => Real.exp (-a * t) * Q t) (Ioi 0) := hp.1
      have hpval : a * (∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * Q t) =
          ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * ((Real.cos t - 1) / t) := hp.2
      rw [integral_congr_ae hrep,
        integral_add hboth hpint,
        integral_add hconst hg.1,
        integral_const_mul, he]
      have hcancel : a * ((cosineIntegral 1 - Q 1) * (1 / a)) = cosineIntegral 1 - Q 1 := by
        field_simp
      rw [mul_add, mul_add, hcancel, hg.2, hpval, hdamped a ha]
      ring
    have hlim : Tendsto
        (fun a : ℝ => cosineIntegral 1 - Q 1 - Real.eulerMascheroniConstant - Real.log (a ^ 2 + 1) / 2)
        (𝓝[>] 0) (𝓝 (cosineIntegral 1 - Q 1 - Real.eulerMascheroniConstant)) := by
      have hl : Tendsto (fun a : ℝ => Real.log (a ^ 2 + 1) / 2) (𝓝[>] 0) (𝓝 0) := by
        have hh : ContinuousAt (fun a : ℝ => Real.log (a ^ 2 + 1) / 2) 0 := by
          fun_prop (disch := norm_num)
        simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
      simpa using tendsto_const_nhds.sub hl
    have hlim2 : Tendsto
        (fun a : ℝ => cosineIntegral 1 - Q 1 - Real.eulerMascheroniConstant - Real.log (a ^ 2 + 1) / 2)
        (𝓝[>] 0) (𝓝 0) := by
      apply hLaplace.2.congr'
      filter_upwards [self_mem_nhdsWithin] with a ha
      exact hformula a ha
    have hz := tendsto_nhds_unique hlim hlim2
    change cosineIntegral 1 = Real.eulerMascheroniConstant + Q 1
    linarith
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  rw [hCi ((N : ℝ) * θ) (mul_pos hn0 hθ), hnorm, Real.log_mul hn0.ne' hθ.ne']
  rw [Real.log_mul hn0.ne' hθ.ne'] at hmain
  convert hmain using 1
  congr 1
  dsimp [q]
  ring

#print axioms result
end D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder
