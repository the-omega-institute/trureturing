/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/RHMobiusLinear
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/LinearOrder/RHMobiusLinear
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A linear in order remainder for the prime-only Möbius window under RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.OmittedSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.TrivialResponse
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHMobiusSingleLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

open Chebyshev Real ArithmeticFunction MeasureTheory Set
open scoped ArithmeticFunction.Moebius
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

private theorem centered_sum_linear (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m,
        -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| ≤
      K * (m : ℝ) * Real.exp (-(orderRate m) * u) := by
  obtain ⟨D, hD, htriv⟩ := trivial_response_signed_bound hRH
  obtain ⟨K, hK, hroot⟩ := omitted_root_density_linear hRH
  let H : ℝ := 144 * ((Real.log 4+5)*5000)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨D+K+H, by positivity, fun m hm u hu => ?_⟩
  let W := Real.exp (-(orderRate m)*u)
  let S := Finset.Icc 2 m
  let T := S.filter (fun n => m+1 ≤ 2*n)
  let f (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u)-rootDensity (n : ℝ) u)
  let g (n : ℕ) := -(μ n : ℝ) * rootDensity (n : ℝ) u
  let h (n : ℕ) := -(μ n : ℝ) * centered (n : ℝ) (Real.exp u)
  have hW : 0 ≤ W := Real.exp_nonneg _
  have hμ (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
  have hExp : Real.exp (-u/2) ≤ W := by
    apply Real.exp_le_exp.mpr
    unfold orderRate
    have hpos : 0 ≤ (m+1 : ℝ)⁻¹ := by positivity
    nlinarith only [mul_nonneg hu hpos]
  have hTriv (j : ℕ) (hj : j ≤ m) : |∑ n ∈ Finset.Icc 2 j, f n| ≤ D*(m : ℝ)*W := by
    apply (htriv j u hu).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hD.le)
      hExp (Real.exp_nonneg _) (by positivity)
  have hS : ∀ n ∈ S, (2 : ℝ) ≤ n := by
    intro n hn
    exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hLarge : (m : ℝ)+1 ≤ u → |∑ n ∈ T, g n| ≤ K*(m : ℝ)*W := by
    intro hx
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply le_trans _ (hroot m hm u hx)
    apply Finset.sum_le_sum
    intro n hn
    unfold g
    rw [abs_mul, abs_neg]
    exact mul_le_of_le_one_left (abs_nonneg _) (hμ n)
  have hSmall : u ≤ (m : ℝ)+1 → |∑ n ∈ T, h n| ≤ H*(m : ℝ)*W := by
    intro hx
    have hpoint : ∀ n ∈ T, |h n| ≤ H*W := by
      intro n hn
      obtain ⟨hnS, hnT⟩ := Finset.mem_filter.mp hn
      have hn2 := hS n hnS
      have hn0 : 0 < (n : ℝ) := by linarith
      have hnT' : (m : ℝ)+1 ≤ 2*(n : ℝ) := by exact_mod_cast hnT
      have ht : u/(n : ℝ) ≤ 2 := (div_le_iff₀ hn0).mpr (hx.trans hnT')
      have hnn := div_nonneg hu hn0.le
      have hpow : (1+u/(n : ℝ))^2 ≤ 9 :=
        (pow_le_pow_left₀ (by linarith) (show 1+u/(n : ℝ) ≤ 3 by linarith) 2).trans_eq (by norm_num)
      have hrate : Real.exp (((2*(n : ℝ))⁻¹-1/2)*u) ≤ W := by
        apply Real.exp_le_exp.mpr
        unfold orderRate
        have hr := inv_anti₀ (show 0 < (m+1 : ℝ) by positivity) hnT'
        nlinarith only [mul_nonneg hu (sub_nonneg.mpr hr)]
      have hh := centered_chebyshev_log hRH hn2 hu
      unfold h
      rw [abs_mul, abs_neg]
      apply (mul_le_of_le_one_left (abs_nonneg _) (hμ n)).trans
      apply hh.trans
      have hcoef : 0 ≤ 16 * ((Real.log 4 + 5) * 5000) := by positivity
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hpow hcoef) hrate
        (Real.exp_nonneg _) (by positivity)).trans_eq (by dsimp [H]; ring)
    have hc : (T.card : ℝ) ≤ m := by
      exact_mod_cast (show T.card ≤ m from
        (Finset.card_filter_le _ _).trans (by dsimp [S]; rw [Nat.card_Icc]; omega))
    calc
      _ ≤ ∑ n ∈ T, |h n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ T, H*W := Finset.sum_le_sum hpoint
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact (mul_le_mul_of_nonneg_right hc (mul_nonneg hH.le hW)).trans_eq (by ring)
  by_cases hu' : (m : ℝ)+1 ≤ u
  · have he : (∑ n ∈ S, -(μ n : ℝ) *
          (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)) =
        (∑ n ∈ S, f n) + ∑ n ∈ T, g n := by
      rw [show T = S.filter (fun n => m+1 ≤ 2*n) from rfl,
        Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      unfold capturedSpectrum f g
      by_cases hcut : 2*n < m+1
      · simp [hcut, not_le_of_gt hcut]
      · rw [ite_eq_right hcut, ite_eq_left (le_of_not_gt hcut)]
        ring
    rw [he]
    exact ((abs_add_le _ _).trans (add_le_add (hTriv m le_rfl) (hLarge hu'))).trans (by
      nlinarith only [mul_nonneg (mul_nonneg hH.le (Nat.cast_nonneg m)) hW])
  · have hpart : S.filter (fun n => 2*n < m+1) = Finset.Icc 2 (m/2) := by
      ext n
      simp only [S, Finset.mem_filter, Finset.mem_Icc]
      omega
    have he : (∑ n ∈ S, -(μ n : ℝ) *
          (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)) =
        (∑ n ∈ Finset.Icc 2 (m/2), f n) + ∑ n ∈ T, h n := by
      rw [← hpart, show T = S.filter (fun n => m+1 ≤ 2*n) from rfl,
        Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      unfold capturedSpectrum f h
      by_cases hcut : 2*n < m+1
      · simp [hcut, not_le_of_gt hcut]
      · have hle := le_of_not_gt hcut
        simp [hcut, hle]
    rw [he]
    exact ((abs_add_le _ _).trans (add_le_add (hTriv (m/2) (by omega))
      (hSmall (le_of_not_ge hu')))).trans (by
        nlinarith only [mul_nonneg (mul_nonneg hK.le (Nat.cast_nonneg m)) hW])

private theorem all_orders_density_linear (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * (m : ℝ) * Real.exp (-(orderRate m) * u) := by
  obtain ⟨L, hL, hsum'⟩ := centered_sum_linear hRH
  let A := (Real.log 4 + 4) * 4 * (1 + 2 / Real.log 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 ≤ C := abs_nonneg _
  refine ⟨A + L + C, by linarith, fun m hm u hu => ?_⟩
  let x := Real.exp u
  let W := Real.exp (-(orderRate m) * u)
  let T (n : ℕ) := Real.sqrt x * (∫ t in Ioi x, psi (t ^ (n : ℝ)⁻¹) / t ^ 2)
  let e (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) x - capturedSpectrum m n u)
  let R := Real.sqrt x * (primeTail x - Q x) - ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n
  let E := RHSharpActualEnvelope.G u - Real.exp (-u / 2) * (actualH u).re
  have hx : 2 ≤ x := by
    have hexp : Real.exp (Real.log 2) ≤ Real.exp u := Real.exp_le_exp.mpr hu
    simpa only [x, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hexp
  have hx0 : 0 < x := by linarith
  have hu0 : 0 ≤ u := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hu
  have hW : 0 < W := Real.exp_pos _
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hR : |R| ≤ A * (m : ℝ) * W := integrated_mobius_linear hm hx
  have hE : |E| ≤ C * W := by
    refine (RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le hu0).le.trans ?_
    dsimp only [W]
    rw [mul_comm (Real.exp _)]
    apply mul_le_mul (le_abs_self _) _ (Real.exp_nonneg _) hC
    apply Real.exp_le_exp.mpr
    unfold orderRate
    nlinarith [mul_nonneg (show 0 ≤ (m + 1 : ℝ)⁻¹ by positivity) hu0]
  have hsum : |∑ n ∈ Finset.Icc 2 m, e n| ≤ L * (m : ℝ) * W :=
    hsum' m hm u hu0
  have hterms (n : ℕ) (hn : n ∈ Finset.Icc 2 m) :
      (μ n : ℝ) * T n + retainedDensity m n u + e n = 0 := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have ht := root_tail_main (r := (n : ℝ)) hn1 hx0
    change T n = (n : ℝ) / ((n : ℝ) - 1) * x ^ ((n : ℝ)⁻¹ - 1 / 2) + centered (n : ℝ) x at ht
    have hpow : x ^ ((n : ℝ)⁻¹ - 1 / 2) = Real.exp (-(arithmeticRate n) * u) := by
      dsimp only [x, arithmeticRate]
      rw [← Real.exp_mul]
      congr 1
      ring
    rw [ht, hpow]
    unfold retainedDensity e
    ring
  have hs : (∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n) +
      (∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) +
      (∑ n ∈ Finset.Icc 2 m, e n) = 0 := by
    simp_rw [← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl hterms).trans Finset.sum_const_zero
  have hsplit : rootWindowDensity u - ∑ n ∈ Finset.Icc 2 m, retainedDensity m n u =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E - 2 := by
    dsimp only [R, E, rootWindowDensity, x]
    linear_combination -hs
  rw [show rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2) =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E by linarith only [hsplit]]
  have hm₁ : (1 : ℝ) ≤ m := by linarith
  calc
    _ ≤ |R| + |∑ n ∈ Finset.Icc 2 m, e n| + |E| := by
      calc
        _ ≤ |-R + ∑ n ∈ Finset.Icc 2 m, e n| + |E| := abs_add_le _ _
        _ ≤ (|-R| + |∑ n ∈ Finset.Icc 2 m, e n|) + |E| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_neg]
    _ ≤ A * (m : ℝ) * W + L * (m : ℝ) * W + C * (m : ℝ) * W :=
      add_le_add (add_le_add hR hsum)
        (hE.trans (mul_le_mul_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_left hm₁ hC) hW.le))
    _ = _ := by ring

open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean
  (windowError normalizedMass normalizedZeroSeries)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (prime_window_remainder_of_rh spectralPrimitive windowDiscrepancy)

/-- Under RH, one pair of constants bounds the prime-window residual at every truncation degree. -/
theorem prime_window_mobius_linear_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * (m : ℝ) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (late_strict_prime_tail hRH)
  obtain ⟨K, hK, hD⟩ := all_orders_density_linear hRH
  refine ⟨max T 2, 6 * K, le_max_right _ _, by positivity, ?_⟩
  intro m hm a B ha hab
  have h_arithmetic (n : ℕ) : -(arithmeticRate n) = (n : ℝ)⁻¹ - 1 / 2 := by
    unfold arithmeticRate
    ring
  have h_order : -(orderRate m) = (m + 1 : ℝ)⁻¹ - 1 / 2 := by
    unfold orderRate
    ring
  simp_rw [← h_order, ← h_arithmetic]
  change |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
      spectralPrimitive (phaseOrbit (Real.log a)) -
      (∑ n ∈ Finset.Icc 3 m, arithmeticPrimitive n a B) -
      (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
        -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
      6 * K * (m : ℝ) * powerGap (orderRate m) a B
  have ha₂ := (le_max_right T (2 : ℝ)).trans ha
  have ha₀ : 0 < a := by linarith
  have hB₀ := ha₀.trans_le hab
  have hlog := Real.log_le_log ha₀ hab
  have hlog₂ := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ha₂
  have hr : 1 / 6 ≤ orderRate m := by
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have h := inv_anti₀ (show (0 : ℝ) < 3 by norm_num)
      (show (3 : ℝ) ≤ (m + 1 : ℝ) by linarith)
    unfold orderRate
    norm_num at h
    linarith
  have hr₀ : 0 < orderRate m := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hr
  have Hwin : (∫ u in Real.log a..Real.log B, windowError u) =
      ∫ u in Real.log a..Real.log B, rootWindowDensity u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hlog] at hu
    have hx : a ≤ Real.exp u := by simpa only [Real.exp_log ha₀] using Real.exp_le_exp.mpr hu.1
    have hpos := hT _ ((le_max_left T 2).trans (ha.trans hx))
    have hscaled := complete_scaled (x := Real.exp u) (ha₂.trans hx)
    rw [Real.log_exp] at hscaled
    rw [windowError, normalizedMass, normalizedZeroSeries, max_eq_left hpos.le,
      rootWindowDensity, Complex.re_ofReal_mul, hscaled]
    ring
  let f (u : ℝ) := ∑ n ∈ Finset.Icc 2 m, retainedDensity m n u
  let e (u : ℝ) := rootWindowDensity u - (f u - 2)
  let w (u : ℝ) := K * (m : ℝ) * Real.exp (-(orderRate m) * u)
  have hi : IntervalIntegrable rootWindowDensity volume (Real.log a) (Real.log B) :=
    (rootWindowDensity_continuousOn.mono (by
      rw [uIcc_of_le hlog]
      exact fun _ hu => hlog₂.trans hu.1)).intervalIntegrable
  have hfi : IntervalIntegrable f volume (Real.log a) (Real.log B) := by
    have hf : f = ∑ n ∈ Finset.Icc 2 m, retainedDensity m n := by
      funext u
      simp [f, Finset.sum_apply]
    rw [hf]
    exact IntervalIntegrable.sum (f := retainedDensity m) (Finset.Icc 2 m) (fun n hn =>
      (retainedDensity_integral (Finset.mem_Icc.mp hn).1 ha₀ hB₀).1)
  have hc : IntervalIntegrable (fun _ : ℝ => (2 : ℝ)) volume (Real.log a) (Real.log B) :=
    intervalIntegrable_const
  have hei : IntervalIntegrable e volume (Real.log a) (Real.log B) := hi.sub (hfi.sub hc)
  have hwi : IntervalIntegrable w volume (Real.log a) (Real.log B) :=
    (by unfold w; fun_prop : Continuous w).intervalIntegrable _ _
  have hmono : |∫ u in Real.log a..Real.log B, e u| ≤ ∫ u in Real.log a..Real.log B, w u :=
    (intervalIntegral.abs_integral_le_integral_abs hlog).trans
      (intervalIntegral.integral_mono_on hlog hei.abs hwi
        (fun u hu => hD m hm u (hlog₂.trans hu.1)))
  have Hf : (∫ u in Real.log a..Real.log B, f u) =
      2 * (Real.log B - Real.log a) +
        (∑ n ∈ Finset.Icc 3 m, arithmeticPrimitive n a B) +
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a)) := by
    unfold f
    rw [intervalIntegral.integral_finsetSum fun n hn =>
      (retainedDensity_integral (Finset.mem_Icc.mp hn).1 ha₀ hB₀).1]
    calc
      _ = ∑ n ∈ Finset.Icc 2 m,
          ((if n = 2 then 2 * (Real.log B - Real.log a) else arithmeticPrimitive n a B) +
            capturedPrimitive m n a B) :=
        Finset.sum_congr rfl fun _ hn =>
          (retainedDensity_integral (Finset.mem_Icc.mp hn).1 ha₀ hB₀).2
      _ = _ := by
        rw [Finset.sum_add_distrib]
        have hs : Finset.Icc 2 m = insert 2 (Finset.Icc 3 m) := by
          ext n
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hmain :
            (∑ n ∈ Finset.Icc 2 m,
              if n = 2 then 2 * (Real.log B - Real.log a) else arithmeticPrimitive n a B) =
              2 * (Real.log B - Real.log a) + ∑ n ∈ Finset.Icc 3 m, arithmeticPrimitive n a B := by
          rw [hs, Finset.sum_insert (by simp)]
          congr 1
          refine Finset.sum_congr rfl fun n hn => ite_eq_right ?_
          have hn3 := (Finset.mem_Icc.mp hn).1
          omega
        rw [hmain, Finset.sum_filter]
        rfl
  have hw : (∫ u in Real.log a..Real.log B, w u) =
      K * (m : ℝ) * (powerGap (orderRate m) a B / orderRate m) := by
    unfold w
    rw [intervalIntegral.integral_const_mul, exp_decay_integral hr₀]
    have hrpow {x : ℝ} (hx : 0 < x) (r : ℝ) : Real.exp (-r * Real.log x) = x ^ (-r) := by
      rw [Real.rpow_def_of_pos hx, mul_comm]
    rw [hrpow ha₀, hrpow hB₀]
    rfl
  have hgap : 0 ≤ powerGap (orderRate m) a B :=
    sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos ha₀ hab (neg_nonpos.mpr hr₀.le))
  have hdiv : powerGap (orderRate m) a B / orderRate m ≤ 6 * powerGap (orderRate m) a B := by
    apply (div_le_iff₀ hr₀).mpr
    nlinarith only [mul_nonneg hgap (show 0 ≤ 6 * orderRate m - 1 by linarith)]
  rw [(prime_window_remainder_of_rh hRH).2.2 a B ha₂ hab, Hwin]
  have hle : (∫ u in Real.log a..Real.log B, w u) ≤
      6 * K * (m : ℝ) * powerGap (orderRate m) a B := by
    rw [hw]
    exact (mul_le_mul_of_nonneg_left hdiv (by positivity)).trans_eq (by ring)
  refine (?_ : _ ≤ ∫ u in Real.log a..Real.log B, w u).trans hle
  dsimp only [e] at hmono
  rw [intervalIntegral.integral_sub hi (hfi.sub hc), intervalIntegral.integral_sub hfi hc, Hf,
    intervalIntegral.integral_const, smul_eq_mul] at hmono
  convert hmono using 1
  congr 1
  ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
