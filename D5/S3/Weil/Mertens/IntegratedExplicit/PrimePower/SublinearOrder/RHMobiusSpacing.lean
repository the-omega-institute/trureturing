/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSpacing
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSpacing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual sample separation yields inverse double-logarithmic saving in the RH prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusRate
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.RHMobiusLinear
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.TrivialResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Real ArithmeticFunction Finset Chebyshev MeasureTheory
open Set (Ioi)
open scoped ArithmeticFunction.Moebius
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder (spectralPrimitive windowDiscrepancy)

private def spacingScale (m : ℕ) : ℝ :=
  1 + Real.log (Real.log ((m : ℝ)+1))

private theorem spacingScale_pos {m : ℕ} (hm : 2 ≤ m) : 0 < spacingScale m := by
  have hthree : (3 : ℝ) ≤ (m : ℝ)+1 := by exact_mod_cast (show 3 ≤ m + 1 by omega)
  have hlog : (1/2 : ℝ) ≤ Real.log ((m : ℝ)+1) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < (m : ℝ)+1 by positivity)
    have hinv := inv_anti₀ (show (0 : ℝ) < 3 by norm_num) hthree
    norm_num at hinv
    linarith
  have hsmall : Real.exp (-1) < (1/2 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) (by linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)])
  have h := Real.log_lt_log (Real.exp_pos (-1)) (hsmall.trans_le hlog)
  rw [Real.log_exp] at h
  dsimp [spacingScale]
  linarith

private theorem spacingScale_mono {m k : ℕ} (hm : 2 ≤ m) (hmk : m ≤ k) :
    spacingScale m ≤ spacingScale k := by
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmK : (m : ℝ) ≤ k := by exact_mod_cast hmk
  unfold spacingScale
  refine add_le_add le_rfl (Real.log_le_log (Real.log_pos ?_) (Real.log_le_log ?_ ?_))
  · linarith
  · linarith
  · linarith

private theorem spacing_cutoff_bounds :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M,
      let L := spacingScale m / 8
      2 ≤ Real.log (m : ℝ) ∧ 1 ≤ L ∧
        spacingScale m ≤ 7*(Real.log (m : ℝ))^(1/5 : ℝ) ∧
        spacingScale m * (Real.exp (2*L) / Real.log (m : ℝ)) ≤ 28 := by
  obtain ⟨X, hX, hcut⟩ := logarithmic_order_cutoff_bounds
  obtain ⟨M, hM⟩ := exists_nat_ge X
  refine ⟨max 2 M, le_max_left _ _, fun m hm => ?_⟩
  have hMle : M ≤ m := (le_max_right 2 M).trans hm
  have hx : X ≤ (m : ℝ) := hM.trans (by exact_mod_cast hMle)
  obtain ⟨ht, hL, _, _, _⟩ := hcut (m : ℝ) hx
  let t := Real.log (m : ℝ)
  let ell := spacingScale m
  let L := ell / 8
  have ht1 : 1 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hm3 : (3 : ℝ) ≤ m := hX.trans hx
  have hm0 : (0 : ℝ) < m := by linarith
  have hlogplus0 : 0 < Real.log ((m : ℝ)+1) := Real.log_pos (by linarith)
  have hlogplus : Real.log ((m : ℝ)+1) ≤ 2*t := by
    have h := Real.log_le_log (by positivity : 0 < (m : ℝ)+1)
      (show (m : ℝ)+1 ≤ (m : ℝ)^2 by nlinarith)
    rwa [pow_two, Real.log_mul hm0.ne' hm0.ne', ← two_mul] at h
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hll := Real.log_le_log hlogplus0 hlogplus
  rw [Real.log_mul (by norm_num) ht0.ne'] at hll
  have hpow := Real.one_le_rpow ht1 (by norm_num : (0 : ℝ) ≤ 1/5)
  have hlogt := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1/5)
  have hell : ell ≤ 7 * t^(1/5 : ℝ) := by
    dsimp [ell, spacingScale]
    linarith
  have hexact : Real.exp (2*L) =
      Real.exp (1/4) * (Real.log ((m : ℝ)+1))^(1/4 : ℝ) := by
    rw [show 2*L = 1/4 + Real.log (Real.log ((m : ℝ)+1))*(1/4) by
      dsimp [L, ell, spacingScale]; ring, Real.exp_add, Real.rpow_def_of_pos hlogplus0]
  have hexp4 : Real.exp (1/4) ≤ 2 := by
    have h : (1/4 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      linarith
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr h
  have hb : (Real.log ((m : ℝ)+1))^(1/4 : ℝ) ≤ 2 * t^(1/4 : ℝ) := by
    refine (Real.rpow_le_rpow hlogplus0.le hlogplus (by norm_num)).trans ?_
    rw [Real.mul_rpow (by norm_num) ht0.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht0.le _)
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1/4 : ℝ) ≤ 1)
  have he : Real.exp (2*L) ≤ 4*t^(1/4 : ℝ) := by
    rw [hexact]
    exact (mul_le_mul hexp4 hb (by positivity) (by norm_num)).trans_eq (by ring)
  have hp : t^(1/5 : ℝ) * t^(1/4 : ℝ) ≤ t := by
    rw [← Real.rpow_add ht0]
    simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (1/5 : ℝ) + 1/4 ≤ 1)
  refine ⟨ht, hL, hell, ?_⟩
  change ell * (Real.exp (2*L)/t) ≤ 28
  rw [← mul_div_assoc]
  apply (div_le_iff₀ ht0).2
  calc
    _ ≤ (7*t^(1/5 : ℝ)) * (4*t^(1/4 : ℝ)) :=
      mul_le_mul hell he (Real.exp_nonneg _) (by positivity)
    _ = 28 * (t^(1/5 : ℝ) * t^(1/4 : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)

private theorem spacing_far_budget {m : ℕ} (hm : 2 ≤ m) {u : ℝ}
    (hu : spacingScale m / 8 * ((m : ℝ)+1) ≤ u) :
    1 + ((m : ℝ)+1)^2/u + ((m : ℝ)+1)^(7/8 : ℝ) ≤
      39 * ((m : ℝ)/spacingScale m) := by
  let ell := spacingScale m
  let q := (m : ℝ)+1
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hell0 : 0 < ell := spacingScale_pos hm
  have hu0 : 0 < u := (mul_pos (show 0 < ell/8 by positivity) hq0).trans_le hu
  have hlog0 : 0 < Real.log q := Real.log_pos (by dsimp [q]; linarith)
  have hlog := Real.log_le_sub_one_of_pos hlog0
  have hp := Real.log_le_rpow_div hq0.le (by norm_num : (0 : ℝ) < 1/8)
  have hpow := Real.one_le_rpow hq (by norm_num : (0 : ℝ) ≤ 1/8)
  have hell : ell ≤ 9*q^(1/8 : ℝ) := by
    dsimp [ell, spacingScale]
    change 1 + Real.log (Real.log q) ≤ _
    linarith
  have hg : 0 ≤ q^(7/8 : ℝ) := by positivity
  have hf : ell * q^(7/8 : ℝ) ≤ 9*q := by
    refine (mul_le_mul_of_nonneg_right hell hg).trans_eq ?_
    rw [mul_assoc, ← Real.rpow_add hq0]
    norm_num
  have hbase : ell ≤ 9*q := by
    refine hell.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    simpa using Real.rpow_le_rpow_of_exponent_le hq (by norm_num : (1/8 : ℝ) ≤ 1)
  have hratio : q^2/u * ell ≤ 8*q := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hu0).2
    have h := mul_le_mul_of_nonneg_left hu (show 0 ≤ 8*q by positivity)
    nlinarith only [h]
  change 1 + q^2/u + q^(7/8 : ℝ) ≤ 39 * ((m : ℝ)/ell)
  rw [← mul_div_assoc, le_div_iff₀ hell0]
  have hqm : q ≤ (3/2)*(m : ℝ) := by dsimp [q]; linarith
  nlinarith only [hbase, hratio, hf, hqm]

private theorem centered_sum_spacing (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m,
        -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| ≤
        K * ((m : ℝ)/spacingScale m) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨F, hF, hfar⟩ := omitted_root_density_spacing hRH
  obtain ⟨D, hD, htriv⟩ := trivial_response_signed_log_power_saving hRH
  obtain ⟨C, hC, hnear⟩ := omitted_centered_near_moebius_exp_bound hRH
  obtain ⟨M, hM, hcut⟩ := spacing_cutoff_bounds
  let K := 7*D + max (39*F) (28*C)
  refine ⟨K, by dsimp [K]; positivity, M, hM, fun m hm u hu => ?_⟩
  let S := Finset.Icc 2 m
  let T := S.filter (fun n => m+1 ≤ 2*n)
  let p := max 2 ((m+2)/2)
  let L := spacingScale m / 8
  let W := Real.exp (-(orderRate m)*u)
  let Q := (m : ℝ)/spacingScale m
  let f (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)
  let g (n : ℕ) := -(μ n : ℝ) * rootDensity (n : ℝ) u
  let h (n : ℕ) := -(μ n : ℝ) * centered (n : ℝ) (Real.exp u)
  have hm₂ := hM.trans hm
  obtain ⟨ht, hL, hscale, hExp⟩ := hcut m hm
  have hW : 0 ≤ W := Real.exp_nonneg _
  have hQ : 0 ≤ Q := div_nonneg (Nat.cast_nonneg m) (spacingScale_pos hm₂).le
  have hEW : Real.exp (-u/2) ≤ W := exp_half_le_order m hu
  have ht0 : 0 < Real.log (m : ℝ) := by linarith
  have htp := Real.rpow_pos_of_pos ht0 (1/5)
  have htriv' (k : ℕ) (hkm : k ≤ m) : |∑ n ∈ Finset.Icc 2 k, f n| ≤ 7*D*Q*W := by
    have hbase : (m : ℝ)/(Real.log (m : ℝ))^(1/5 : ℝ) ≤ 7*Q := by
      dsimp [Q]
      rw [← mul_div_assoc, div_le_div_iff₀ htp (spacingScale_pos hm₂)]
      calc
        _ ≤ (m : ℝ)*(7*(Real.log (m : ℝ))^(1/5 : ℝ)) :=
          mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg m)
        _ = _ := by ring
    exact (htriv m hm₂ ht k hkm u hu).trans ((mul_le_mul
      (mul_le_mul_of_nonneg_left hbase hD.le) hEW (Real.exp_nonneg _) (by positivity)).trans_eq (by ring))
  change 1 ≤ L at hL
  change spacingScale m * (Real.exp (2*L) / Real.log (m : ℝ)) ≤ 28 at hExp
  by_cases huL : L*((m : ℝ)+1) ≤ u
  · have he : (∑ n ∈ S, -(μ n : ℝ) *
          (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)) =
          (∑ n ∈ S, f n) + ∑ n ∈ T, g n := by
      dsimp only [T]
      rw [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      unfold capturedSpectrum f g
      by_cases hcut : 2*n < m+1
      · simp [hcut, not_le_of_gt hcut]
      · rw [ite_eq_right hcut, ite_eq_left (le_of_not_gt hcut)]
        ring
    have hbase := spacing_far_budget hm₂ huL
    have hqu : (m : ℝ)+1 ≤ u := by
      exact (le_mul_of_one_le_left (by positivity) hL).trans huL
    have hz : |∑ n ∈ T, g n| ≤ 39*F*Q*W := by
      have hsumabs : |∑ n ∈ T, g n| ≤ ∑ n ∈ T, |rootDensity (n : ℝ) u| := by
        refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro n hn
        unfold g
        rw [abs_mul, abs_neg]
        exact mul_le_of_le_one_left (abs_nonneg _)
          (by exact_mod_cast abs_moebius_le_one (n := n))
      refine (hsumabs.trans (hfar m hm₂ u hqu)).trans ?_
      dsimp only [W, Q]
      calc
        _ ≤ Real.exp (-(orderRate m)*u) * (F * (39*((m : ℝ)/spacingScale m))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbase hF.le) (Real.exp_nonneg _)
        _ = _ := by ring
    rw [he]
    refine ((abs_add_le _ _).trans (add_le_add (htriv' m le_rfl) hz)).trans ?_
    have hFmax : (39*F : ℝ) ≤ max (39*F) (28*C) := le_max_left _ _
    dsimp [K]
    nlinarith only [mul_le_mul_of_nonneg_right hFmax (mul_nonneg hQ hW)]
  · have hpart : S.filter (fun n => 2*n < m+1) = Finset.Icc 2 (m/2) := by
      ext n
      simp only [S, Finset.mem_filter, Finset.mem_Icc]
      omega
    have hTp : T = Finset.Icc p m := by
      ext n
      simp only [T, S, p, Finset.mem_filter, Finset.mem_Icc, max_le_iff]
      omega
    have he : (∑ n ∈ S, -(μ n : ℝ) *
        (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)) =
        (∑ n ∈ Finset.Icc 2 (m/2), f n) + ∑ n ∈ T, h n := by
      rw [← hpart]
      dsimp only [T]
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      unfold capturedSpectrum f h
      by_cases hcut : 2*n < m+1
      · simp [hcut, not_le_of_gt hcut]
      · simp [hcut, le_of_not_gt hcut]
    have hp₂ : 2 ≤ p := le_max_left _ _
    have hpm : p ≤ m := by dsimp [p]; omega
    have hhalf : m+1 ≤ 2*p := by dsimp [p]; omega
    have hh := hnear L (by linarith) m p u hp₂ hpm hhalf hu (le_of_not_ge huL)
    have hh' : |∑ n ∈ T, h n| ≤
        C * Real.exp (2*L) * ((m : ℝ) / Real.log m) * Real.exp (-u/2) := by
      rw [hTp]
      simpa only [h, centered, neg_mul, Finset.sum_neg_distrib, abs_neg] using hh
    have hbase : (m : ℝ) * (Real.exp (2*L) / Real.log m) ≤ 28*Q := by
      dsimp only [Q]
      rw [show 28 * ((m : ℝ) / spacingScale m) = (28 * (m : ℝ)) / spacingScale m by ring,
        le_div_iff₀ (spacingScale_pos hm₂)]
      nlinarith only [mul_le_mul_of_nonneg_left hExp (Nat.cast_nonneg m)]
    have hz : |∑ n ∈ T, h n| ≤ 28*C*Q*W := by
      refine hh'.trans ?_
      rw [show C*Real.exp (2*L)*((m : ℝ)/Real.log m) =
        C*((m : ℝ)*(Real.exp (2*L)/Real.log m)) by ring]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hbase hC.le) hEW
        (Real.exp_nonneg _) (by positivity)).trans_eq (by ring)
    rw [he]
    refine ((abs_add_le _ _).trans (add_le_add (htriv' (m/2) (Nat.div_le_self _ _)) hz)).trans ?_
    have hCmax : (28*C : ℝ) ≤ max (39*F) (28*C) := le_max_right _ _
    dsimp [K]
    nlinarith only [mul_le_mul_of_nonneg_right hCmax (mul_nonneg hQ hW)]

private theorem density_spacing (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * ((m : ℝ)/spacingScale m) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨D, hD, M₁, hM₁, hsum'⟩ := centered_sum_spacing hRH
  obtain ⟨A, hA, htail⟩ := normalized_mobius_tail_one_log hRH
  obtain ⟨M₂, hM₂, hcut⟩ := spacing_cutoff_bounds
  let C := |Real.log (2*Real.pi)|
  refine ⟨7*A+D+7*C, by dsimp [C]; positivity, max M₁ M₂, hM₁.trans (le_max_left _ _),
    fun m hm u hu => ?_⟩
  have hm₁ := (le_max_left M₁ M₂).trans hm
  have hm₂ := hM₁.trans hm₁
  obtain ⟨ht, _, hs, _⟩ := hcut m ((le_max_right M₁ M₂).trans hm)
  let x := Real.exp u
  let W := Real.exp (-(orderRate m) * u)
  let T (n : ℕ) := Real.sqrt x * (∫ t in Ioi x, psi (t ^ (n : ℝ)⁻¹) / t ^ 2)
  let e (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) x - capturedSpectrum m n u)
  let R := Real.sqrt x * (primeTail x - Q x) - ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n
  let E := RHSharpActualEnvelope.G u - Real.exp (-u / 2) * (actualH u).re
  have hx : 2 ≤ x := by
    have hexp : Real.exp (Real.log 2) ≤ Real.exp u := Real.exp_le_exp.mpr hu
    simpa only [x, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hexp
  have hu0 : 0 ≤ u := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hu
  have hW : 0 ≤ W := Real.exp_nonneg _
  let q := (m : ℝ)/spacingScale m
  have hm0 : (0 : ℝ) < m := by positivity
  have ht0 : 0 < Real.log (m : ℝ) := by linarith
  have ht1 : 1 ≤ Real.log (m : ℝ) := by linarith
  have hs0 := spacingScale_pos hm₂
  have hlog : Real.log (m : ℝ) ≤ Real.log ((m : ℝ)+1) :=
    Real.log_le_log hm0 (by linarith)
  have hpow : (Real.log (m : ℝ))^(1/5 : ℝ) ≤ Real.log (m : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (1/5 : ℝ) ≤ 1)
    simpa only [Real.rpow_one] using h
  have hslog : spacingScale m ≤ 7*Real.log (m : ℝ) :=
    hs.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have hbase : (m : ℝ)/Real.log ((m : ℝ)+1) ≤ 7*q := by
    dsimp only [q]
    rw [← mul_div_assoc, div_le_div_iff₀ (ht0.trans_le hlog) hs0]
    have h := mul_le_mul_of_nonneg_left (hslog.trans
      (mul_le_mul_of_nonneg_left hlog (by norm_num))) hm0.le
    nlinarith only [h]
  have hR : |R| ≤ 7*A*q*W := by
    exact (htail m hm₂ u hx).trans
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hA.le) hW).trans_eq (by ring))
  have hQ : 1 ≤ 7*q := by
    dsimp only [q]
    rw [← mul_div_assoc, one_le_div hs0]
    refine hslog.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    linarith [Real.log_le_sub_one_of_pos hm0]
  have hE : |E| ≤ 7*C*q*W := by
    have hbound := (RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le hu0).le
    refine hbound.trans ?_
    rw [mul_comm (Real.exp _)]
    have hcoef : Real.log (2*Real.pi) ≤ 7*C*q := by
      calc
        _ ≤ C := le_abs_self _
        _ = C * 1 := (mul_one _).symm
        _ ≤ C * (7*q) := mul_le_mul_of_nonneg_left hQ (abs_nonneg _)
        _ = _ := by ring
    exact mul_le_mul hcoef (exp_half_le_order m hu0) (Real.exp_nonneg _) (by dsimp [C, q]; positivity)
  have hsum : |∑ n ∈ Finset.Icc 2 m, e n| ≤ D*q*W := hsum' m hm₁ u hu0
  rw [show rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2) =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E from mobius_window_density_split m u]
  calc
    _ ≤ |R| + |∑ n ∈ Finset.Icc 2 m, e n| + |E| := by
      simpa only [abs_neg] using (abs_add_le (-R + ∑ n ∈ Finset.Icc 2 m, e n) E).trans
        (add_le_add (abs_add_le (-R) (∑ n ∈ Finset.Icc 2 m, e n)) (le_refl |E|))
    _ ≤ 7*A*q*W + D*q*W + 7*C*q*W := add_le_add (add_le_add hR hsum) hE
    _ = _ := by dsimp [q, W]; ring

/-- A uniform inverse double-logarithmic rate for the signed Möbius prime-tail interval. -/
theorem prime_window_mobius_spacing_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧
      ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * ((m : ℝ) / (1 + Real.log (Real.log ((m : ℝ)+1)))) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨a₁, ha₁, hwindow⟩ := prime_window_threshold_of_rh hRH
  obtain ⟨a₂, B₀, ha₂, hB₀, hlinear⟩ := prime_window_mobius_linear_of_rh hRH
  obtain ⟨D, hD, M, hM, hDens⟩ := density_spacing hRH
  let K := max (6*D) (B₀ * spacingScale M)
  have hK : 0 < K := (show 0 < 6*D by positivity).trans_le (le_max_left _ _)
  refine ⟨max a₁ a₂, K, ha₁.trans (le_max_left _ _), hK, fun m hm a B ha hAB => ?_⟩
  have ha' : a₁ ≤ a := (le_max_left a₁ a₂).trans ha
  have ha'' : a₂ ≤ a := (le_max_right a₁ a₂).trans ha
  have ha0 : 0 < a := by linarith
  have hgap : 0 ≤ a ^ ((m + 1 : ℝ)⁻¹ - 1/2) - B ^ ((m + 1 : ℝ)⁻¹ - 1/2) := by
    apply sub_nonneg.mpr
    apply Real.rpow_le_rpow_of_nonpos ha0 hAB
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have h := inv_anti₀ (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≤ m+1 by linarith)
    norm_num at h
    linarith
  have hs0 := spacingScale_pos hm
  change _ ≤ K * ((m : ℝ)/spacingScale m) * _
  by_cases hlarge : M ≤ m
  · have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 m) {a B : ℝ} (ha : 2 ≤ a) (hab : a ≤ B) := by
      have ha₀ : 0 < a := by linarith
      exact retainedDensity_integral (m := m) (Finset.mem_Icc.mp hn).1 ha₀ (ha₀.trans_le hab)
    have h := hwindow m hm retainedDensity
      (fun n hn a B ha hab => by
        simpa only [arithmeticPrimitive, capturedPrimitive, powerGap, arithmeticRate, neg_sub]
          using hterm n hn ha hab)
      (D * ((m : ℝ)/spacingScale m)) (hDens m hlarge) a B ha' hAB
    apply h.trans
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (div_nonneg (Nat.cast_nonneg m) hs0.le)) hgap
  · have h := hlinear m hm a B ha'' hAB
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ hgap
    rw [← mul_div_assoc, le_div_iff₀ hs0]
    have hscale := spacingScale_mono hm (Nat.le_of_lt (lt_of_not_ge hlarge))
    have hk : B₀ * spacingScale m ≤ K :=
      (mul_le_mul_of_nonneg_left hscale hB₀.le).trans (le_max_right _ _)
    nlinarith only [mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg m)]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
