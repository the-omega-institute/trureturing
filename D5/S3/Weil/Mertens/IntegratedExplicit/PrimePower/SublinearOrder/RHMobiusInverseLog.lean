/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusInverseLog
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusInverseLog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inverse-logarithmic RH prime window from power-saving Möbius prefixes. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusSublinear
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.TrivialResponse
import D5.S3.Weil.ZetaPntBounds.MobiusEnergyPointwise

/-! Signed inverse-logarithmic bounds on the actual prime window under RH. -/

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
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (spectralPrimitive windowDiscrepancy)

private def logOrder (m : ℕ) : ℝ := Real.log ((m : ℝ) + 1)

private theorem logOrder_pos {m : ℕ} (hm : 2 ≤ m) : 0 < logOrder m := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  exact Real.log_pos (by linarith)

private theorem logOrder_le_order (m : ℕ) : logOrder m ≤ m := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) + 1 by positivity)
  dsimp [logOrder]
  linarith

private theorem inverse_log_far_budget {m : ℕ} (hm : 2 ≤ m) {u : ℝ}
    (hu : (1 + logOrder m / 16) * ((m : ℝ) + 1) ≤ u) :
    1 + ((m : ℝ) + 1)^2/u + ((m : ℝ) + 1)^(7/8 : ℝ) ≤
      48 * ((m : ℝ)/logOrder m) := by
  let q := (m : ℝ) + 1
  let t := logOrder m
  have ht : 0 < t := logOrder_pos hm
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hqm : q ≤ (3/2) * (m : ℝ) := by dsimp [q]; linarith
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hsmall : t*q/16 ≤ u := by
    change (1+t/16)*q ≤ u at hu
    nlinarith only [hu, hq]
  have hu0 : 0 < u := (show 0 < t*q/16 by positivity).trans_le hsmall
  have htq : t ≤ 8*q^(1/8 : ℝ) := by
    have h := Real.log_le_rpow_div hq0.le (by norm_num : (0 : ℝ) < 1/8)
    change Real.log q ≤ _
    linarith only [h]
  have hpow : t*q^(7/8 : ℝ) ≤ 8*q := by
    refine (mul_le_mul_of_nonneg_right htq (Real.rpow_nonneg hq0.le _)).trans_eq ?_
    rw [mul_assoc, ← Real.rpow_add hq0]
    norm_num
  have hbase : t ≤ 8*q := by
    have h := logOrder_le_order m
    dsimp [t, q]
    linarith
  have hratio : q^2/u*t ≤ 16*q := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hu0).2
    have h := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 16*q by positivity)
    nlinarith only [h]
  change 1 + q^2/u + q^(7/8 : ℝ) ≤ 48 * ((m : ℝ)/t)
  rw [← mul_div_assoc, le_div_iff₀ ht]
  nlinarith only [hpow, hbase, hratio, hqm]

private theorem inverse_log_near_budget {m : ℕ} (hm : 2 ≤ m) :
    Real.exp (2*(1 + logOrder m / 16)) * (m : ℝ)^(3/4 : ℝ) ≤
      (12*Real.exp 2) * ((m : ℝ)/logOrder m) := by
  let q := (m : ℝ) + 1
  let t := logOrder m
  have ht : 0 < t := logOrder_pos hm
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hqm : q ≤ (3/2) * (m : ℝ) := by dsimp [q]; linarith
  have hq0 : 0 < q := by dsimp [q]; positivity
  have htq : t ≤ 8*q^(1/8 : ℝ) := by
    have h := Real.log_le_rpow_div hq0.le (by norm_num : (0 : ℝ) < 1/8)
    change Real.log q ≤ _
    linarith only [h]
  have hmPow : (m : ℝ)^(3/4 : ℝ) ≤ q^(3/4 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by dsimp [q]; linarith) (by norm_num)
  have hexp : Real.exp (2*(1+t/16)) = Real.exp 2 * q^(1/8 : ℝ) := by
    rw [show 2*(1+t/16) = 2 + Real.log q*(1/8) by change 2*(1+Real.log q/16) = _; ring,
      Real.exp_add, Real.rpow_def_of_pos hq0]
  change Real.exp (2*(1+t/16)) * (m : ℝ)^(3/4 : ℝ) ≤
    (12*Real.exp 2) * ((m : ℝ)/t)
  rw [hexp, ← mul_div_assoc, le_div_iff₀ ht]
  calc
    _ ≤ (Real.exp 2 * q^(1/8 : ℝ)) * q^(3/4 : ℝ) * (8*q^(1/8 : ℝ)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hmPow (by positivity)) htq ht.le
      positivity
    _ = 8*Real.exp 2*q := by
      rw [show (Real.exp 2 * q^(1/8 : ℝ)) * q^(3/4 : ℝ) * (8*q^(1/8 : ℝ)) =
        8*Real.exp 2*(q^(1/8 : ℝ)*q^(3/4 : ℝ)*q^(1/8 : ℝ)) by ring,
        ← Real.rpow_add hq0, ← Real.rpow_add hq0]
      norm_num
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hqm (Real.exp_nonneg 2)]

private theorem inverse_log_trivial_budget {m : ℕ} (hm : 2 ≤ m) {D c : ℝ}
    (hD : 0 ≤ D) (hc : 0 ≤ c) :
    (D*(m : ℝ)^(3/4 : ℝ)+1) * (1+Real.log m+c) ≤
      ((D+1)*(6*(1+c)+96)) * ((m : ℝ)/logOrder m) := by
  let q := (m : ℝ) + 1
  let t := logOrder m
  have ht : 0 < t := logOrder_pos hm
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hqm : q ≤ (3/2) * (m : ℝ) := by dsimp [q]; linarith
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have htq : t ≤ 4*q^(1/4 : ℝ) := by
    have h := Real.log_le_rpow_div hq0.le (by norm_num : (0 : ℝ) < 1/4)
    change Real.log q ≤ _
    linarith only [h]
  have htq' : t ≤ 8*q^(1/8 : ℝ) := by
    have h := Real.log_le_rpow_div hq0.le (by norm_num : (0 : ℝ) < 1/8)
    change Real.log q ≤ _
    linarith only [h]
  have hmPow : (m : ℝ)^(3/4 : ℝ) ≤ q^(3/4 : ℝ) :=
    Real.rpow_le_rpow hm0.le (by dsimp [q]; linarith) (by norm_num)
  have hpow : 1 ≤ q^(3/4 : ℝ) := Real.one_le_rpow hq (by norm_num)
  have hlog : Real.log (m : ℝ) ≤ t := Real.log_le_log hm0 (show (m : ℝ) ≤ (m : ℝ) + 1 by linarith)
  change _ ≤ ((D+1)*(6*(1+c)+96)) * ((m : ℝ)/t)
  rw [← mul_div_assoc, le_div_iff₀ ht]
  have hcoef : D*(m : ℝ)^(3/4 : ℝ)+1 ≤ (D+1)*q^(3/4 : ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_left hmPow hD, hpow]
  have hlin : t*q^(3/4 : ℝ) ≤ 4*q := by
    refine (mul_le_mul_of_nonneg_right htq (Real.rpow_nonneg hq0.le _)).trans_eq ?_
    rw [mul_assoc, ← Real.rpow_add hq0]
    norm_num
  have hsq : t^2*q^(3/4 : ℝ) ≤ 64*q := by
    refine (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ ht.le htq' 2) (Real.rpow_nonneg hq0.le _)).trans_eq ?_
    rw [show (8*q^(1/8 : ℝ))^2*q^(3/4 : ℝ) =
      64*(q^(1/8 : ℝ)*q^(1/8 : ℝ)*q^(3/4 : ℝ)) by ring,
      ← Real.rpow_add hq0, ← Real.rpow_add hq0]
    norm_num
  have hfactor : 0 ≤ 1+Real.log (m : ℝ)+c := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ m by linarith)]
  calc
    _ ≤ ((D+1)*q^(3/4 : ℝ)) * (1+t+c) * t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hcoef (by linarith) hfactor (by positivity)) ht.le
    _ = (D+1)*((1+c)*(t*q^(3/4 : ℝ))+t^2*q^(3/4 : ℝ)) := by ring
    _ ≤ (D+1)*((1+c)*(4*q)+64*q) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hlin (by positivity)) hsq) (by positivity)
    _ ≤ _ := by
      calc
        _ = ((D+1)*(4*(1+c)+64))*q := by ring
        _ ≤ ((D+1)*(4*(1+c)+64))*((3/2)*(m : ℝ)) :=
          mul_le_mul_of_nonneg_left hqm (by positivity)
        _ = _ := by ring

theorem mobius_prefix_rh_power (hRH : RiemannHypothesis) :
    ∃ D : ℝ, 0 < D ∧ ∀ m k : ℕ, k ≤ m →
      |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ D*(m : ℝ)^(3/4 : ℝ) := by
  have hzero (z : ℂ) (hz : 1/2 < z.re) (hne : z ≠ 1) : riemannZeta z ≠ 0 := by
    intro hroot
    have htriv : ¬ ∃ n : ℕ, z = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      simp at hz
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (ne_of_gt hz) (hRH z hroot htriv hne)
  obtain ⟨D, hD, hprefix⟩ :=
    @D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.unweighted_mobius_prefix_power_bound
      (1/2) (1/4) (by norm_num) (by norm_num) hzero (by norm_num) (by norm_num)
  refine ⟨D, hD, fun m k hkm => ?_⟩
  by_cases hk : 1 ≤ k
  · have hset : Finset.Ioc 0 k = Finset.Icc 1 k := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hset]
    have h := hprefix k hk
    norm_num at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkm) (by norm_num)) hD.le)
  · have hzero : k = 0 := by omega
    subst k
    simpa using (show 0 ≤ D*(m : ℝ)^(3/4 : ℝ) by positivity)

private theorem centered_sum_inverse_log (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m,
        -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| ≤
        K * ((m : ℝ)/logOrder m) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨F, hF, hfar⟩ := omitted_root_density_spacing hRH
  obtain ⟨D, hD, hprefix⟩ := mobius_prefix_rh_power hRH
  obtain ⟨C, hC, hnear⟩ := omitted_centered_near_of_prefix
  let c := |Real.log (2*Real.pi)|
  let T₀ := (D+1)*(6*(1+c)+96)
  let K := T₀ + max (48*F) (12*Real.exp 2*C*D)
  have hc : 0 ≤ c := abs_nonneg _
  have hT₀ : 0 ≤ T₀ := by dsimp [T₀]; positivity
  refine ⟨K, by dsimp [K]; linarith [le_max_left (48*F) (12*Real.exp 2*C*D)], ?_⟩
  intro m hm u hu
  let S := Finset.Icc 2 m
  let T := S.filter (fun n => m+1 ≤ 2*n)
  let p := max 2 ((m+2)/2)
  let L := 1 + logOrder m / 16
  let W := Real.exp (-(orderRate m)*u)
  let Q := (m : ℝ)/logOrder m
  let H := D*(m : ℝ)^(3/4 : ℝ)
  let f (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)
  let g (n : ℕ) := -(μ n : ℝ) * rootDensity (n : ℝ) u
  let h (n : ℕ) := -(μ n : ℝ) * centered (n : ℝ) (Real.exp u)
  have hL : 1 ≤ L := by dsimp [L]; linarith [logOrder_pos hm]
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hW : 0 ≤ W := Real.exp_nonneg _
  have hQ : 0 ≤ Q := div_nonneg (Nat.cast_nonneg _) (logOrder_pos hm).le
  have hEW : Real.exp (-u/2) ≤ W := exp_half_le_order m hu
  have htriv (k : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m) :
      |∑ n ∈ Finset.Icc 2 k, f n| ≤ T₀*Q*W := by
    have hlog : Real.log (k : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast hkm)
    refine (trivial_response_of_mobius_prefix k hu
      (fun j hj => hprefix m j (hj.trans hkm))).trans ?_
    have hcoef : (H+1)*(1+Real.log k+c) ≤ T₀*Q := by
      calc
        _ ≤ (H+1)*(1+Real.log m+c) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ _ := inverse_log_trivial_budget hm hD.le hc
    exact mul_le_mul hcoef hEW (Real.exp_nonneg _) (mul_nonneg hT₀ hQ)
  have htriv_all (k : ℕ) (hkm : k ≤ m) : |∑ n ∈ Finset.Icc 2 k, f n| ≤ T₀*Q*W := by
    by_cases hk : 2 ≤ k
    · exact htriv k hk hkm
    · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hk), Finset.sum_empty, abs_zero]
      exact mul_nonneg (mul_nonneg hT₀ hQ) hW
  by_cases huL : L*((m : ℝ) + 1) ≤ u
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
    have hqu : (m : ℝ) + 1 ≤ u :=
      (le_mul_of_one_le_left (by positivity) hL).trans huL
    have hz : |∑ n ∈ T, g n| ≤ 48*F*Q*W := by
      have hsumabs : |∑ n ∈ T, g n| ≤ ∑ n ∈ T, |rootDensity (n : ℝ) u| := by
        refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro n hn
        unfold g
        rw [abs_mul, abs_neg]
        exact mul_le_of_le_one_left (abs_nonneg _)
          (by exact_mod_cast abs_moebius_le_one (n := n))
      refine (hsumabs.trans (hfar m hm u hqu)).trans ?_
      calc
        _ ≤ W * (F * (48*Q)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (inverse_log_far_budget hm huL) hF.le) hW
        _ = _ := by ring
    rw [he]
    refine ((abs_add_le _ _).trans (add_le_add (htriv m hm le_rfl) hz)).trans ?_
    have hFmax : (48*F : ℝ) ≤ max (48*F) (12*Real.exp 2*C*D) := le_max_left _ _
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
    have hhalf : m+1 ≤ 2*p := by dsimp [p]; omega
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hhalf' : (m : ℝ) + 1 ≤ 2*(p : ℝ) := by exact_mod_cast hhalf
    have hexp : Real.exp (u/(p : ℝ)) ≤ Real.exp (2*L) := by
      apply Real.exp_le_exp.mpr
      exact (div_le_iff₀ hp0).2 ((le_of_not_ge huL).trans
        ((mul_le_mul_of_nonneg_left hhalf' (by linarith : 0 ≤ L)).trans_eq (by ring)))
    have hh := (hnear m p u H hp₂ hu (hprefix m)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC.le) hH)
        (Real.exp_nonneg _))
    have hh' : |∑ n ∈ T, h n| ≤ C * Real.exp (2*L) * H * Real.exp (-u/2) := by
      rw [hTp]
      simpa only [h, centered, neg_mul, Finset.sum_neg_distrib, abs_neg] using hh
    have hz : |∑ n ∈ T, h n| ≤ 12*Real.exp 2*C*D*Q*W := by
      refine hh'.trans ?_
      rw [show C*Real.exp (2*L)*H = (C*D)*(Real.exp (2*L)*(m : ℝ)^(3/4 : ℝ)) by
        dsimp [H]; ring]
      exact (mul_le_mul
        (mul_le_mul_of_nonneg_left (inverse_log_near_budget hm) (by positivity : 0 ≤ C*D))
        hEW (Real.exp_nonneg _) (by positivity)).trans_eq (by ring)
    rw [he]
    refine ((abs_add_le _ _).trans (add_le_add (htriv_all (m/2) (Nat.div_le_self _ _)) hz)).trans ?_
    have hCmax : (12*Real.exp 2*C*D : ℝ) ≤ max (48*F) (12*Real.exp 2*C*D) := le_max_right _ _
    dsimp [K]
    nlinarith only [mul_le_mul_of_nonneg_right hCmax (mul_nonneg hQ hW)]

private theorem density_inverse_log (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * ((m : ℝ)/logOrder m) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨D, hD, hsum'⟩ := centered_sum_inverse_log hRH
  obtain ⟨A, hA, htail⟩ := normalized_mobius_tail_one_log hRH
  let C := |Real.log (2*Real.pi)|
  refine ⟨A+D+C, by dsimp [C]; positivity, fun m hm u hu => ?_⟩
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
  let q := (m : ℝ)/logOrder m
  have hR : |R| ≤ A*q*W := htail m hm u hx
  have hQ : 1 ≤ q := (one_le_div (logOrder_pos hm)).2 (logOrder_le_order m)
  have hE : |E| ≤ C*q*W := by
    have hbound := (RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le hu0).le
    refine hbound.trans ?_
    rw [mul_comm (Real.exp _)]
    have hcoef : Real.log (2*Real.pi) ≤ C*q := by
      calc
        _ ≤ C := le_abs_self _
        _ = C * 1 := (mul_one _).symm
        _ ≤ C * q := mul_le_mul_of_nonneg_left hQ (abs_nonneg _)
        _ = _ := by ring
    exact mul_le_mul hcoef (exp_half_le_order m hu0) (Real.exp_nonneg _) (by dsimp [C, q]; positivity)
  have hsum : |∑ n ∈ Finset.Icc 2 m, e n| ≤ D*q*W := hsum' m hm u hu0
  rw [show rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2) =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E from mobius_window_density_split m u]
  calc
    _ ≤ |R| + |∑ n ∈ Finset.Icc 2 m, e n| + |E| := by
      simpa only [abs_neg] using (abs_add_le (-R + ∑ n ∈ Finset.Icc 2 m, e n) E).trans
        (add_le_add (abs_add_le (-R) (∑ n ∈ Finset.Icc 2 m, e n)) (le_refl |E|))
    _ ≤ A*q*W + D*q*W + C*q*W := add_le_add (add_le_add hR hsum) hE
    _ = _ := by dsimp [q, W]; ring

/-- A uniform inverse logarithmic rate for the signed Möbius prime-tail interval. -/
theorem prime_window_mobius_inverse_log_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧
      ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * ((m : ℝ) / Real.log ((m : ℝ) + 1)) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨a₀, ha₀, hwindow⟩ := prime_window_threshold_of_rh hRH
  obtain ⟨D, hD, hDens⟩ := density_inverse_log hRH
  refine ⟨a₀, 6*D, ha₀, by positivity, fun m hm a B ha hAB => ?_⟩
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 m) {a B : ℝ} (ha : 2 ≤ a) (hab : a ≤ B) := by
    have ha₀ : 0 < a := by linarith
    exact retainedDensity_integral (m := m) (Finset.mem_Icc.mp hn).1 ha₀ (ha₀.trans_le hab)
  have h := hwindow m hm retainedDensity
    (fun n hn a B ha hab => by
      simpa only [arithmeticPrimitive, capturedPrimitive, powerGap, arithmeticRate, neg_sub]
        using hterm n hn ha hab)
    (D * ((m : ℝ)/logOrder m)) (hDens m hm) a B ha hAB
  exact h.trans_eq (by dsimp [logOrder]; ring)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
