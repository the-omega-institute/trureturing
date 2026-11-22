/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusRate
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An explicit sublinear order rate for the actual prime-only Möbius window under RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.ArithmeticResponse
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

private theorem exp_half_le_order (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u/2) ≤ Real.exp (-(orderRate m)*u) := by
  apply Real.exp_le_exp.mpr
  unfold orderRate
  nlinarith only [mul_nonneg hu (show 0 ≤ (m+1 : ℝ)⁻¹ by positivity)]

private def orderScale (m : ℕ) : ℝ :=
  Real.sqrt (1 + Real.log (Real.log ((m : ℝ)+1)))

private theorem orderScale_pos {m : ℕ} (hm : 2 ≤ m) : 0 < orderScale m := by
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hsmall : Real.exp (-1) ≤ (1/2 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have ht : Real.exp (-1) < Real.log ((m : ℝ)+1) :=
    hsmall.trans_lt (hlog2.trans_lt (Real.log_lt_log (by norm_num) (by linarith)))
  have h := Real.log_lt_log (Real.exp_pos (-1)) ht
  rw [Real.log_exp] at h
  exact Real.sqrt_pos.mpr (by linarith)

private theorem orderScale_mono {m k : ℕ} (hm : 2 ≤ m) (hmk : m ≤ k) :
    orderScale m ≤ orderScale k := by
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmK : (m : ℝ) ≤ k := by exact_mod_cast hmk
  unfold orderScale
  exact Real.sqrt_le_sqrt (add_le_add (le_refl (1 : ℝ))
    (Real.log_le_log (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) (by linarith))))

private theorem quantitative_order_bounds :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M,
      let L := (1 + Real.log (Real.log ((m : ℝ)+1))) / 8
      2 ≤ Real.log (m : ℝ) ∧ 1 ≤ L ∧ L ≤ (m : ℝ) ∧
        orderScale m ≤ 3*(Real.log (m : ℝ))^(1/5 : ℝ) ∧
        orderScale m * (Real.exp (2*L) / Real.log (m : ℝ)) ≤ 12 := by
  obtain ⟨X, hX, hcut⟩ := logarithmic_order_cutoff_bounds
  obtain ⟨M, hM⟩ := exists_nat_ge X
  refine ⟨max 2 M, le_max_left _ _, fun m hm => ?_⟩
  have hMm := (le_max_right 2 M).trans hm
  obtain ⟨ht, hL, hLm, hscale, hExp⟩ := hcut (m : ℝ) (hM.trans (by exact_mod_cast hMm))
  refine ⟨ht, hL, hLm, ?_, hExp⟩
  have ht0 : 0 < Real.log (m : ℝ) := by linarith
  have hr := Real.rpow_pos_of_pos ht0 (1/5)
  dsimp only [orderScale]
  rw [show (-1/5 : ℝ) = -(1/5) by ring, Real.rpow_neg ht0.le, ← div_eq_mul_inv] at hscale
  exact (div_le_iff₀ hr).mp hscale

private theorem centered_sum_quantitative (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m,
        -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| ≤
        K * ((m : ℝ)/orderScale m) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨F, hF, hfar⟩ := omitted_root_density_inv_sqrt_far hRH
  obtain ⟨D, hD, htriv⟩ := trivial_response_signed_log_power_saving hRH
  obtain ⟨C, hC, hnear⟩ := omitted_centered_near_moebius_exp_bound hRH
  obtain ⟨M, hM, hcut⟩ := quantitative_order_bounds
  let K := 3*D + max (3*F) (12*C)
  refine ⟨K, by dsimp [K]; positivity, M, hM, fun m hm u hu => ?_⟩
  let S := Finset.Icc 2 m
  let T := S.filter (fun n => m+1 ≤ 2*n)
  let p := max 2 ((m+2)/2)
  let L := (1 + Real.log (Real.log ((m : ℝ)+1))) / 8
  let W := Real.exp (-(orderRate m)*u)
  let Q := (m : ℝ)/orderScale m
  let f (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)
  let g (n : ℕ) := -(μ n : ℝ) * rootDensity (n : ℝ) u
  let h (n : ℕ) := -(μ n : ℝ) * centered (n : ℝ) (Real.exp u)
  have hm₂ := hM.trans hm
  obtain ⟨ht, hL, hLm, hscale, hExp⟩ := hcut m hm
  have hW : 0 ≤ W := Real.exp_nonneg _
  have hQ : 0 ≤ Q := div_nonneg (Nat.cast_nonneg m) (orderScale_pos hm₂).le
  have hEW : Real.exp (-u/2) ≤ W := exp_half_le_order m hu
  have ht0 : 0 < Real.log (m : ℝ) := by linarith
  have htp := Real.rpow_pos_of_pos ht0 (1/5)
  have htriv' (k : ℕ) (hkm : k ≤ m) : |∑ n ∈ Finset.Icc 2 k, f n| ≤ 3*D*Q*W := by
    have hbase : (m : ℝ)/(Real.log (m : ℝ))^(1/5 : ℝ) ≤ 3*Q := by
      dsimp [Q]
      rw [← mul_div_assoc, div_le_div_iff₀ htp (orderScale_pos hm₂)]
      calc
        _ ≤ (m : ℝ)*(3*(Real.log (m : ℝ))^(1/5 : ℝ)) :=
          mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg m)
        _ = _ := by ring
    exact (htriv m hm₂ ht k hkm u hu).trans ((mul_le_mul
      (mul_le_mul_of_nonneg_left hbase hD.le) hEW (Real.exp_nonneg _) (by positivity)).trans_eq (by ring))
  change 1 ≤ L at hL
  change orderScale m * (Real.exp (2*L) / Real.log (m : ℝ)) ≤ 12 at hExp
  have hLq : L ≤ (m : ℝ)+1 := by change L ≤ (m : ℝ) at hLm; linarith
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
    have hscale_explicit : orderScale m = Real.sqrt L * Real.sqrt 8 := by
      dsimp [orderScale]
      rw [← Real.sqrt_mul (show 0 ≤ L by linarith)]
      congr 1
      dsimp [L]
      ring
    have hbase : (m : ℝ)/Real.sqrt L ≤ 3*Q := by
      have hL0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
      dsimp only [Q]
      rw [← mul_div_assoc, div_le_div_iff₀ hL0 (orderScale_pos hm₂), hscale_explicit]
      have h8 : Real.sqrt 8 ≤ 3 := (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
      nlinarith only [mul_le_mul_of_nonneg_left h8 (mul_nonneg (Nat.cast_nonneg m) hL0.le)]
    have hz : |∑ n ∈ T, g n| ≤ 3*F*Q*W := by
      have hsumabs : |∑ n ∈ T, g n| ≤ ∑ n ∈ T, |rootDensity (n : ℝ) u| := by
        refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro n hn
        unfold g
        rw [abs_mul, abs_neg]
        exact mul_le_of_le_one_left (abs_nonneg _)
          (by exact_mod_cast abs_moebius_le_one (n := n))
      exact (hsumabs.trans (hfar m hm₂ L hL hLq u huL)).trans
        ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hF.le) hW).trans_eq (by ring))
    rw [he]
    refine ((abs_add_le _ _).trans (add_le_add (htriv' m le_rfl) hz)).trans ?_
    have hFmax : (3*F : ℝ) ≤ max (3*F) (12*C) := le_max_left _ _
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
    have hbase : (m : ℝ) * (Real.exp (2*L) / Real.log m) ≤ 12*Q := by
      dsimp only [Q]
      rw [show 12 * ((m : ℝ) / orderScale m) = (12 * (m : ℝ)) / orderScale m by ring,
        le_div_iff₀ (orderScale_pos hm₂)]
      nlinarith only [mul_le_mul_of_nonneg_left hExp (Nat.cast_nonneg m)]
    have hz : |∑ n ∈ T, h n| ≤ 12*C*Q*W := by
      refine hh'.trans ?_
      rw [show C*Real.exp (2*L)*((m : ℝ)/Real.log m) =
        C*((m : ℝ)*(Real.exp (2*L)/Real.log m)) by ring]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hbase hC.le) hEW
        (Real.exp_nonneg _) (by positivity)).trans_eq (by ring)
    rw [he]
    refine ((abs_add_le _ _).trans (add_le_add (htriv' (m/2) (Nat.div_le_self _ _)) hz)).trans ?_
    have hCmax : (12*C : ℝ) ≤ max (3*F) (12*C) := le_max_right _ _
    dsimp [K]
    nlinarith only [mul_le_mul_of_nonneg_right hCmax (mul_nonneg hQ hW)]

private theorem density_quantitative (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * ((m : ℝ)/orderScale m) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨D, hD, M₁, hM₁, hsum'⟩ := centered_sum_quantitative hRH
  obtain ⟨A, hA, htail⟩ := normalized_mobius_tail_one_log hRH
  obtain ⟨M₂, hM₂, hcut⟩ := quantitative_order_bounds
  let C := |Real.log (2*Real.pi)|
  refine ⟨3*A+D+3*C, by dsimp [C]; positivity, max M₁ M₂, hM₁.trans (le_max_left _ _),
    fun m hm u hu => ?_⟩
  have hm₁ := (le_max_left M₁ M₂).trans hm
  have hm₂ := hM₁.trans hm₁
  obtain ⟨ht, _, _, hs, _⟩ := hcut m ((le_max_right M₁ M₂).trans hm)
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
  let q := (m : ℝ)/orderScale m
  have hm0 : (0 : ℝ) < m := by positivity
  have ht0 : 0 < Real.log (m : ℝ) := by linarith
  have ht1 : 1 ≤ Real.log (m : ℝ) := by linarith
  have hs0 := orderScale_pos hm₂
  have hlog : Real.log (m : ℝ) ≤ Real.log ((m : ℝ)+1) :=
    Real.log_le_log hm0 (by linarith)
  have hpow : (Real.log (m : ℝ))^(1/5 : ℝ) ≤ Real.log (m : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (1/5 : ℝ) ≤ 1)
    simpa only [Real.rpow_one] using h
  have hslog : orderScale m ≤ 3*Real.log (m : ℝ) :=
    hs.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
  have hbase : (m : ℝ)/Real.log ((m : ℝ)+1) ≤ 3*q := by
    dsimp only [q]
    rw [← mul_div_assoc, div_le_div_iff₀ (ht0.trans_le hlog) hs0]
    have h := mul_le_mul_of_nonneg_left (hslog.trans
      (mul_le_mul_of_nonneg_left hlog (by norm_num))) hm0.le
    nlinarith only [h]
  have hR : |R| ≤ 3*A*q*W := by
    exact (htail m hm₂ u hx).trans
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hA.le) hW).trans_eq (by ring))
  have hQ : 1 ≤ 3*q := by
    dsimp only [q]
    rw [← mul_div_assoc, one_le_div hs0]
    refine hslog.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    linarith [Real.log_le_sub_one_of_pos hm0]
  have hE : |E| ≤ 3*C*q*W := by
    have hbound := (RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le hu0).le
    refine hbound.trans ?_
    rw [mul_comm (Real.exp _)]
    have hcoef : Real.log (2*Real.pi) ≤ 3*C*q := by
      calc
        _ ≤ C := le_abs_self _
        _ = C * 1 := (mul_one _).symm
        _ ≤ C * (3*q) := mul_le_mul_of_nonneg_left hQ (abs_nonneg _)
        _ = _ := by ring
    exact mul_le_mul hcoef (exp_half_le_order m hu0) (Real.exp_nonneg _) (by dsimp [C, q]; positivity)
  have hsum : |∑ n ∈ Finset.Icc 2 m, e n| ≤ D*q*W := hsum' m hm₁ u hu0
  rw [show rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2) =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E from mobius_window_density_split m u]
  calc
    _ ≤ |R| + |∑ n ∈ Finset.Icc 2 m, e n| + |E| := by
      simpa only [abs_neg] using (abs_add_le (-R + ∑ n ∈ Finset.Icc 2 m, e n) E).trans
        (add_le_add (abs_add_le (-R) (∑ n ∈ Finset.Icc 2 m, e n)) (le_refl |E|))
    _ ≤ 3*A*q*W + D*q*W + 3*C*q*W := add_le_add (add_le_add hR hsum) hE
    _ = _ := by dsimp [q, W]; ring

/-- A uniform explicit order rate for the signed Möbius prime-tail interval. -/
theorem prime_window_mobius_quantitative_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧
      ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * ((m : ℝ) / Real.sqrt (1 + Real.log (Real.log ((m : ℝ)+1)))) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨a₁, ha₁, hwindow⟩ := prime_window_threshold_of_rh hRH
  obtain ⟨a₂, B₀, ha₂, hB₀, hlinear⟩ := prime_window_mobius_linear_of_rh hRH
  obtain ⟨D, hD, M, hM, hDens⟩ := density_quantitative hRH
  let K := max (6*D) (B₀ * orderScale M)
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
  have hs0 := orderScale_pos hm
  change _ ≤ K * ((m : ℝ)/orderScale m) * _
  by_cases hlarge : M ≤ m
  · have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 m) {a B : ℝ} (ha : 2 ≤ a) (hab : a ≤ B) := by
      have ha₀ : 0 < a := by linarith
      exact retainedDensity_integral (m := m) (Finset.mem_Icc.mp hn).1 ha₀ (ha₀.trans_le hab)
    have h := hwindow m hm retainedDensity
      (fun n hn a B ha hab => by
        simpa only [arithmeticPrimitive, capturedPrimitive, powerGap, arithmeticRate, neg_sub]
          using hterm n hn ha hab)
      (D * ((m : ℝ)/orderScale m)) (hDens m hlarge) a B ha' hAB
    apply h.trans
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (div_nonneg (Nat.cast_nonneg m) hs0.le)) hgap
  · have h := hlinear m hm a B ha'' hAB
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ hgap
    rw [← mul_div_assoc, le_div_iff₀ hs0]
    have hscale := orderScale_mono hm (Nat.le_of_lt (lt_of_not_ge hlarge))
    have hk : B₀ * orderScale m ≤ K :=
      (mul_le_mul_of_nonneg_left hscale hB₀.le).trans (le_max_right _ _)
    nlinarith only [mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg m)]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
