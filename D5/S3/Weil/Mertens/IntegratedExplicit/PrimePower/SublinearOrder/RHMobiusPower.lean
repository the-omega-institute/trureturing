/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusPower
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusPower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Power-saving order bound for the signed RH prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusSublinear
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.TrivialResponse
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.SignedOmittedSpectrum
import D5.S3.Weil.ZetaPntBounds.MobiusEnergyPointwise

/-! Power-saving bounds on the signed prime-tail remainder under RH. -/

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

private theorem mobius_prefix_rh_power (hRH : RiemannHypothesis) :
    ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ, 1 ≤ k →
      |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ D*(k : ℝ)^(3/4 : ℝ) := by
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
  refine ⟨D, hD, fun k hk => ?_⟩
  have hset : Finset.Ioc 0 k = Finset.Icc 1 k := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset]
  simpa only [show (2+(1/4 : ℝ))/3 = 3/4 by norm_num] using hprefix k hk

private theorem centered_sum_power (hRH : RiemannHypothesis) {D : ℝ} (hD : 0 < D)
    (hprefix : ∀ k : ℕ, 1 ≤ k →
      |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ D*(k : ℝ)^(3/4 : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m,
        -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| ≤
        K * (((m : ℝ)+1)^(27/28 : ℝ)) * Real.exp (-(orderRate m)*u) := by
  have hpre (m k : ℕ) (hkm : k ≤ m) :
      |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ D*(((m : ℝ)+1)^(3/4 : ℝ)) := by
    by_cases hk : 1 ≤ k
    · exact (hprefix k hk).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by
          have h : (k : ℝ) ≤ m := by exact_mod_cast hkm
          linarith) (by norm_num)) hD.le)
    · have hz : k = 0 := by omega
      subst k
      simpa using (show 0 ≤ D*(((m : ℝ)+1)^(3/4 : ℝ)) by positivity)
  have hpre' (m : ℕ) (_ : 2 ≤ m) (k : ℕ) (hk : k ≤ m+1) :
      |∑ n ∈ Finset.range k, (μ n : ℝ)| ≤ D*(((m : ℝ)+1)^(3/4 : ℝ)) := by
    cases k with
    | zero => simpa using (show 0 ≤ D*(((m : ℝ)+1)^(3/4 : ℝ)) by positivity)
    | succ k =>
      have he : Finset.range (k+1) = insert 0 (Finset.Ioc 0 k) := by
        ext n
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
        omega
      rw [he, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, Int.cast_zero, zero_add]
      exact hpre m k (by omega)
  obtain ⟨F, hF, hfar⟩ := signed_omitted_root_density_power hRH hpre'
  obtain ⟨C, hC, hnear⟩ := omitted_centered_near_of_prefix
  let c := |Real.log (2*Real.pi)|
  let T₀ := (D+1)*(9+c)
  let K := T₀ + max F (C * (Real.exp 2) * D)
  have hc : 0 ≤ c := abs_nonneg _
  have hT₀ : 0 ≤ T₀ := by dsimp [T₀]; positivity
  refine ⟨K, by dsimp [K]; linarith [le_max_left F (C * (Real.exp 2) * D)], ?_⟩
  intro m hm u hu
  let S := Finset.Icc 2 m
  let T := S.filter (fun n => m+1 ≤ 2*n)
  let p := max 2 ((m+2)/2)
  let q := (m : ℝ)+1
  let W := Real.exp (-(orderRate m)*u)
  let Q := q^(27/28 : ℝ)
  let H := D*q^(3/4 : ℝ)
  let f (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)
  let g (n : ℕ) := -(μ n : ℝ) * rootDensity (n : ℝ) u
  let h (n : ℕ) := -(μ n : ℝ) * centered (n : ℝ) (Real.exp u)
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hq₀ := zero_lt_one.trans_le hq
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hW : 0 ≤ W := Real.exp_nonneg _
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hEW : Real.exp (-u/2) ≤ W := exp_half_le_order m hu
  have htriv (k : ℕ) (hkm : k ≤ m) :
      |∑ n ∈ Finset.Icc 2 k, f n| ≤ T₀*Q*W := by
    by_cases hk : 2 ≤ k
    · have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkq : (k : ℝ) ≤ q := by
        have hkc : (k : ℝ) ≤ m := by exact_mod_cast hkm
        dsimp [q]
        linarith
      have hlog := (Real.log_le_log hk₀ hkq).trans
        (show Real.log q ≤ 8*q^(1/8 : ℝ) by
          linarith only [Real.log_le_rpow_div hq₀.le (by norm_num : (0 : ℝ) < 1/8)])
      have hb := Real.one_le_rpow hq (by norm_num : (0 : ℝ) ≤ 1/8)
      have ha := Real.one_le_rpow hq (by norm_num : (0 : ℝ) ≤ 3/4)
      have hleft : H+1 ≤ (D+1)*q^(3/4 : ℝ) := by dsimp [H]; linarith only [ha]
      have hright : 1+Real.log (k : ℝ)+c ≤ (9+c)*q^(1/8 : ℝ) := by
        nlinarith only [hlog, hb, mul_le_mul_of_nonneg_left hb hc]
      have hcoef : (H+1)*(1+Real.log k+c) ≤ T₀*Q := by
        calc
          _ ≤ ((D+1)*q^(3/4 : ℝ))*((9+c)*q^(1/8 : ℝ)) :=
            mul_le_mul hleft hright
              (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega))])
              (by positivity)
          _ = T₀*q^(7/8 : ℝ) := by
            rw [show ((D+1)*q^(3/4 : ℝ))*((9+c)*q^(1/8 : ℝ)) =
              T₀*(q^(3/4 : ℝ)*q^(1/8 : ℝ)) by dsimp [T₀]; ring,
              ← Real.rpow_add hq₀]
            norm_num
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hq (by norm_num)) hT₀
      exact (trivial_response_of_mobius_prefix k hu (fun j hj => hpre m j (hj.trans hkm))).trans
        (mul_le_mul hcoef hEW (Real.exp_nonneg _) (mul_nonneg hT₀ hQ))
    · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hk), Finset.sum_empty, abs_zero]
      exact mul_nonneg (mul_nonneg hT₀ hQ) hW
  by_cases huq : q ≤ u
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
    rw [he]
    refine ((abs_add_le _ _).trans (add_le_add (htriv m le_rfl) (hfar m hm u huq))).trans ?_
    have hFmax : F ≤ max F (C * (Real.exp 2) * D) := le_max_left _ _
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
    have hexp : Real.exp (u/(p : ℝ)) ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr ((div_le_iff₀ hp0).2 ((le_of_not_ge huq).trans hhalf'))
    have hh' : |∑ n ∈ T, h n| ≤ C * Real.exp (u/(p : ℝ)) * H * Real.exp (-u/2) := by
      rw [hTp]
      have hpm : p ≤ m := by dsimp [p]; omega
      simpa only [h, centered, neg_mul, Finset.sum_neg_distrib, abs_neg] using
        hnear m p u H hp₂ hpm hu (hpre m)
    have hz : |∑ n ∈ T, h n| ≤ C * Real.exp 2 * D * Q * W := by
      refine hh'.trans ?_
      have hpowe : q^(3/4 : ℝ) ≤ Q :=
        Real.rpow_le_rpow_of_exponent_le hq (by norm_num)
      exact (mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hexp hC.le)
          (mul_le_mul_of_nonneg_left hpowe hD.le) hH (by positivity))
        hEW (Real.exp_nonneg _) (by positivity)).trans_eq (by ring)
    rw [he]
    refine ((abs_add_le _ _).trans (add_le_add (htriv (m/2) (Nat.div_le_self _ _)) hz)).trans ?_
    have hCmax : C * (Real.exp 2) * D ≤ max F (C * (Real.exp 2) * D) := le_max_right _ _
    dsimp [K]
    nlinarith only [mul_le_mul_of_nonneg_right hCmax (mul_nonneg hQ hW)]

private theorem density_power (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * (((m : ℝ)+1)^(27/28 : ℝ)) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨P, hP, hprefix⟩ := mobius_prefix_rh_power hRH
  obtain ⟨D, hD, hsum'⟩ := centered_sum_power hRH hP hprefix
  obtain ⟨A, hA, htail⟩ := normalized_mobius_tail_of_power_prefix
    (β := 3/4) (by norm_num) (by norm_num) hprefix
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
  let q := ((m : ℝ)+1)^(27/28 : ℝ)
  have hbase : (1 : ℝ) ≤ (m : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hR : |R| ≤ A*q*W :=
    (htail m hm u hx).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)) hA.le) hW)
  have hQ : 1 ≤ q := Real.one_le_rpow hbase (by norm_num)
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

/-- A uniform power-saving order bound for the signed Möbius prime-tail interval. -/
theorem prime_window_mobius_power_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧
      ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * (m : ℝ)^(27/28 : ℝ) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨a₀, ha₀, hwindow⟩ := prime_window_threshold_of_rh hRH
  obtain ⟨D, hD, hDens⟩ := density_power hRH
  refine ⟨a₀, 12*D, ha₀, by positivity, fun m hm a B ha hAB => ?_⟩
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 m) {a B : ℝ} (ha : 2 ≤ a) (hab : a ≤ B) := by
    have ha₀ : 0 < a := by linarith
    exact retainedDensity_integral (m := m) (Finset.mem_Icc.mp hn).1 ha₀ (ha₀.trans_le hab)
  have h := hwindow m hm retainedDensity
    (fun n hn a B ha hab => by
      simpa only [arithmeticPrimitive, capturedPrimitive, powerGap, arithmeticRate, neg_sub]
        using hterm n hn ha hab)
    (D * ((m : ℝ)+1)^(27/28 : ℝ)) (hDens m hm) a B ha hAB
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpower : ((m : ℝ)+1)^(27/28 : ℝ) ≤ 2*(m : ℝ)^(27/28 : ℝ) := by
    refine (Real.rpow_le_rpow (by positivity) (show (m : ℝ)+1 ≤ 2*(m : ℝ) by linarith)
      (by norm_num : (0 : ℝ) ≤ 27/28)).trans ?_
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (27/28 : ℝ) ≤ 1)
  have ha' : 0 < a := by linarith
  have hgap : 0 ≤ a ^ ((m + 1 : ℝ)⁻¹ - 1/2) - B ^ ((m + 1 : ℝ)⁻¹ - 1/2) := by
    apply sub_nonneg.mpr
    apply Real.rpow_le_rpow_of_nonpos ha' hAB
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ m+1 by linarith)
    norm_num at hi
    linarith
  have hcoef : 6*(D*((m : ℝ)+1)^(27/28 : ℝ)) ≤ (12*D)*(m : ℝ)^(27/28 : ℝ) := by
    calc
      _ = (6*D)*((m : ℝ)+1)^(27/28 : ℝ) := by ring
      _ ≤ (6*D)*(2*(m : ℝ)^(27/28 : ℝ)) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right hcoef hgap)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
