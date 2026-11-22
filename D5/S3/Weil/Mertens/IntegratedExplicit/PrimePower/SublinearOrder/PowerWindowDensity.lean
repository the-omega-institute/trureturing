/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/PowerWindowDensity
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/PowerWindowDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Power-weighted response estimates for the signed prime-window density. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusSublinear
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.TrivialResponse
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusWindowTransfer

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

theorem range_moebius_prefix_of_Ioc_power_bound {β D : ℝ} (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (hprefix : ∀ k : ℕ, 1 ≤ k → |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ D*(k : ℝ)^β)
    (m k : ℕ) (hk : k ≤ m+1) :
    |∑ n ∈ Finset.range k, (μ n : ℝ)| ≤ D*(((m : ℝ)+1)^β) := by
  cases k with
  | zero => simpa using (show 0 ≤ D*(((m : ℝ)+1)^β) by positivity)
  | succ k =>
    have he : Finset.range (k+1) = insert 0 (Finset.Ioc 0 k) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [he, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, Int.cast_zero, zero_add]
    by_cases hk₁ : 1 ≤ k
    · refine (hprefix k hk₁).trans (mul_le_mul_of_nonneg_left ?_ hD)
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hβ
      have h : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
      linarith
    · have hzero : k = 0 := by omega
      subst k
      simpa using (show 0 ≤ D*(((m : ℝ)+1)^β) by positivity)

private theorem centered_sum_of_power_prefix {β κ D F : ℝ} (hβ : 0 ≤ β)
    (hβκ : β < κ) (hD : 0 < D) (hF : 0 < F)
    (hprefix : ∀ k : ℕ, 1 ≤ k →
      |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ D*(k : ℝ)^β)
    (hfar : ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, (m : ℝ)+1 ≤ u →
      |∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
        -(μ n : ℝ) * rootDensity n u| ≤
        F * (((m : ℝ)+1)^κ) * Real.exp (-(orderRate m)*u)) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m,
        -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| ≤
        K * (((m : ℝ)+1)^κ) * Real.exp (-(orderRate m)*u) := by
  have hpre (m k : ℕ) (hkm : k ≤ m) :
      |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ D*(((m : ℝ)+1)^β) := by
    by_cases hk : 1 ≤ k
    · exact (hprefix k hk).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by
          have h : (k : ℝ) ≤ m := by exact_mod_cast hkm
          linarith) hβ) hD.le)
    · have hz : k = 0 := by omega
      subst k
      simpa using (show 0 ≤ D*(((m : ℝ)+1)^β) by positivity)
  obtain ⟨C, hC, hnear⟩ := omitted_centered_near_of_prefix
  let c := |Real.log (2*Real.pi)|
  let δ := κ-β
  have hδ : 0 < δ := sub_pos.mpr hβκ
  let T₀ := (D+1)*(1+δ⁻¹+c)
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
  let Q := q^κ
  let H := D*q^β
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
      have hlog : Real.log k ≤ δ⁻¹*q^δ := (Real.log_le_log hk₀ hkq).trans
        (by simpa only [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hq₀.le hδ)
      have hb := Real.one_le_rpow hq hδ.le
      have ha := Real.one_le_rpow hq hβ
      have hleft : H+1 ≤ (D+1)*q^β := by dsimp [H]; linarith only [ha]
      have hright : 1+Real.log (k : ℝ)+c ≤ (1+δ⁻¹+c)*q^δ := by
        nlinarith only [hlog, hb, mul_le_mul_of_nonneg_left hb hc]
      have hcoef : (H+1)*(1+Real.log k+c) ≤ T₀*Q := by
        calc
          _ ≤ ((D+1)*q^β)*((1+δ⁻¹+c)*q^δ) :=
            mul_le_mul hleft hright
              (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega))])
              (by positivity)
          _ = T₀*Q := by
            rw [show ((D+1)*q^β)*((1+δ⁻¹+c)*q^δ) =
              T₀*(q^β*q^δ) by dsimp [T₀]; ring, ← Real.rpow_add hq₀]
            simp [Q, δ]
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
      simpa only [h, centered, neg_mul, Finset.sum_neg_distrib, abs_neg] using
        hnear m p u H hp₂ hu (hpre m)
    have hz : |∑ n ∈ T, h n| ≤ C * Real.exp 2 * D * Q * W := by
      refine hh'.trans ?_
      have hpowe : q^β ≤ Q :=
        Real.rpow_le_rpow_of_exponent_le hq hβκ.le
      exact (mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hexp hC.le)
          (mul_le_mul_of_nonneg_left hpowe hD.le) hH (by positivity))
        hEW (Real.exp_nonneg _) (by positivity)).trans_eq (by ring)
    rw [he]
    refine ((abs_add_le _ _).trans (add_le_add (htriv (m/2) (Nat.div_le_self _ _)) hz)).trans ?_
    have hCmax : C * (Real.exp 2) * D ≤ max F (C * (Real.exp 2) * D) := le_max_right _ _
    dsimp [K]
    nlinarith only [mul_le_mul_of_nonneg_right hCmax (mul_nonneg hQ hW)]

/-- The ordinary prefix estimate controls the arithmetic, near and trivial-root responses.
A separate signed spectral estimate controls the far response. -/
theorem window_density_of_power_prefix (hRH : RiemannHypothesis) {β κ P F : ℝ}
    (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (hβκ : β < κ) (hP : 0 < P) (hF : 0 < F)
    (hprefix : ∀ k : ℕ, 1 ≤ k → |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ P*(k : ℝ)^β)
    (hfar : ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, (m : ℝ)+1 ≤ u →
      |∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
        -(μ n : ℝ) * rootDensity n u| ≤
        F * (((m : ℝ)+1)^κ) * Real.exp (-(orderRate m)*u)) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * (((m : ℝ)+1)^κ) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨D, hD, hsum'⟩ := centered_sum_of_power_prefix hβ hβκ hP hF hprefix hfar
  obtain ⟨A, hA, htail⟩ := normalized_mobius_tail_of_power_prefix
    hβ hβ₁ hprefix
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
  let q := ((m : ℝ)+1)^κ
  have hbase : (1 : ℝ) ≤ (m : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hR : |R| ≤ A*q*W :=
    (htail m hm u hx).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase hβκ.le) hA.le) hW)
  have hQ : 1 ≤ q := Real.one_le_rpow hbase (hβ.trans hβκ.le)
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

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
