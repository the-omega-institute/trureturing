/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSublinear
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusSublinear
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform sublinear order dependence for the actual prime-only Möbius window under RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.ArithmeticResponse
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.OmittedSpectrum

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

private theorem eventually_logarithmic_order_le {C δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, C * ((m : ℝ) / Real.log m) ≤ δ * (m : ℝ) := by
  obtain ⟨K, hK⟩ := exists_nat_ge (Real.exp (C/δ))
  refine ⟨max 2 K, le_max_left _ _, fun m hm => ?_⟩
  have hm₂ : 2 ≤ m := (le_max_left 2 K).trans hm
  have hKm : K ≤ m := (le_max_right 2 K).trans hm
  have hm₂' : (2 : ℝ) ≤ m := by exact_mod_cast hm₂
  have hlog : 0 < Real.log m := Real.log_pos (by linarith)
  have hlim := Real.log_le_log (Real.exp_pos (C/δ)) (hK.trans (show (K : ℝ) ≤ (m : ℝ) by exact_mod_cast hKm))
  rw [Real.log_exp] at hlim
  have hC : C ≤ δ * Real.log m := by linarith only [(div_le_iff₀ hδ).mp hlim]
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hlog).mpr (by
    have h := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg m)
    nlinarith only [h])

private theorem exp_half_le_order (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u/2) ≤ Real.exp (-(orderRate m)*u) := by
  apply Real.exp_le_exp.mpr
  unfold orderRate
  nlinarith only [mul_nonneg hu (show 0 ≤ (m+1 : ℝ)⁻¹ by positivity)]

private theorem centered_sum_sublinear (hRH : RiemannHypothesis) :
    ∀ ε > (0 : ℝ), ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m,
        -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| ≤
        ε * (m : ℝ) * Real.exp (-(orderRate m)*u) := by
  intro ε hε
  let δ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨L, F, hL, _, hF⟩ := omitted_root_density_sublinear_far hRH hδ
  obtain ⟨D, hD, htriv⟩ := trivial_response_signed_sublinear hRH δ hδ
  obtain ⟨K, hK, hnear⟩ := omitted_centered_near_moebius_bound hRH (zero_le_one.trans hL)
  obtain ⟨A, hA, hlogA⟩ := eventually_logarithmic_order_le (C := K) hδ
  let M := max (2*D) (max A F)
  refine ⟨M, hA.trans ((le_max_left _ F).trans (le_max_right _ _)), fun m hm u hu => ?_⟩
  have hmA : A ≤ m := (le_max_left A F).trans ((le_max_right _ _).trans hm)
  have hmF : F ≤ m := (le_max_right A F).trans ((le_max_right _ _).trans hm)
  have hmD : 2*D ≤ m := (le_max_left _ _).trans hm
  have hm₂ : 2 ≤ m := hA.trans hmA
  have hm₀ : D ≤ m := by omega
  have hmm : D ≤ m/2 := by omega
  let S := Finset.Icc 2 m
  let T := S.filter (fun n => m+1 ≤ 2*n)
  let p := max 2 ((m+2)/2)
  let W := Real.exp (-(orderRate m)*u)
  let f (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - rootDensity (n : ℝ) u)
  let g (n : ℕ) := -(μ n : ℝ) * rootDensity (n : ℝ) u
  let h (n : ℕ) := -(μ n : ℝ) * centered (n : ℝ) (Real.exp u)
  have hEW : Real.exp (-u/2) ≤ W := exp_half_le_order m hu
  have hW : 0 ≤ W := Real.exp_nonneg _
  have htriv' (k : ℕ) (hk : D ≤ k) (hkm : k ≤ m) :
      |∑ n ∈ Finset.Icc 2 k, f n| ≤ δ * (m : ℝ) * W := by
    apply (htriv k hk u hu).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by exact_mod_cast hkm) hδ.le)
      hEW (Real.exp_nonneg _) (by positivity)
  have hcombine : δ * (m : ℝ) * W + δ * (m : ℝ) * W = ε * (m : ℝ) * W := by
    dsimp [δ]
    ring
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
    have hz : |∑ n ∈ T, g n| ≤ δ * (m : ℝ) * W := by
      refine (abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum ?_).trans (hF m hmF u huL))
      intro n hn
      unfold g
      rw [abs_mul, abs_neg]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (by exact_mod_cast abs_moebius_le_one (n := n))
    change |∑ n ∈ S, _| ≤ _
    rw [he]
    exact ((abs_add_le _ _).trans (add_le_add (htriv' m hm₀ le_rfl) hz)).trans_eq hcombine
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
    have hh := hnear m p u hp₂ hpm hhalf hu (le_of_not_ge huL)
    have hh' : |∑ n ∈ T, h n| ≤ K * ((m : ℝ) / Real.log m) * Real.exp (-u/2) := by
      rw [hTp]
      simpa only [h, centered, neg_mul, Finset.sum_neg_distrib, abs_neg] using hh
    have hz : |∑ n ∈ T, h n| ≤ δ * (m : ℝ) * W :=
      hh'.trans (mul_le_mul (hlogA m hmA) hEW (Real.exp_nonneg _) (by positivity))
    change |∑ n ∈ S, _| ≤ _
    rw [he]
    exact ((abs_add_le _ _).trans (add_le_add
      (htriv' (m/2) hmm (Nat.div_le_self _ _)) hz)).trans_eq hcombine

private theorem all_orders_density_sublinear (hRH : RiemannHypothesis)
    (centeredBound : ∀ ε > (0 : ℝ), ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ u : ℝ, 0 ≤ u →
      |∑ n ∈ Finset.Icc 2 m,
        -(μ n : ℝ) * (centered (n : ℝ) (Real.exp u) - capturedSpectrum m n u)| ≤
        ε * (m : ℝ) * Real.exp (-(orderRate m)*u)) :
    ∀ ε > (0 : ℝ), ∃ M : ℕ, 2 ≤ M ∧ ∀ m ≥ M, ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        ε * (m : ℝ) * Real.exp (-(orderRate m)*u) := by
  intro ε hε
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨A, hA, htail⟩ := normalized_mobius_tail_one_log hRH
  obtain ⟨P, hP, hlogP⟩ := eventually_logarithmic_order_le (C := A) hδ
  obtain ⟨Q₀, hQ₀, hsum'⟩ := centeredBound δ hδ
  let C := |Real.log (2 * Real.pi)|
  obtain ⟨J, hJ⟩ := exists_nat_ge (C/δ)
  refine ⟨max P (max Q₀ J), hP.trans (le_max_left _ _), fun m hm u hu => ?_⟩
  have hmP : P ≤ m := (le_max_left _ _).trans hm
  have hmQ : Q₀ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hmJ : J ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hm₂ : 2 ≤ m := hP.trans hmP
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
  have hm₂' : (2 : ℝ) ≤ m := by exact_mod_cast hm₂
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hlog_le : Real.log (m : ℝ) ≤ Real.log ((m : ℝ)+1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hR : |R| ≤ δ * (m : ℝ) * W := by
    apply (htail m hm₂ u hx).trans
    apply mul_le_mul_of_nonneg_right _ hW
    apply le_trans _ (hlogP m hmP)
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (Nat.cast_nonneg m) hlog hlog_le) hA.le
  have hE : |E| ≤ δ * (m : ℝ) * W := by
    have hbound := (RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le hu0).le
    have hmain : C ≤ δ * (m : ℝ) := by
      have hleft := hJ.trans (show (J : ℝ) ≤ m by exact_mod_cast hmJ)
      linarith only [(div_le_iff₀ hδ).mp hleft]
    refine hbound.trans ?_
    rw [mul_comm (Real.exp _)]
    exact mul_le_mul ((le_abs_self _).trans hmain) (exp_half_le_order m hu0)
      (Real.exp_nonneg _) (by positivity)
  have hsum : |∑ n ∈ Finset.Icc 2 m, e n| ≤ δ * (m : ℝ) * W :=
    hsum' m hmQ u hu0
  rw [show rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2) =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E from mobius_window_density_split m u]
  calc
    _ ≤ |R| + |∑ n ∈ Finset.Icc 2 m, e n| + |E| := by
      simpa only [abs_neg] using (abs_add_le (-R + ∑ n ∈ Finset.Icc 2 m, e n) E).trans
        (add_le_add (abs_add_le (-R) (∑ n ∈ Finset.Icc 2 m, e n)) (le_refl |E|))
    _ ≤ δ * (m : ℝ) * W + δ * (m : ℝ) * W + δ * (m : ℝ) * W :=
      add_le_add (add_le_add hR hsum) hE
    _ = _ := by dsimp [δ, W]; ring

/-- Transfer the uniform sublinear density estimate to the signed prime-only window. -/
theorem prime_window_mobius_sublinear_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ : ℝ, 2 ≤ a₀ ∧ ∀ ε > (0 : ℝ), ∃ M : ℕ, 2 ≤ M ∧
      ∀ m ≥ M, ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        ε * (m : ℝ) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨a₀, ha₀, hwindow⟩ := prime_window_threshold_of_rh hRH
  refine ⟨a₀, ha₀, fun ε hε => ?_⟩
  obtain ⟨M, hM, hD⟩ := all_orders_density_sublinear hRH (centered_sum_sublinear hRH)
    (ε/6) (by positivity)
  refine ⟨M, hM, fun m hm a B ha hAB => ?_⟩
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 m) {a B : ℝ} (ha : 2 ≤ a) (hab : a ≤ B) := by
    have ha₀ : 0 < a := by linarith
    exact retainedDensity_integral (m := m) (Finset.mem_Icc.mp hn).1 ha₀ (ha₀.trans_le hab)
  have h := hwindow m (hM.trans hm) retainedDensity
    (fun n hn a B ha hab => by
      simpa only [arithmeticPrimitive, capturedPrimitive, powerGap, arithmeticRate, neg_sub]
        using hterm n hn ha hab)
    ((ε/6)*(m : ℝ)) (hD m hm) a B ha hAB
  convert h using 1
  ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
