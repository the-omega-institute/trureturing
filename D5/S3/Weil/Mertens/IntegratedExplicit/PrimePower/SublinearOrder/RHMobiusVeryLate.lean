/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusVeryLate
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusVeryLate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed RH prime window past the logarithmic square-root spacing regime. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.LateArithmeticTail

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
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (spectralPrimitive windowDiscrepancy)

-- Combine the weighted omitted degrees with the arithmetic tail and trivial-root decay.
private theorem window_density_of_very_late (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ), 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      ((m : ℝ)+1)^(3/2 : ℝ) ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
      K * (1+Real.log ((m : ℝ)+1))^2 * (1+((m : ℝ)+1)^2/u) *
        Real.exp (-(orderRate m)*u) := by
  obtain ⟨A, hA, htail⟩ := normalized_mobius_tail_of_very_late
  obtain ⟨G, hG, hroot⟩ := root_density_log_sq hRH
  let C := |Real.log (2*Real.pi)|
  let J := |trivialConstant|
  have hC : 0 ≤ C := abs_nonneg _
  have hJ : 0 ≤ J := abs_nonneg _
  refine ⟨A+G+8*J+C, by linarith, fun m hm u hu hlate => ?_⟩
  let q := m+1
  let p := (q+1)/2
  let x := Real.exp u
  let W := Real.exp (-(orderRate m)*u)
  let L := 1+Real.log (q : ℝ)
  let V := 1+(q : ℝ)^2/u
  let T (n : ℕ) := Real.sqrt x * (∫ t in Ioi x, psi (t ^ (n : ℝ)⁻¹) / t ^ 2)
  let e (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) x - capturedSpectrum m n u)
  let f (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) x - rootDensity (n : ℝ) u)
  let R := Real.sqrt x * (primeTail x - Q x) - ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n
  let E := RHSharpActualEnvelope.G u - Real.exp (-u/2) * (actualH u).re
  have hq' : (q : ℝ) = (m : ℝ)+1 := by simp [q]
  have hq : 0 < q := Nat.succ_pos _
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 := zero_lt_one.trans_le hq₁
  have hu0 : 0 < u := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hu
  have hx : 2 ≤ x := by
    simpa only [x, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hu
  have hW : 0 ≤ W := Real.exp_nonneg _
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Real.log_nonneg hq₁]
  have hL₀ := zero_le_one.trans hL
  have hV : 1 ≤ V := by dsimp only [V]; linarith [div_nonneg (sq_nonneg (q : ℝ)) hu0.le]
  have hV₀ := zero_le_one.trans hV
  have hLS : L ≤ L^2 := by nlinarith only [mul_le_mul_of_nonneg_left hL hL₀]
  have hL₂ : 1 ≤ L^2 := hL.trans hLS
  have hR : |R| ≤ A*V*W := by
    simpa only [V, W, R, q, Nat.cast_add, Nat.cast_one] using htail m hm u hx hlate
  have hE : |E| ≤ C*W := by
    refine (RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le hu0.le).le.trans ?_
    rw [mul_comm (Real.exp _)]
    have hw : Real.exp (-u/2) ≤ W := by
      apply Real.exp_le_exp.mpr
      dsimp [W, orderRate]
      nlinarith only [mul_nonneg (inv_nonneg.mpr (show 0 ≤ (m : ℝ)+1 by positivity)) hu0.le]
    exact mul_le_mul (le_abs_self _) hw (Real.exp_nonneg _) hC
  have hT : (q : ℝ)*Real.exp (-u/2) ≤ 8*W := by
    have hdamp : (q : ℝ)*Real.exp (-u/(2*(q : ℝ))) ≤ 8 :=
      degree_mul_exp_neg_le_eight hq0 (by simpa only [hq'] using hlate)
    have hslack : Real.exp (-u/(q : ℝ)) ≤ Real.exp (-u/(2*(q : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have ht := div_le_div_of_nonneg_left hu0.le hq0 (show (q : ℝ) ≤ 2*q by linarith)
      linarith only [show -u/(q : ℝ) = -(u/(q : ℝ)) by ring,
        show -u/(2*(q : ℝ)) = -(u/(2*(q : ℝ))) by ring, ht]
    have heq : Real.exp (-u/2) = Real.exp (-u/(q : ℝ))*W := by
      dsimp only [W, orderRate]
      rw [← Real.exp_add, hq']
      congr 1
      ring
    rw [heq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hslack hq0.le).trans hdamp) hW
  have htriv : |∑ n ∈ Finset.Icc 2 m, f n| ≤ 8*J*L*W := by
    have hn (n : ℕ) (hnm : n ∈ Finset.Icc 2 m) :
        |f n| ≤ (J*L)*Real.exp (-u/2) := by
      obtain ⟨hn₂, hnm⟩ := Finset.mem_Icc.mp hnm
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hnq : (n : ℝ) ≤ q := by exact_mod_cast hnm.trans (Nat.le_add_right m 1)
      have hln : 1 + Real.log (n : ℝ) ≤ L := by
        exact add_le_add le_rfl (Real.log_le_log hn0 hnq)
      have hnlog : 0 ≤ 1+Real.log (n : ℝ) := by
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega))]
      have h := root_centered_log_bound hn₂ (v := u/(n : ℝ)) (by positivity)
      rw [show (n : ℝ)*(u/(n : ℝ)) = u by field_simp] at h
      have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
      dsimp only [f, x]
      rw [abs_mul, abs_neg]
      refine (mul_le_of_le_one_left (abs_nonneg _) hμ).trans (h.trans ?_)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul (le_abs_self _) hln hnlog hJ
    have hcard : ((Finset.Icc 2 m).card : ℝ) ≤ q := by
      exact_mod_cast (show (Finset.Icc 2 m).card ≤ q by rw [Nat.card_Icc]; dsimp [q]; omega)
    calc
      _ ≤ ∑ n ∈ Finset.Icc 2 m, |f n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Icc 2 m, (J*L)*Real.exp (-u/2) := Finset.sum_le_sum hn
      _ = ((Finset.Icc 2 m).card : ℝ) * ((J*L)*Real.exp (-u/2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q : ℝ)*((J*L)*Real.exp (-u/2)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (J*L)*((q : ℝ)*Real.exp (-u/2)) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hT (by positivity)).trans_eq (by ring)
  let S := (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n)
  let w (n : ℕ) := Real.exp (-(2*u/(q : ℝ)-u/(n : ℝ))/2)
  have hp : 0 < p := by dsimp [p, q]; omega
  have hpq : p ≤ q := by dsimp [p, q]; omega
  have hhalf : q ≤ 2*p := by dsimp [p, q]; omega
  have hSub : S ⊆ Finset.Icc p q := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    simp only [Finset.mem_Icc, p, q]
    omega
  have hspec : |∑ n ∈ S, -(μ n : ℝ)*rootDensity n u| ≤ G*L^2*V*W := by
    calc
      _ ≤ ∑ n ∈ S, |-(μ n : ℝ)*rootDensity n u| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ S, (G*L^2*W)*w n := by
        apply Finset.sum_le_sum
        intro n hn
        have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
        have hn0 : (0 : ℝ) < n := by linarith
        have hnq : (n : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp (hSub hn)).2
        have hln : 1 + Real.log (n : ℝ) ≤ L :=
          add_le_add le_rfl (Real.log_le_log hn0 hnq)
        have hln₀ : 0 ≤ 1+Real.log (n : ℝ) := by
          linarith [Real.log_nonneg (show (1 : ℝ) ≤ n by linarith)]
        have heq : Real.exp (((2*(n : ℝ))⁻¹-1/2)*u) = W*w n := by
          dsimp only [W, w, orderRate]
          rw [← Real.exp_add, ← hq']
          congr 1
          field_simp
          ring
        have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
        rw [abs_mul, abs_neg]
        refine (mul_le_of_le_one_left (abs_nonneg _) hμ).trans ((hroot n hn₂ u).trans ?_)
        rw [heq]
        calc
          _ = G*(1+Real.log (n : ℝ))^2*(W*w n) := by ring
          _ ≤ G*L^2*(W*w n) := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hln₀ hln _) hG.le) (by positivity)
          _ = _ := by ring
      _ = (G*L^2*W)*(∑ n ∈ S, w n) := by rw [Finset.mul_sum]
      _ ≤ (G*L^2*W)*V := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum_of_subset_of_nonneg hSub (fun n _ _ => Real.exp_nonneg _)).trans
          (weighted_omitted_degree_sum_le hp hpq hhalf hu0)) (by positivity)
      _ = _ := by ring
  have he : (∑ n ∈ Finset.Icc 2 m, e n) = (∑ n ∈ Finset.Icc 2 m, f n) +
      ∑ n ∈ S, -(μ n : ℝ)*rootDensity n u := by
    dsimp only [S]
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    unfold e capturedSpectrum f
    by_cases hcut : 2*n < m+1
    · simp [hcut, not_le_of_gt hcut]
    · rw [ite_eq_right hcut, ite_eq_left (le_of_not_gt hcut)]
      ring
  have hsum := (abs_add_le _ _).trans (add_le_add htriv hspec)
  rw [← he] at hsum
  rw [show rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2) =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E from mobius_window_density_split m u]
  rw [← hq']
  have hLV : 1 ≤ L^2*V := by nlinarith only [mul_le_mul_of_nonneg_right hL₂ hV₀, hV]
  have hLLV : L ≤ L^2*V := hLS.trans (le_mul_of_one_le_right (sq_nonneg _) hV)
  calc
    _ ≤ |R| + |∑ n ∈ Finset.Icc 2 m, e n| + |E| := by
      simpa only [abs_neg] using (abs_add_le (-R + ∑ n ∈ Finset.Icc 2 m, e n) E).trans
        (add_le_add (abs_add_le (-R) (∑ n ∈ Finset.Icc 2 m, e n)) (le_refl |E|))
    _ ≤ A*V*W + (8*J*L*W + G*L^2*V*W) + C*W := add_le_add (add_le_add hR hsum) hE
    _ ≤ A*L^2*V*W + (8*J*L^2*V*W + G*L^2*V*W) + C*L^2*V*W := by
      have ha : A*V*W ≤ A*L^2*V*W := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hA.le hL₂) hV₀) hW
      have ht : 8*J*L*W ≤ 8*J*L^2*V*W := by
        have hh := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLLV (show 0 ≤ 8*J by positivity)) hW
        exact hh.trans_eq (by ring)
      have hc : C*W ≤ C*L^2*V*W := by
        have hh := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hLV) hW
        exact hh.trans_eq (by ring)
      exact add_le_add (add_le_add ha (add_le_add ht le_rfl)) hc
    _ = _ := by dsimp only [L, V, W]; ring

/-- At later starts the geometric degree budget gives the exponent (1-d+ε). -/
theorem prime_window_mobius_very_late_of_rh (hRH : RiemannHypothesis)
    {d ε : ℝ} (hd : 1/2 ≤ d) (hdone : d ≤ 1) (hε : 0 < ε) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧
      ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      ((m : ℝ)+1)^(1+d) ≤ Real.log a →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * (m : ℝ)^(1-d+ε) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  let η := min (ε/4) (1/4)
  let κ := 1-d+2*η
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηone : η ≤ 1/4 := min_le_right _ _
  have hηε : η ≤ ε/4 := min_le_left _ _
  have hκ : 0 ≤ κ := by dsimp [κ]; linarith
  have hκ₁ : κ ≤ 1 := by dsimp [κ]; linarith
  have hκε : κ ≤ 1-d+ε := by dsimp [κ]; linarith
  obtain ⟨D, hD, hdensity⟩ := window_density_of_very_late hRH
  obtain ⟨a₀, ha₀, hwindow⟩ := prime_window_threshold_of_local_density hRH
  let C := 2*D*(1+η⁻¹)^2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨a₀, 12*C, ha₀, by positivity, fun m hm a B ha hAB hlate => ?_⟩
  let q : ℝ := (m : ℝ)+1
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hq0 := zero_lt_one.trans_le hq
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (ha₀.trans ha)
  have hbudget (u : ℝ) (hu : q^(1+d) ≤ u) :
      D*(1+Real.log q)^2*(1+q^2/u) ≤ C*q^κ := by
    have hlogq := Real.log_le_rpow_div hq0.le hη
    have hlog' : 1+Real.log q ≤ (1+η⁻¹)*q^η := by
      have hqη := Real.one_le_rpow hq hη.le
      rw [div_eq_mul_inv] at hlogq
      linarith only [hlogq, hqη,
        show (1+η⁻¹)*q^η = q^η+q^η*η⁻¹ by ring]
    have hs : (1+Real.log q)^2 ≤ (1+η⁻¹)^2*q^(2*η) := by
      have hn : 0 ≤ 1+Real.log q := by linarith [Real.log_nonneg hq]
      refine (pow_le_pow_left₀ hn hlog' 2).trans_eq ?_
      rw [mul_pow, ← Real.rpow_mul_natCast hq0.le]
      congr 2
      push_cast
      ring
    have hquot : q^2/u ≤ q^(1-d) := by
      have hqp := Real.rpow_pos_of_pos hq0 (1+d)
      refine (div_le_div_of_nonneg_left (sq_nonneg q) hqp hu).trans_eq ?_
      rw [← Real.rpow_natCast, ← Real.rpow_sub hq0]
      congr 1
      push_cast
      ring
    have hS : 1+q^2/u ≤ 2*q^(1-d) :=
      by linarith only [hquot, Real.one_le_rpow hq (sub_nonneg.mpr hdone)]
    calc
      _ ≤ (D*((1+η⁻¹)^2*q^(2*η)))*(2*q^(1-d)) := by
        have hu0 := (Real.rpow_pos_of_pos hq0 _).trans_le hu
        exact mul_le_mul (mul_le_mul_of_nonneg_left hs hD.le) hS (by positivity) (by positivity)
      _ = C*(q^(2*η)*q^(1-d)) := by dsimp only [C]; ring
      _ = _ := by
        rw [← Real.rpow_add hq0]
        congr 2
        dsimp only [κ]
        ring
  have hDens (u : ℝ) (hu : u ∈ Set.Icc (Real.log a) (Real.log B)) :
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        (C*q^κ)*Real.exp (-(orderRate m)*u) := by
    have hu' : q^(1+d) ≤ u := hlate.trans hu.1
    have hfar := (Real.rpow_le_rpow_of_exponent_le hq (show (3/2 : ℝ) ≤ 1+d by linarith)).trans hu'
    exact (hdensity m hm u (hlog.trans hu.1) hfar).trans
      (mul_le_mul_of_nonneg_right (hbudget u hu') (Real.exp_nonneg _))
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 m) {a B : ℝ} (ha : 2 ≤ a) (hab : a ≤ B) := by
    have ha₀ : 0 < a := by linarith
    exact retainedDensity_integral (m := m) (Finset.mem_Icc.mp hn).1 ha₀ (ha₀.trans_le hab)
  have h := hwindow m hm retainedDensity
    (fun n hn a B ha hab => by
      simpa only [arithmeticPrimitive, capturedPrimitive, powerGap, arithmeticRate, neg_sub]
        using hterm n hn ha hab)
    a B ha hAB (C*q^κ) hDens
  have hpower : q^κ ≤ 2*(m : ℝ)^κ := by
    refine (Real.rpow_le_rpow (by positivity) (show q ≤ 2*(m : ℝ) by dsimp [q]; linarith)
      hκ).trans ?_
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hκ₁
  have ha' : 0 < a := by linarith
  have hgap : 0 ≤ a ^ ((m + 1 : ℝ)⁻¹ - 1/2) - B ^ ((m + 1 : ℝ)⁻¹ - 1/2) := by
    apply sub_nonneg.mpr
    apply Real.rpow_le_rpow_of_nonpos ha' hAB
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ m+1 by linarith)
    norm_num at hi
    linarith
  have hcoef : 6*(C*q^κ) ≤ (12*C)*(m : ℝ)^κ := by
    calc
      _ = (6*C)*q^κ := by ring
      _ ≤ (6*C)*(2*(m : ℝ)^κ) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = _ := by ring
  refine (h.trans (mul_le_mul_of_nonneg_right hcoef hgap)).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hκε) (by positivity)) hgap

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
