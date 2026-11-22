/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusLateSpacing
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusLateSpacing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A window-dependent exponent for the signed RH prime residual. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.PowerWindowDensity
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.OmittedPrefixSpectrum
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.LateWindowSpectrum
import D5.S3.Weil.ZetaPntBounds.MobiusShortAverage

/-! Exact spectral spacing improves the exponent on late logarithmic windows. -/

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

private theorem late_cutoff_budget {q d η u : ℝ} (hq : 1 ≤ q)
    (hd : 0 ≤ d) (hd₁ : d ≤ 1/2) (hη : 0 < η) (hηhalf : η < 1/2)
    (hu : q^(1+d) ≤ u) :
    let H := ⌊q^(1/2-d)⌋₊
    let κ := 3/4-d/2+2*η
    0 < H ∧
      q^(1/2+η) * ((H : ℝ)+1)^(1/2+η) ≤ 2*q^κ ∧
      ((H : ℝ)+1)^(1+η) ≤ 4*q^κ ∧
      (1+q^2/u)*(H : ℝ)^(η-1/2) ≤ 4*q^κ ∧ q^(1/2+η) ≤ q^κ := by
  let cutoffExponent := 1/2-d
  let κ := 3/4-d/2+2*η
  let Y := q^cutoffExponent
  let H := ⌊Y⌋₊
  have hcutoffExponent : 0 ≤ cutoffExponent := by dsimp [cutoffExponent]; linarith
  have hcutoffExponent₁ : cutoffExponent ≤ 1/2 := by dsimp [cutoffExponent]; linarith
  have hq₀ := zero_lt_one.trans_le hq
  have hY : 1 ≤ Y := Real.one_le_rpow hq hcutoffExponent
  have hY₀ := zero_lt_one.trans_le hY
  have hH₁ : 1 ≤ H := (Nat.le_floor_iff hY₀.le).2 (by simpa using hY)
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hH₁
  have hHY : (H : ℝ) ≤ Y := Nat.floor_le hY₀.le
  have hYH : Y < (H : ℝ)+1 := Nat.lt_floor_add_one _
  have htop : (H : ℝ)+1 ≤ 2*Y := by linarith
  have hbottom : (1/2 : ℝ)*Y ≤ (H : ℝ) := by linarith
  have hup (c j : ℝ) (hc : 0 ≤ c) (hj : (2 : ℝ)^c ≤ j) :
      ((H : ℝ)+1)^c ≤ j*q^(cutoffExponent*c) := by
    refine (Real.rpow_le_rpow (by positivity) htop hc).trans ?_
    rw [Real.mul_rpow (by norm_num) hY₀.le]
    dsimp [Y]
    rw [← Real.rpow_mul hq₀.le]
    exact mul_le_mul_of_nonneg_right hj (by positivity)
  have htwo : (2 : ℝ)^(1/2+η) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (show 1/2+η ≤ (1 : ℝ) by linarith)
  have hfour : (2 : ℝ)^(1+η) ≤ 4 := by
    have ht : (2 : ℝ)^(2 : ℝ) = 4 := by norm_num [Real.rpow_two]
    rw [← ht]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hneg : (1/2 : ℝ)^(η-1/2) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_ge (x := (1/2 : ℝ)) (by norm_num)
      (by norm_num) (show (-1 : ℝ) ≤ η-1/2 by linarith)
    simpa [Real.rpow_neg_one] using h
  have hηcutoffExponent : cutoffExponent*η ≤ η/2 := by
    linarith only [mul_le_mul_of_nonneg_right hcutoffExponent₁ hη.le]
  have hshape : cutoffExponent/2 = 1/4-d/2 := by dsimp [cutoffExponent]; ring
  have hspacing : 1+q^2/u ≤ 2*q^(1-d) := by
    have hqp : 0 < q^(1+d) := Real.rpow_pos_of_pos hq₀ _
    have hquot : q^2/u ≤ q^(1-d) := by
      refine (div_le_div_of_nonneg_left (sq_nonneg q) hqp hu).trans_eq ?_
      rw [← Real.rpow_natCast, ← Real.rpow_sub hq₀]
      congr 1
      push_cast
      ring
    linarith only [hquot, Real.one_le_rpow hq (show 0 ≤ 1-d by linarith)]
  have hbound : (H : ℝ)^(η-1/2) ≤ 2*q^(cutoffExponent*(η-1/2)) := by
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) hbottom (by linarith)).trans ?_
    rw [Real.mul_rpow (by norm_num) hY₀.le]
    dsimp [Y]
    rw [← Real.rpow_mul hq₀.le]
    exact mul_le_mul_of_nonneg_right hneg (by positivity)
  change 0 < H ∧
    q^(1/2+η) * ((H : ℝ)+1)^(1/2+η) ≤ 2*q^κ ∧
    ((H : ℝ)+1)^(1+η) ≤ 4*q^κ ∧
    (1+q^2/u)*(H : ℝ)^(η-1/2) ≤ 4*q^κ ∧ q^(1/2+η) ≤ q^κ
  refine ⟨hH₁, ?_, ?_, ?_, Real.rpow_le_rpow_of_exponent_le hq ?_⟩
  · calc
      _ ≤ q^(1/2+η)*(2*q^(cutoffExponent*(1/2+η))) :=
        mul_le_mul_of_nonneg_left (hup _ _ (by linarith) htwo) (by positivity)
      _ = 2*q^(1/2+η+cutoffExponent*(1/2+η)) := by
        rw [Real.rpow_add hq₀ (1/2+η) (cutoffExponent*(1/2+η))]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq (by dsimp [κ]; nlinarith)) (by norm_num)
  · refine (hup _ _ (by linarith) hfour).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq ?_) (by norm_num))
    dsimp [κ]
    have he : cutoffExponent = 1/2-d := rfl
    nlinarith
  · calc
      _ ≤ (2*q^(1-d))*(2*q^(cutoffExponent*(η-1/2))) := mul_le_mul hspacing hbound (by positivity)
        (by positivity)
      _ = 4*q^(1-d+cutoffExponent*(η-1/2)) := by rw [Real.rpow_add hq₀]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq (by dsimp [κ]; nlinarith)) (by norm_num)
  · dsimp [κ]
    linarith

private theorem late_density_with_spectral_bound {β κ P F : ℝ}
    (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (hβκ : β < κ) (hP : 0 < P) (hF : 0 < F)
    (hprefix : ∀ k : ℕ, 1 ≤ k → |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ P*(k : ℝ)^β) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      (|∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
        -(μ n : ℝ) * rootDensity n u| ≤ F * (((m : ℝ)+1)^κ) * Real.exp (-(orderRate m)*u)) →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * (((m : ℝ)+1)^κ) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨A, hA, htail⟩ := normalized_mobius_tail_of_power_prefix hβ hβ₁ hprefix
  let C := |Real.log (2*Real.pi)|
  let δ := κ-β
  have hδ : 0 < δ := sub_pos.mpr hβκ
  have hC : 0 ≤ C := abs_nonneg _
  let J := (P+1)*(1+δ⁻¹+C)
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  refine ⟨A+J+F+C, by linarith, fun m hm u hu hfar => ?_⟩
  let q := (m : ℝ)+1
  let W := Real.exp (-(orderRate m)*u)
  let x := Real.exp u
  let T (n : ℕ) := Real.sqrt x * (∫ t in Ioi x, psi (t ^ (n : ℝ)⁻¹) / t^2)
  let e (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) x - capturedSpectrum m n u)
  let f (n : ℕ) := -(μ n : ℝ) * (centered (n : ℝ) x - rootDensity (n : ℝ) u)
  let R := Real.sqrt x * (primeTail x - Q x) - ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * T n
  let E := RHSharpActualEnvelope.G u - Real.exp (-u/2) * (actualH u).re
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hq0 := zero_lt_one.trans_le hq
  have hx : 2 ≤ x := by
    have hexp := Real.exp_le_exp.mpr hu
    simpa only [x, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hexp
  have hu0 : 0 ≤ u := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hu
  have hW : 0 ≤ W := Real.exp_nonneg _
  have hpre (k : ℕ) (hk : k ≤ m) :
      |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ P*q^β := by
    by_cases h₁ : 1 ≤ k
    · apply (hprefix k h₁).trans
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
        ((show (k : ℝ) ≤ m by exact_mod_cast hk).trans (by dsimp [q]; linarith)) hβ) hP.le
    · have hzero : k = 0 := by omega
      subst k
      simpa using (show 0 ≤ P*q^β by positivity)
  have hR : |R| ≤ A*q^κ*W :=
    (htail m hm u hx).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq hβκ.le) hA.le) hW)
  have hpowers := Real.one_le_rpow hq (hβ.trans hβκ.le)
  have hE : |E| ≤ C*q^κ*W := by
    refine (RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le hu0).le.trans ?_
    rw [mul_comm (Real.exp _)]
    have hcoef : Real.log (2*Real.pi) ≤ C*q^κ :=
      (le_abs_self _).trans (le_mul_of_one_le_right hC hpowers)
    exact mul_le_mul hcoef (exp_half_le_order m hu0) (Real.exp_nonneg _) (by positivity)
  have htriv : |∑ n ∈ Finset.Icc 2 m, f n| ≤ J*q^κ*W := by
    have hlog : Real.log m ≤ δ⁻¹*q^δ :=
      (Real.log_le_log (by linarith : (0 : ℝ) < m)
        (show (m : ℝ) ≤ q from le_add_of_nonneg_right zero_le_one)).trans
        (by simpa only [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hq0.le hδ)
    have hleft : P*q^β+1 ≤ (P+1)*q^β := by
      linarith only [Real.one_le_rpow hq hβ]
    have hright : 1+Real.log (m : ℝ)+C ≤ (1+δ⁻¹+C)*q^δ := by
      have hb := Real.one_le_rpow hq hδ.le
      nlinarith only [hlog, hb, mul_le_mul_of_nonneg_left hb hC]
    have hcoef : (P*q^β+1)*(1+Real.log m+C) ≤ J*q^κ := by
      calc
        _ ≤ ((P+1)*q^β)*((1+δ⁻¹+C)*q^δ) :=
          mul_le_mul hleft hright (by positivity) (by positivity)
        _ = _ := by
          rw [show ((P+1)*q^β)*((1+δ⁻¹+C)*q^δ) = J*(q^β*q^δ) by dsimp [J]; ring,
            ← Real.rpow_add hq0]
          simp [δ]
    exact (trivial_response_of_mobius_prefix m hu0 hpre).trans
      (mul_le_mul hcoef (exp_half_le_order m hu0) (Real.exp_nonneg _) (by positivity))
  have hsum : |∑ n ∈ Finset.Icc 2 m, e n| ≤ J*q^κ*W + F*q^κ*W := by
    have he : (∑ n ∈ Finset.Icc 2 m, e n) = (∑ n ∈ Finset.Icc 2 m, f n) +
        ∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n), -(μ n : ℝ)*rootDensity n u := by
      rw [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      unfold e capturedSpectrum f
      by_cases hcut : 2*n < m+1
      · simp [hcut, not_le_of_gt hcut]
      · rw [ite_eq_right hcut, ite_eq_left (le_of_not_gt hcut)]
        ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add htriv hfar)
  rw [show rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2) =
      -R + (∑ n ∈ Finset.Icc 2 m, e n) + E from mobius_window_density_split m u]
  calc
    _ ≤ |R| + |∑ n ∈ Finset.Icc 2 m, e n| + |E| := by
      simpa only [abs_neg] using (abs_add_le (-R + ∑ n ∈ Finset.Icc 2 m, e n) E).trans
        (add_le_add (abs_add_le (-R) (∑ n ∈ Finset.Icc 2 m, e n)) (le_refl |E|))
    _ ≤ A*q^κ*W + (J*q^κ*W + F*q^κ*W) + C*q^κ*W := add_le_add (add_le_add hR hsum) hE
    _ = _ := by dsimp only [q, W]; ring

/-- Late logarithmic starting points improve the order exponent in the signed RH residual. -/
theorem prime_window_mobius_late_spacing_of_rh (hRH : RiemannHypothesis)
    {d ε : ℝ} (hd : 0 ≤ d) (hdhalf : d ≤ 1/2) (hε : 0 < ε) :
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
        K * (m : ℝ)^(3/4-d/2+ε) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  let η := min (ε/3) (1/12)
  let β := 1/2+η
  let κ := 3/4-d/2+2*η
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηupper : η ≤ 1/12 := min_le_right _ _
  have hηε : η ≤ ε/3 := min_le_left _ _
  have hηhalf : η < 1/2 := by linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hβ₁ : β ≤ 1 := by dsimp [β]; linarith
  have hβκ : β < κ := by dsimp [β, κ]; linarith
  have hκ : 0 ≤ κ := hβ.trans hβκ.le
  have hκ₁ : κ ≤ 1 := by dsimp [κ]; linarith
  have hκeps : κ ≤ 3/4-d/2+ε := by dsimp [κ]; linarith
  have hzero (z : ℂ) (hz : 1/2 < z.re) (hne : z ≠ 1) : riemannZeta z ≠ 0 := by
    intro hroot
    have htriv : ¬ ∃ n : ℕ, z = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      simp at hz
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (ne_of_gt hz) (hRH z hroot htriv hne)
  obtain ⟨P, hP, hprefix⟩ :=
    D5.S3.Weil.ZetaPntBounds.MobiusShortAverage.ordinary_mobius_prefix_of_zero_free
      (by norm_num) (by norm_num) hzero hη
  have hpre (k : ℕ) (hk : 1 ≤ k) :
      |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ P*(k : ℝ)^β := by
    have hset : Finset.Ioc 0 k = Finset.Icc 1 k := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    simpa only [hset, β] using hprefix k hk
  obtain ⟨L, hL, hlow⟩ := signed_low_occurrence_sum_of_damped_prefix hRH hη
  obtain ⟨U, hU, hhigh⟩ := masked_occurrence_tail_of_exact_spacing hRH hη hηhalf
  let F := L*(2*P+4)+5*U
  have hF : 0 < F := by dsimp [F]; positivity
  have hfar (m : ℕ) (hm : 2 ≤ m) (u : ℝ) (hu : ((m : ℝ)+1)^(1+d) ≤ u) :
      |∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
        -(μ n : ℝ) * rootDensity n u| ≤
        F * (((m : ℝ)+1)^κ) * Real.exp (-(orderRate m)*u) := by
    let q := m+1
    let p := (q+1)/2
    let a (n : ℕ) : ℂ := -((μ n : ℝ) : ℂ)
    have hq' : (q : ℝ) = (m : ℝ)+1 := by simp [q]
    have hqnat : 3 ≤ q := by dsimp [q]; omega
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hqu : (q : ℝ) ≤ u := by
      rw [← hq'] at hu
      have hp := Real.rpow_le_rpow_of_exponent_le hq (show (1 : ℝ) ≤ 1+d by linarith)
      rw [Real.rpow_one] at hp
      exact hp.trans hu
    have hu0 := (Nat.cast_nonneg q : (0 : ℝ) ≤ q).trans hqu
    let H := ⌊(q : ℝ)^(1/2-d)⌋₊
    obtain ⟨hH, hL₁, hL₂, hU₁, hU₂⟩ :=
      late_cutoff_budget (u := u) hq hd hdhalf hη hηhalf (by simpa only [hq'] using hu)
    have hp : q ≤ 2*p := by dsimp [p]; omega
    have ha₁ (n : ℕ) : ‖a n‖ ≤ 1 := by
      simp only [a, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    have haP (k : ℕ) (hk : k ≤ m+1) : ‖∑ n ∈ Finset.range k, a n‖ ≤ P*(q : ℝ)^β := by
      have h := range_moebius_prefix_of_Ioc_power_bound hβ hP.le hpre m k hk
      simpa only [a, Finset.sum_neg_distrib, ← Complex.ofReal_sum, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, hq'] using h
    have hl := hlow q p m H hqnat (Nat.le_add_right _ _) hp u hu0 a (P*(q : ℝ)^β) ha₁ haP
    have hh (T : Finset ℕ) := hhigh q H hqnat hH u hqu T
    have hb := signed_omitted_root_density_of_finite_bounds (H := H)
      hRH hm hu0 hl (fun T => by simpa only [mem_lowBins, not_le] using hh T)
    refine hb.trans ?_
    rw [mul_comm (Real.exp _), ← hq']
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    have hl' : P*(q : ℝ)^β * ((H : ℝ)+1)^(1/2+η) ≤ P*(2*(q : ℝ)^κ) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hL₁ hP.le
    exact (add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add hl' hL₂) hL.le)
      (mul_le_mul_of_nonneg_left (add_le_add hU₁ hU₂) hU.le)).trans_eq
        (by dsimp [F]; ring)
  obtain ⟨a₀, ha₀, hwindow⟩ := prime_window_threshold_of_local_density hRH
  obtain ⟨D, hD, hDens⟩ := late_density_with_spectral_bound hβ hβ₁ hβκ hP hF hpre
  refine ⟨a₀, 12*D, ha₀, by positivity, fun m hm a B ha hAB hlate => ?_⟩
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 m) {a B : ℝ} (ha : 2 ≤ a) (hab : a ≤ B) := by
    have ha₀ : 0 < a := by linarith
    exact retainedDensity_integral (m := m) (Finset.mem_Icc.mp hn).1 ha₀ (ha₀.trans_le hab)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (ha₀.trans ha)
  have h := hwindow m hm retainedDensity
    (fun n hn a B ha hab => by
      simpa only [arithmeticPrimitive, capturedPrimitive, powerGap, arithmeticRate, neg_sub]
        using hterm n hn ha hab)
    a B ha hAB (D * ((m : ℝ)+1)^κ)
    (fun u hu => hDens m hm u (hlog.trans hu.1) (hfar m hm u (hlate.trans hu.1)))
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpower : ((m : ℝ)+1)^κ ≤ 2*(m : ℝ)^κ := by
    refine (Real.rpow_le_rpow (by positivity) (show (m : ℝ)+1 ≤ 2*(m : ℝ) by linarith)
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
  have hcoef : 6*(D*((m : ℝ)+1)^κ) ≤ (12*D)*(m : ℝ)^κ := by
    calc
      _ = (6*D)*((m : ℝ)+1)^κ := by ring
      _ ≤ (6*D)*(2*(m : ℝ)^κ) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = _ := by ring
  refine (h.trans (mul_le_mul_of_nonneg_right hcoef hgap)).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hκeps) (by positivity)) hgap

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
