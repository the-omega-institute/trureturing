/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusThreeQuarters
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusThreeQuarters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A three-quarter power bound for the signed RH prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.PowerWindowDensity
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.OmittedPrefixSpectrum
import D5.S3.Weil.ZetaPntBounds.MobiusShortAverage

/-! The signed degree prefix improves the low spectral cost at the square-root cutoff. -/

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

private theorem square_root_cutoff_budget {q η : ℝ} (hq : 1 ≤ q)
    (hη : 0 < η) (hηhalf : η < 1/2) :
    let H := ⌊q^(1/2 : ℝ)⌋₊
    0 < H ∧
      q^(1/2+η) * ((H : ℝ)+1)^(1/2+η) ≤ 2*q^(3/4+2*η) ∧
      ((H : ℝ)+1)^(1+η) ≤ 4*q^(3/4+2*η) ∧
      q*(H : ℝ)^(η-1/2) ≤ 2*q^(3/4+2*η) := by
  let Y := q^(1/2 : ℝ)
  let H := ⌊Y⌋₊
  have hq₀ := zero_lt_one.trans_le hq
  have hY : 1 ≤ Y := Real.one_le_rpow hq (by norm_num)
  have hY₀ := zero_lt_one.trans_le hY
  have hH₁ : 1 ≤ H := (Nat.le_floor_iff hY₀.le).2 (by simpa using hY)
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hH₁
  have hHY : (H : ℝ) ≤ Y := Nat.floor_le hY₀.le
  have hYH : Y < (H : ℝ)+1 := Nat.lt_floor_add_one _
  have hu : (H : ℝ)+1 ≤ 2*Y := by linarith
  have hl : (1/2 : ℝ)*Y ≤ (H : ℝ) := by linarith
  have hup (c j : ℝ) (hc : 0 ≤ c) (hj : (2 : ℝ)^c ≤ j) :
      ((H : ℝ)+1)^c ≤ j*q^((1/2)*c) := by
    refine (Real.rpow_le_rpow (by positivity) hu hc).trans ?_
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
  refine ⟨hH₁, ?_, ?_, ?_⟩
  · calc
      _ ≤ q^(1/2+η)*(2*q^((1/2)*(1/2+η))) :=
        mul_le_mul_of_nonneg_left (hup _ _ (by linarith) htwo) (by positivity)
      _ = 2*(q^(1/2+η)*q^((1/2)*(1/2+η))) := by ring
      _ = 2*q^((1/2+η)+(1/2)*(1/2+η)) := by rw [← Real.rpow_add hq₀]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq (by linarith)) (by norm_num)
  · exact (hup _ _ (by linarith) hfour).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq (by linarith)) (by norm_num))
  · have hb : (H : ℝ)^(η-1/2) ≤ 2*q^((1/2)*(η-1/2)) := by
      refine (Real.rpow_le_rpow_of_nonpos (by positivity) hl (by linarith)).trans ?_
      rw [Real.mul_rpow (by norm_num) hY₀.le]
      dsimp [Y]
      rw [← Real.rpow_mul hq₀.le]
      exact mul_le_mul_of_nonneg_right hneg (by positivity)
    calc
      _ ≤ q*(2*q^((1/2)*(η-1/2))) := mul_le_mul_of_nonneg_left hb hq₀.le
      _ = 2*q^(1+(1/2)*(η-1/2)) := by rw [Real.rpow_add hq₀, Real.rpow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq (by linarith)) (by norm_num)

/-- Under RH the signed prime-window residual has order exponent at most three quarters plus
any positive slack, including coincident real endpoints. -/
theorem prime_window_mobius_three_quarters_of_rh (hRH : RiemannHypothesis)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧
      ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * (m : ℝ)^(3/4+ε : ℝ) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  let η := min (ε/3) (1/12)
  let β := 1/2+η
  let κ := 3/4+2*η
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηupper : η ≤ 1/12 := min_le_right _ _
  have hηε : η ≤ ε/3 := min_le_left _ _
  have hηhalf : η < 1/2 := by linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hβ₁ : β ≤ 1 := by dsimp [β]; linarith
  have hβκ : β < κ := by dsimp [β, κ]; linarith
  have hκ : 0 ≤ κ := hβ.trans hβκ.le
  have hκ₁ : κ ≤ 1 := by dsimp [κ]; linarith
  have hκeps : κ ≤ 3/4+ε := by dsimp [κ]; linarith
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
  obtain ⟨F, hF, hsplit⟩ := signed_omitted_root_density_of_damped_prefix hRH hη hηhalf
  have hfar (m : ℕ) (hm : 2 ≤ m) (u : ℝ) (hu : (m : ℝ)+1 ≤ u) :
      |∑ n ∈ (Finset.Icc 2 m).filter (fun n => m+1 ≤ 2*n),
        -(μ n : ℝ) * rootDensity n u| ≤
        (F*(2*P+6)) * (((m : ℝ)+1)^κ) * Real.exp (-(orderRate m)*u) := by
    let q := (m : ℝ)+1
    have hq : 1 ≤ q := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) m]
    let H := ⌊q^(1/2 : ℝ)⌋₊
    obtain ⟨hH, hl, hc, hh⟩ := square_root_cutoff_budget hq hη hηhalf
    have hb := hsplit m H hm hH u hu (P*q^β)
      (range_moebius_prefix_of_Ioc_power_bound hβ hP.le hpre m)
    refine hb.trans ?_
    have hlow : P*q^β * ((H : ℝ)+1)^(1/2+η) ≤ P*(2*q^κ) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hl hP.le
    have hcost : F*(P*q^β * ((H : ℝ)+1)^(1/2+η) + ((H : ℝ)+1)^(1+η) +
        q*(H : ℝ)^(η-1/2)) ≤ F*(2*P+6)*q^κ := by
      exact (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hlow hc) hh) hF.le).trans_eq
        (by ring)
    rw [mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_right hcost (Real.exp_nonneg _)
  obtain ⟨a₀, ha₀, hwindow⟩ := prime_window_threshold_of_rh hRH
  obtain ⟨D, hD, hDens⟩ := window_density_of_power_prefix hRH hβ hβ₁ hβκ hP
    (show 0 < F*(2*P+6) by positivity) hpre hfar
  refine ⟨a₀, 12*D, ha₀, by positivity, fun m hm a B ha hAB => ?_⟩
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 m) {a B : ℝ} (ha : 2 ≤ a) (hab : a ≤ B) := by
    have ha₀ : 0 < a := by linarith
    exact retainedDensity_integral (m := m) (Finset.mem_Icc.mp hn).1 ha₀ (ha₀.trans_le hab)
  have h := hwindow m hm retainedDensity
    (fun n hn a B ha hab => by
      simpa only [arithmeticPrimitive, capturedPrimitive, powerGap, arithmeticRate, neg_sub]
        using hterm n hn ha hab)
    (D * ((m : ℝ)+1)^κ) (hDens m hm) a B ha hAB
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
