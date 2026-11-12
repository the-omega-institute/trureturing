/- GID: D5/S3/Arith/Robin/PriceRecord/ActualRecordSingleTwoTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualRecordSingleTwoTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform single-two-tail reduction for all positive-price original records. -/

import D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
import D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
import D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! The full original 2-tail at the integer's own logarithmic clock.
The strict profitable prefix excludes equality layers; the original tail includes
them with zero loss. The prescribed full bank, Robin/5040 and RH remain open. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualRecordSingleTwoTail

open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
  (beta gain powerSum powerSum_pos powerSum_succ powerSum_geometric beta_nat beta_pos)
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
  (normalized_gain_bounds)
open D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
  (FullRecord BHPMaximumGap BHPShortIntervalCount)
open D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
  (bhp_actual_five_mode_small_slack)

/- Quantitative separation for the ACTUAL marginal. We use the existing
beta_nat reconciliation rather than postulating a different spectrum.
For s = powerSum j 2 > 0, the next sum is exactly 2*s+2. -/
private theorem two_layer_halving {j : ℕ} (hj : 1 ≤ j) :
    2 * goldenLayerMarginal 2 (j + 1) < goldenLayerMarginal 2 j := by
  let s : ℝ := powerSum j 2
  have hs : 0 < s := powerSum_pos (by norm_num) hj
  have hnext : powerSum (j + 1) 2 = 2 * s + 2 := by
    have hg := powerSum_geometric j (2 : ℝ)
    rw [powerSum_succ, pow_succ]
    dsimp only [s] at *
    nlinarith only [hg]
  have hd : 0 < 2 * s + 2 := by linarith
  have hb : 0 < 1 + 1 / (2 * s + 2) := by positivity
  have hratio : (1 + 1 / (2 * s + 2)) ^ 2 < 1 + 1 / s := by
    have hleft : 1 + 1 / (2 * s + 2) = (2 * s + 3) / (2 * s + 2) := by
      field_simp [hd.ne'] <;> ring
    have hright : 1 + 1 / s = (s + 1) / s := by
      field_simp [hs.ne'] <;> ring
    rw [hleft, hright, div_pow]
    apply (div_lt_div_iff₀ (pow_pos hd 2) hs).mpr
    nlinarith [sq_nonneg s]
  have hlog : 2 * log (1 + 1 / (2 * s + 2)) < log (1 + 1 / s) := by
    have hh := log_lt_log (pow_pos hb 2) hratio
    simpa only [log_pow, Nat.cast_ofNat] using hh
  rw [← beta_nat (p := 2) (j := j + 1) Nat.prime_two (by omega),
    ← beta_nat (p := 2) (j := j) Nat.prime_two hj]
  change 2 * (log (1 + 1 / powerSum (j + 1) 2) / log 2) <
    log (1 + 1 / s) / log 2
  rw [hnext]
  calc
    2 * (log (1 + 1 / (2 * s + 2)) / log 2) =
        (2 * log (1 + 1 / (2 * s + 2))) / log 2 := by ring
    _ < _ := div_lt_div_of_pos_right hlog (log_pos (by norm_num))

private theorem marginal_antitone {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    goldenLayerMarginal 2 j ≤ goldenLayerMarginal 2 i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact (golden_layer_strict_decrease Nat.prime_two hi hlt).le

/- The filter and price here are arbitrary: mu may vary at every point.
Only the FIRST component of the full mass law's UnitRate is needed.
The unused second-order coefficient remains -sqrt(2)*log(2)/2, not zero.

The new actual-price limit comes from the literal factorization
 c / beta 1 P = ((T/P)*(log T/log P)*(gain 1 P*P))^(-1).
No referencePrice is identified with beta 1 P.
-/
private theorem record_clock_price_limits {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ x, 2 ≤ m x)
    (hmu : ∀ x, 0 < mu x) (hrecord : ∀ x, FullRecord (m x) (mu x))
    (hP : Tendsto (fun x => (largestPrime (m x) : ℝ)) l atTop) :
    Tendsto (fun x =>
      (1 / (log (m x : ℝ) * log (log (m x : ℝ)))) /
        beta 1 (largestPrime (m x) : ℝ)) l (𝓝 1) ∧
    Tendsto (fun x => log (log (m x : ℝ))) l atTop ∧
    Tendsto (fun x => log (log (m x : ℝ)) ^ 2 *
      (largestPrime (m x) : ℝ) ^ (-(19 / 640 : ℝ))) l (𝓝 0) := by
  let P : α → ℝ := fun x => largestPrime (m x)
  let T : α → ℝ := fun x => log (m x : ℝ)
  let M : α → ℝ := fun x => log (T x)
  have hmass := FullArithmeticCorrectionSecondOrder.record_mass_limits
    m mu hm hmu hrecord hP
  have hTP : Tendsto (fun x => T x / P x) l (𝓝 1) := hmass.2.2.1
  have hTpos (x : α) : 0 < T x :=
    log_pos (by exact_mod_cast (show 1 < m x by have := hm x; omega))
  have hTtop : Tendsto T l atTop := by
    apply (hTP.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hP).congr'
    filter_upwards [hP.eventually_gt_atTop 0] with x hx
    exact div_mul_cancel₀ _ hx.ne'
  have hMtop : Tendsto M l atTop := tendsto_log_atTop.comp hTtop
  have hLP : Tendsto (fun x => log (P x)) l atTop := tendsto_log_atTop.comp hP
  have hlogratio : Tendsto (fun x => log (T x / P x)) l (𝓝 0) := by
    simpa only [log_one, Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hTP
  have hz : Tendsto (fun x => log (T x / P x) / log (P x)) l (𝓝 0) :=
    hlogratio.div_atTop hLP
  have hMP : Tendsto (fun x => M x / log (P x)) l (𝓝 1) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).add hz
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [hP.eventually_gt_atTop 1] with x hx
    dsimp only [M]
    rw [log_div (hTpos x).ne' (by linarith : P x ≠ 0)]
    have hLPne : log (P x) ≠ 0 := (log_pos (show 1 < P x from hx)).ne'
    field_simp [hLPne]
    <;> ring
  have hinv : Tendsto (fun x => 1 / P x) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hP
  have hgain : Tendsto (fun x => gain 1 (P x) * P x) l (𝓝 1) := by
    have hlo : Tendsto (fun x => 1 - 1 / P x) l (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    · filter_upwards [hP.eventually_ge_atTop 2] with x hx
      simpa only [pow_one] using (normalized_gain_bounds (by norm_num : 1 ≤ 1) hx).1
    · filter_upwards [hP.eventually_ge_atTop 2] with x hx
      simpa only [pow_one] using (normalized_gain_bounds (by norm_num : 1 ≤ 1) hx).2.1
  have hproduct : Tendsto
      (fun x => (T x / P x) * (M x / log (P x)) * (gain 1 (P x) * P x))
      l (𝓝 1) := by
    simpa only [one_mul] using (hTP.mul hMP).mul hgain
  have hprice : Tendsto (fun x => (1 / (T x * M x)) / beta 1 (P x))
      l (𝓝 1) := by
    have hh := hproduct.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simp only [inv_one] at hh
    apply hh.congr'
    filter_upwards [hP.eventually_gt_atTop 1, hMtop.eventually_gt_atTop 0] with x hx hMx
    have hgpos : 0 < gain 1 (P x) :=
      HigherLayerLogSlope.gain_pos (by linarith) (by norm_num)
    dsimp only [beta]
    field_simp [(by linarith : P x ≠ 0), (log_pos hx).ne',
      (hTpos x).ne', hMx.ne', hgpos.ne'] <;> ring
  have hsmall : Tendsto (fun u : ℝ => log u ^ 2 / u ^ (19 / 640 : ℝ))
      atTop (𝓝 0) := by
    simpa only [rpow_natCast] using
      (_root_.isLittleO_log_rpow_rpow_atTop 2
        (by norm_num : (0 : ℝ) < 19 / 640)).tendsto_div_nhds_zero
  have herror : Tendsto (fun x => M x ^ 2 * P x ^ (-(19 / 640 : ℝ)))
      l (𝓝 0) := by
    have hh := (hMP.pow 2).mul (hsmall.comp hP)
    simp only [one_pow, one_mul] at hh
    apply hh.congr'
    filter_upwards [hP.eventually_gt_atTop 1] with x hx
    change (M x / log (P x)) ^ 2 * (log (P x) ^ 2 / P x ^ (19 / 640 : ℝ)) =
      M x ^ 2 * P x ^ (-(19 / 640 : ℝ))
    have hLPne : log (P x) ≠ 0 := (log_pos (show 1 < P x from hx)).ne'
    rw [Real.rpow_neg (by linarith : 0 ≤ P x)]
    field_simp [hLPne,
      (Real.rpow_pos_of_pos (by linarith : 0 < P x) (19 / 640 : ℝ)).ne']
    <;> ring
  exact ⟨hprice, hMtop, herror⟩

/- One threshold before ALL (m,mu), obtained on the space of all original
positive-price strict records. No compactness, fixed mu or record sequence
is supplied as an extra premise. -/
private theorem uniform_price_and_error (C : ℝ) :
    ∃ T0 : ℝ, 0 < T0 ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T0 ≤ (largestPrime m : ℝ) →
        2 ≤ (largestPrime m : ℝ) ∧
        0 < 1 / (log (m : ℝ) * log (log (m : ℝ))) ∧
        1 / (log (m : ℝ) * log (log (m : ℝ))) ≤
          5 * beta 1 (largestPrime m : ℝ) / 4 ∧
        C * log (log (m : ℝ)) ^ (-(4 : ℝ)) +
          C * log (log (m : ℝ)) ^ 2 *
            (largestPrime m : ℝ) ^ (-(19 / 640 : ℝ)) ≤ log 2 / 4 := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧ FullRecord v.1 v.2}
  let m : S → ℕ := fun x => x.1.1
  let mu : S → ℝ := fun x => x.1.2
  let P : S → ℝ := fun x => largestPrime (m x)
  let M : S → ℝ := fun x => log (log (m x : ℝ))
  let l : Filter S := comap P atTop
  have hP : Tendsto P l atTop := tendsto_comap
  obtain ⟨hprice, hM, herror⟩ := record_clock_price_limits m mu
    (fun x => x.2.1) (fun x => x.2.2.1) (fun x => x.2.2.2) hP
  have hinv : Tendsto (fun x => M x ^ (-(4 : ℝ))) l (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4)).comp hM
  have hbracket : Tendsto (fun x => C * M x ^ (-(4 : ℝ)) +
      C * M x ^ 2 * P x ^ (-(19 / 640 : ℝ))) l (𝓝 0) := by
    have hh := (hinv.const_mul C).add (herror.const_mul C)
    simp only [mul_zero, add_zero] at hh
    apply hh.congr
    intro x
    ring
  have hell : 0 < log (2 : ℝ) / 4 := by positivity
  have hall : ∀ᶠ x in l,
      2 ≤ P x ∧ 0 < 1 / (log (m x : ℝ) * M x) ∧
      1 / (log (m x : ℝ) * M x) ≤ 5 * beta 1 (P x) / 4 ∧
      C * M x ^ (-(4 : ℝ)) +
        C * M x ^ 2 * P x ^ (-(19 / 640 : ℝ)) ≤ log 2 / 4 := by
    filter_upwards [hP.eventually_ge_atTop 2, hM.eventually_gt_atTop 0,
      hprice.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 5 / 4)),
      hbracket.eventually (eventually_lt_nhds hell)] with x hx hMx hratio hb
    have hmx : 2 ≤ m x := x.2.1
    have hT : 0 < log (m x : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < m x by omega))
    have hlam : 0 < beta 1 (P x) := beta_pos hx (by norm_num)
    have hc := (div_lt_iff₀ hlam).mp hratio
    exact ⟨hx, one_div_pos.mpr (mul_pos hT hMx), by linarith only [hc], hb.le⟩
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  refine ⟨max T0 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn nu hnu hrecord hlarge
  let x : S := ⟨(n, nu), hn, hnu, hrecord⟩
  exact hT0 (largestPrime n : ℝ) ((le_max_left T0 2).trans hlarge) x rfl

/-- Uniform single-two-tail reduction at the actual own clock.

FullRecord retains EVERY positive strict predecessor and arbitrary positive mu.
The single T0 precedes m, mu and EVERY occupied original bad index k.
-/
theorem bhp_actual_record_single_two_tail :
    BHPMaximumGap → BHPShortIntervalCount →
      ∃ T0 : ℝ, 0 < T0 ∧
        ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
          T0 ≤ (largestPrime m : ℝ) →
          let c := 1 / (Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)))
          let a := optimalLayerCount c 2
          let v := m.factorization 2
          v ≤ a + 1 ∧
            ∀ k : ℕ, 1 ≤ k → k ≤ v → goldenLayerMarginal 2 k < c →
              v = a + 1 ∧ k = v ∧
              Icc (a + 1) v = {v} ∧
              (((v - a : ℕ) : ℝ) * Real.log 2 = Real.log 2) ∧
              (∑ j ∈ Icc (a + 1) v, (c - goldenLayerMarginal 2 j) * Real.log 2) =
                (c - goldenLayerMarginal 2 v) * Real.log 2 := by
  classical
  intro hgap hcount
  obtain ⟨C, Tf, hC, hTf, hfive⟩ := bhp_actual_five_mode_small_slack hgap hcount
  obtain ⟨Tc, hTc, hclock⟩ := uniform_price_and_error C
  refine ⟨max Tf Tc, lt_of_lt_of_le hTf (le_max_left _ _), ?_⟩
  intro m hm mu hmu hrecord hlarge
  dsimp only
  let P : ℝ := largestPrime m
  let M : ℝ := log (log (m : ℝ))
  let lambda := beta 1 P
  let c := 1 / (log (m : ℝ) * M)
  let a := optimalLayerCount c 2
  let v := m.factorization 2
  change v ≤ a + 1 ∧ ∀ k : ℕ, 1 ≤ k → k ≤ v → goldenLayerMarginal 2 k < c →
    v = a + 1 ∧ k = v ∧ Icc (a + 1) v = {v} ∧
      (((v - a : ℕ) : ℝ) * log 2 = log 2) ∧
      (∑ j ∈ Icc (a + 1) v, (c - goldenLayerMarginal 2 j) * log 2) =
        (c - goldenLayerMarginal 2 v) * log 2
  obtain ⟨hP2, hc, hcprice, hbracket⟩ :=
    hclock m hm mu hmu hrecord ((le_max_right Tf Tc).trans hlarge)
  have hlam : 0 < lambda := beta_pos hP2 (by norm_num)
  have hell : 0 < log (2 : ℝ) := log_pos (by norm_num)
  obtain ⟨n, _hn, _hnm, heta, hetab, _herror, hcomparison⟩ :=
    hfive m hm mu hmu hrecord ((le_max_left Tf Tc).trans hlarge)
  let eta := log (m : ℝ) - log (n : ℝ)
  change 0 < eta at heta
  change eta ≤ C * M ^ (-(4 : ℝ)) at hetab
  change lambda * log 2 - goldenLayerMarginal 2 v * log 2 ≤
    (lambda - mu) * eta + C * lambda * M ^ 2 * P ^ (-(19 / 640 : ℝ)) at hcomparison
  have hdeficit : lambda * log 2 - goldenLayerMarginal 2 v * log 2 ≤
      lambda * (log 2 / 4) := by
    calc
      _ ≤ (lambda - mu) * eta + C * lambda * M ^ 2 * P ^ (-(19 / 640 : ℝ)) :=
        hcomparison
      _ ≤ lambda * eta + C * lambda * M ^ 2 * P ^ (-(19 / 640 : ℝ)) := by
        nlinarith only [mul_nonneg hmu.le heta.le]
      _ ≤ lambda * (C * M ^ (-(4 : ℝ))) +
          C * lambda * M ^ 2 * P ^ (-(19 / 640 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hetab hlam.le) le_rfl
      _ = lambda * (C * M ^ (-(4 : ℝ)) +
          C * M ^ 2 * P ^ (-(19 / 640 : ℝ))) := by ring
      _ ≤ lambda * (log 2 / 4) := mul_le_mul_of_nonneg_left hbracket hlam.le
  have htop : 3 * lambda / 4 ≤ goldenLayerMarginal 2 v := by
    apply le_of_mul_le_mul_right (a := log (2 : ℝ)) ?_ hell
    nlinarith only [hdeficit]
  /- Obtain the missing-next-layer inequality from an ACTUAL canonical
  optimizer realizing the strict counts. Globality is proved for this U,
  never assumed for the original m. -/
  obtain ⟨U, hU, hcounts, hopt, _hleast⟩ := optimal_layer_count_spec hc
  have hnext : goldenLayerMarginal 2 (a + 1) ≤ c := by
    have hh := ((golden_resource_optimal_iff_layer_thresholds hc hU).mp hopt).1
      2 Nat.prime_two
    simpa only [hcounts 2] using hh
  have hvbound : v ≤ a + 1 := by
    by_contra hnot
    have hlargeval : a + 2 ≤ v := by omega
    have hhalf : 2 * goldenLayerMarginal 2 (a + 2) <
        goldenLayerMarginal 2 (a + 1) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        (two_layer_halving (j := a + 1) (by omega))
    have hmono := marginal_antitone (i := a + 2) (j := v) (by omega) hlargeval
    have hsmall : goldenLayerMarginal 2 v < c / 2 := by
      linarith only [hhalf, hmono, hnext]
    have hcprice' : c ≤ 5 * lambda / 4 := hcprice
    linarith only [htop, hsmall, hcprice', hlam]
  refine ⟨hvbound, ?_⟩
  intro k hk hkv hbad
  have hak : a < k := by
    by_contra hnot
    have hka : k ≤ a := by omega
    have hactive : k ∈ {j : ℕ | 1 ≤ j ∧ Nat.Prime 2 ∧ c < goldenLayerMarginal 2 j} := by
      rw [positive_layers_eq_count_interval hc Nat.prime_two]
      exact ⟨hk, hka⟩
    exact (not_lt_of_ge hactive.2.2.le) hbad
  have hv : v = a + 1 := by omega
  have hkv' : k = v := by omega
  have htail : Icc (a + 1) v = {v} := by rw [← hv, Icc_self]
  refine ⟨hv, hkv', htail, ?_, ?_⟩
  · have hdiff : v - a = 1 := by omega
    rw [hdiff]
    norm_num
  · rw [htail, sum_singleton]

end D5.S3.Arith.Robin.PriceRecord.ActualRecordSingleTwoTail
