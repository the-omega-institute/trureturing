/- GID: D5/S3/Arith/Robin/PriceRecord/ActualRecordElementarySingleTwoTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualRecordElementarySingleTwoTail
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Elementary single extra binary layer for all original records. -/

import D5.S3.Arith.Robin.PriceRecord.ActualRecordSingleTwoTail
import D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap

/-! Actual finite prime exchanges at the original arbitrary positive price.
The logarithmically weighted marginal estimate uses the original record balance
law and elementary gain bounds. No BHP supplier or infinite record tail is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualRecordElementarySingleTwoTail

open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope (beta gain beta_pos beta_nat)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
  (layerPrime valuation_above_layer_prime)
open D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature (normalized_gain_bounds)
open D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
  (FullRecord logMass priceLip price_variation priceLip_half_bound first_beta_lower
   largestPrime_prime)
open D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
  (actual_finite_predecessor topGain auxiliaryGain)
open D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap (ownPrice)

private theorem weighted_gain_error {α : Type*} {l : Filter α}
    (X u : α → ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hX : ∀ᶠ t in l, 0 ≤ X t) (hu : Tendsto u l atTop)
    (hsmall : Tendsto (fun t => X t / u t) l (𝓝 0)) :
    Tendsto (fun t => X t * (gain j (u t) * u t ^ j - 1)) l (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hsmall.neg) tendsto_const_nhds
  · filter_upwards [hX, hu.eventually_ge_atTop 2] with t hXt hut
    have hh := mul_le_mul_of_nonneg_left (normalized_gain_bounds hj hut).1 hXt
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    nlinarith only [hh]
  · filter_upwards [hX, hu.eventually_ge_atTop 2] with t hXt hut
    have hh := mul_le_mul_of_nonneg_left (normalized_gain_bounds hj hut).2.1 hXt
    nlinarith only [hh]

theorem weighted_boundary_limit {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ t, 2 ≤ m t)
    (hmu : ∀ t, 0 < mu t) (hrecord : ∀ t, FullRecord (m t) (mu t))
    (hP : Tendsto (fun t => (largestPrime (m t) : ℝ)) l atTop) :
    Tendsto (fun t => log (largestPrime (m t) : ℝ) *
      (beta 2 (layerPrime (m t) 2 : ℝ) / beta 1 (largestPrime (m t) : ℝ) - 1))
      l (𝓝 0) := by
  let P : α → ℝ := fun t => largestPrime (m t)
  let Q : α → ℝ := fun t => layerPrime (m t) 2
  let X : α → ℝ := fun t => log (P t)
  let H : α → ℝ := fun t => log (Q t)
  let A : α → ℝ := fun t => gain 1 (P t) * P t
  let B : α → ℝ := fun t => gain 2 (Q t) * Q t ^ 2
  let R : α → ℝ := fun t => Q t ^ 2 * H t / (P t * X t)
  have hratio := record_ratio_limit m mu hm hmu hrecord 2 (by omega) hP
  obtain ⟨hQ, hHX, _hsep⟩ := coarse_scale_limits P Q 2 (by omega)
    (fun t => Nat.cast_nonneg _) hP hratio
  have hX : Tendsto X l atTop := tendsto_log_atTop.comp hP
  have hH : Tendsto H l atTop := tendsto_log_atTop.comp hQ
  have hXH : Tendsto (fun t => X t / H t) l (𝓝 2) := by
    simpa using hHX.inv₀ (by norm_num : (2 : ℝ)⁻¹ ≠ 0)
  have hXP : Tendsto (fun t => X t / P t) l (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hP
  have hHQ : Tendsto (fun t => H t / Q t) l (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hQ
  have hXQ : Tendsto (fun t => X t / Q t) l (𝓝 0) := by
    apply (show Tendsto (fun t => X t / H t * (H t / Q t)) l (𝓝 0) from
      by simpa using hXH.mul hHQ).congr'
    filter_upwards [hH.eventually_gt_atTop 0] with t ht
    field_simp [ht.ne']
  have hAerr : Tendsto (fun t => X t * (A t - 1)) l (𝓝 0) := by
    simpa [A] using weighted_gain_error X P 1 (by omega)
      (hX.eventually_ge_atTop 0) hP hXP
  have hBerr : Tendsto (fun t => X t * (B t - 1)) l (𝓝 0) :=
    weighted_gain_error X Q 2 (by omega) (hX.eventually_ge_atTop 0) hQ hXQ
  have hA : Tendsto A l (𝓝 1) := by
    have hh := hAerr.div_atTop hX
    have hh' := hh.add_const 1
    simp only [zero_add] at hh'
    apply hh'.congr'
    filter_upwards [hX.eventually_gt_atTop 0] with t ht
    field_simp [ht.ne']
    ring
  have hR : Tendsto R l (𝓝 1) := by
    have hh := hratio.mul hHX
    norm_num only [Nat.cast_ofNat, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)] at hh
    convert hh using 1
    funext t
    dsimp [R, H, X]
    ring
  have hRerr : Tendsto (fun t => X t * (R t - 1)) l (𝓝 0) :=
    record_logarithmic_balance_limit m mu hm hmu hrecord 2 (by omega) hP
  have hnum := (hBerr.sub hAerr).sub (hA.mul hRerr)
  have hden := hA.mul hR
  have hlim := hnum.div hden (by norm_num : (1 : ℝ) * 1 ≠ 0)
  simp only [sub_zero, mul_zero, one_mul, zero_div] at hlim
  apply hlim.congr'
  filter_upwards [hP.eventually_gt_atTop 1, hQ.eventually_gt_atTop 1] with t hp hq
  have hg : gain 1 (P t) ≠ 0 :=
    (HigherLayerLogSlope.gain_pos (by linarith) (by omega)).ne'
  have hlogP : log (P t) ≠ 0 := (log_pos (show 1 < P t from hp)).ne'
  change (X t * (B t - 1) - X t * (A t - 1) - A t * (X t * (R t - 1))) /
    (A t * R t) = X t * (beta 2 (Q t) / beta 1 (P t) - 1)
  dsimp [A, B, R, X, H, beta]
  field_simp [hg, (by linarith : P t ≠ 0), (by linarith : Q t ≠ 0),
    hlogP, (log_pos hq).ne']
  ring

theorem window_fee {P Q : ℝ} {p : ℕ}
    (hP : 2 ≤ P) (hQ : 4 ≤ Q) (hQP : P ≤ Q ^ 2)
    (hlog : log P / 8 ≤ log (Q / 2))
    (hp : Q < (p : ℝ)) (hpup : (p : ℝ) ≤ Q * (1 + 1 / log Q ^ 3))
    (hpP : (p : ℝ) ≤ P) :
    |(beta 2 (p : ℝ) - beta 1 P) * log (p : ℝ)| ≤
      beta 1 P * (|log P * (beta 2 Q / beta 1 P - 1)| +
        512 * (log P / log Q ^ 3)) := by
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hX : 0 < log P := log_pos (by linarith)
  have hH : 0 < log Q := log_pos (by linarith)
  have hlam : 0 < beta 1 P := beta_pos hP (by omega)
  have hLip := priceLip_half_bound 2 (by linarith : 1 < P) hQ
    (by norm_num : (0 : ℝ) < 8) hlog
  norm_num only [Nat.cast_ofNat, Nat.reduceAdd, pow_succ, pow_zero, mul_one,
    show (2 : ℝ) * 2 * 2 = 8 by norm_num] at hLip
  have hLip0 : 0 ≤ priceLip 2 (Q / 2) := by
    unfold priceLip
    have : 0 < log (Q / 2) := log_pos (by linarith)
    positivity
  have hdist : |(p : ℝ) - Q| ≤ Q / log Q ^ 3 := by
    rw [abs_of_pos (sub_pos.mpr hp)]
    simp only [div_eq_mul_inv, one_mul] at hpup ⊢
    nlinarith only [hpup]
  have hvar := (price_variation (by omega : 1 ≤ (2 : ℕ))
    (by linarith : 2 ≤ Q / 2) (by linarith : Q / 2 ≤ Q)
    (by linarith : Q / 2 ≤ (p : ℝ))).trans
      (mul_le_mul_of_nonneg_left hdist hLip0)
  have hbase := first_beta_lower hP
  have hnorm : priceLip 2 (Q / 2) * (Q / log Q ^ 3) ≤
      512 * beta 1 P / log Q ^ 3 := by
    calc
      _ ≤ (256 / (Q ^ 3 * log P)) * (Q / log Q ^ 3) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        convert hLip using 1
        ring
      _ = 256 * (1 / (Q ^ 2 * log P)) / log Q ^ 3 := by
        field_simp [hQ0.ne', hH.ne', hX.ne']
      _ ≤ 256 * (1 / (P * log P)) / log Q ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_right hQP hX.le)) (by norm_num)
      _ ≤ _ := by
        have hh := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 256))
          (by positivity : 0 ≤ log Q ^ 3)
        convert hh using 1
        ring
  have hcenter : |beta 2 Q - beta 1 P| =
      beta 1 P * |beta 2 Q / beta 1 P - 1| := by
    calc
      _ = |beta 1 P * (beta 2 Q / beta 1 P - 1)| := by
        congr 1
        field_simp [hlam.ne']
      _ = _ := by rw [abs_mul, abs_of_pos hlam]
  have hfee := (abs_sub_le (beta 2 (p : ℝ)) (beta 2 Q) (beta 1 P)).trans
    (add_le_add (hvar.trans hnorm) le_rfl)
  have hplog : 0 ≤ log (p : ℝ) := log_nonneg (by linarith)
  have hlogp : log (p : ℝ) ≤ log P := log_le_log (by linarith) hpP
  rw [abs_mul, abs_of_nonneg hplog]
  calc
    _ ≤ (512 * beta 1 P / log Q ^ 3 + |beta 2 Q - beta 1 P|) * log P :=
      mul_le_mul hfee hlogp hplog (by positivity)
    _ = _ := by rw [hcenter, abs_mul, abs_of_pos hX]; ring

theorem window_log_mass {Q : ℝ} (hQ : 1 < Q) {U : Finset ℕ}
    (hcard : U.card = 2)
    (hU : ∀ p ∈ U, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + 1 / log Q ^ 3)) :
    2 * log Q < logMass U ∧ logMass U ≤ 2 * log Q + 2 / log Q ^ 3 := by
  have hQ0 : 0 < Q := by linarith
  have hH : 0 < log Q := log_pos hQ
  have hnonempty : U.Nonempty := card_pos.mp (by omega)
  constructor
  · have hh : (∑ _p ∈ U, log Q) < ∑ p ∈ U, log (p : ℝ) := by
      apply sum_lt_sum
      · intro p hp
        exact (log_lt_log hQ0 (hU p hp).1).le
      · obtain ⟨p, hp⟩ := hnonempty
        exact ⟨p, hp, log_lt_log hQ0 (hU p hp).1⟩
    simpa [logMass, hcard] using hh
  · have hh : (∑ p ∈ U, log (p : ℝ)) ≤ ∑ _p ∈ U, (log Q + 1 / log Q ^ 3) := by
      apply sum_le_sum
      intro p hp
      have hb := log_le_log (by linarith [(hU p hp).1] : (0 : ℝ) < p) (hU p hp).2
      have hdelta : 0 < 1 + 1 / log Q ^ 3 := by positivity
      rw [log_mul hQ0.ne' hdelta.ne'] at hb
      have he := log_le_sub_one_of_pos hdelta
      linarith
    simpa [logMass, hcard, mul_add, div_eq_mul_inv] using hh

private theorem eventual_top_layer_floor {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ t, 2 ≤ m t)
    (hmu : ∀ t, 0 < mu t) (hrecord : ∀ t, FullRecord (m t) (mu t))
    (hP : Tendsto (fun t => (largestPrime (m t) : ℝ)) l atTop) :
    ∀ᶠ t in l, 3 * beta 1 (largestPrime (m t) : ℝ) / 4 ≤
      goldenLayerMarginal 2 ((m t).factorization 2) := by
  classical
  let P : α → ℝ := fun t => largestPrime (m t)
  let Q : α → ℝ := fun t => layerPrime (m t) 2
  let X : α → ℝ := fun t => log (P t)
  let H : α → ℝ := fun t => log (Q t)
  let r : α → ℝ := fun t => Q t ^ 2 / (2 * P t)
  let E : α → ℝ := fun t => |X t * (beta 2 (Q t) / beta 1 (P t) - 1)| +
    512 * (X t / H t ^ 3)
  have hb : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hratio := record_ratio_limit m mu hm hmu hrecord 2 (by omega) hP
  obtain ⟨hQ, hHX, hsep⟩ := coarse_scale_limits P Q 2 (by omega)
    (fun t => Nat.cast_nonneg _) hP hratio
  have hX : Tendsto X l atTop := tendsto_log_atTop.comp hP
  have hH : Tendsto H l atTop := tendsto_log_atTop.comp hQ
  have hXH : Tendsto (fun t => X t / H t) l (𝓝 2) := by
    simpa using hHX.inv₀ (by norm_num : (2 : ℝ)⁻¹ ≠ 0)
  have hd : Tendsto (fun t => 1 / H t ^ 3) l (𝓝 0) :=
    ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hH).const_div_atTop 1
  have hXd : Tendsto (fun t => X t / H t ^ 3) l (𝓝 0) := by
    have hh := hXH.mul
      (((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hH).const_div_atTop 1)
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [hH.eventually_gt_atTop 0] with t ht
    dsimp only [Function.comp_def]
    field_simp [ht.ne'] <;> ring
  have hr : Tendsto r l (𝓝 1) := by
    have hh := hratio.div_const 2
    norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0)] at hh
    convert hh using 1
    funext t
    dsimp [r]
    ring
  have hlogr : Tendsto (fun t => log (r t)) l (𝓝 0) := by
    simpa using hr.log (by norm_num : (1 : ℝ) ≠ 0)
  have hsecond : Tendsto (fun t => X t * (r t - 1) + log 2) l (𝓝 0) :=
    record_second_order_limit m mu hm hmu hrecord 2 (by omega) hP
  have hweighted := weighted_boundary_limit m mu hm hmu hrecord hP
  have hE : Tendsto E l (𝓝 0) := by
    simpa only [abs_zero, mul_zero, add_zero] using hweighted.abs.add (hXd.const_mul 512)
  have hsmall : Tendsto (fun t => -log (r t) + 2 * E t) l (𝓝 0) := by
    simpa using hlogr.neg.add (hE.const_mul 2)
  have huppersep : Tendsto (fun t => (Q t * (1 + 1 / H t ^ 3)) / P t)
      l (𝓝 0) := by
    have hh := hsep.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hd)
    simp only [zero_mul] at hh
    convert hh using 1
    funext t
    ring
  have hhalflog : Tendsto (fun t => (H t - log 2) / X t) l (𝓝 (1 / 2 : ℝ)) := by
    have hh := hHX.sub (hX.const_div_atTop (log 2))
    norm_num only [Nat.cast_ofNat, sub_zero, inv_eq_one_div] at hh
    convert hh using 1
    funext t
    ring
  obtain ⟨Tw, _hTw, hwindows⟩ := shrinking_prime_windows 1 zero_lt_one
  filter_upwards [hP.eventually_gt_atTop 4, hQ.eventually_ge_atTop (max Tw 4),
    hH.eventually_ge_atTop 2,
    hratio.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) < 2)),
    huppersep.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    hhalflog.eventually (eventually_gt_nhds (by norm_num : (1 / 8 : ℝ) < 1 / 2)),
    hsecond.eventually_lt_const (show (0 : ℝ) < log 2 / 2 by positivity),
    hXd.eventually_lt_const (show (0 : ℝ) < log 2 / 8 by positivity),
    hsmall.eventually_lt_const (show (0 : ℝ) < log 2 / 4 by positivity)]
    with t hp hq hH2 hratio1 hupper hhalf hsecond' hXd' hsmall'
  have hP0 : 0 < P t := by linarith
  have hQ4 : 4 ≤ Q t := (le_max_right Tw 4).trans hq
  have hQ0 : 0 < Q t := by linarith
  have hXp : 0 < X t := log_pos (by linarith)
  have hHp : 0 < H t := by linarith
  have hlam : 0 < beta 1 (P t) := beta_pos (by linarith) (by omega)
  have hdelta : 0 ≤ 1 / H t ^ 3 := by positivity
  have hupper' : Q t * (1 + 1 / H t ^ 3) < P t := (div_lt_one hP0).mp hupper
  have hQP : Q t < P t := by nlinarith only [hupper', mul_nonneg hQ0.le hdelta]
  have hPQ2 : P t ≤ Q t ^ 2 := by
    have hh := (one_lt_div hP0).mp hratio1
    linarith
  have hloghalf : X t / 8 ≤ log (Q t / 2) := by
    rw [log_div hQ0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have hh := (lt_div_iff₀ hXp).mp hhalf
    change X t / 8 ≤ H t - log 2
    linarith
  have hcapacity : 2 ≤ ⌈(1 : ℝ) * log (Q t) ^ 3⌉₊ := by
    have hpow : (2 : ℝ) ≤ H t ^ 3 := by nlinarith [sq_nonneg (H t - 2)]
    have hh := hpow.trans (Nat.le_ceil (H t ^ 3))
    exact_mod_cast (by simpa only [one_mul] using hh :
      (2 : ℝ) ≤ (⌈(1 : ℝ) * log (Q t) ^ 3⌉₊ : ℝ))
  obtain ⟨_Lo, U, _hLo, hUcard, _hLow, hU⟩ :=
    hwindows (Q t) ((le_max_left Tw 4).trans hq) 2 hcapacity
  have hpP (p : ℕ) (hu : p ∈ U) : (p : ℝ) < P t :=
    (hU p hu).2.2.trans_lt hupper'
  have hval (p : ℕ) (hprime : p.Prime) (hbelow : (p : ℝ) ≤ P t)
      (habove : Q t < (p : ℝ)) : (m t).factorization p = 1 := by
    have hsupport := (price_record_prime_structure (hm t) (hmu t) (hrecord t)).2
    have hmem : p ∈ (m t).primeFactors := by
      rw [hsupport]
      exact Nat.mem_primesLE.mpr ⟨by dsimp only [P] at hbelow; exact_mod_cast hbelow, hprime⟩
    have hlo := (hprime.dvd_iff_one_le_factorization (by have := hm t; omega)).mp
      (Nat.dvd_of_mem_primeFactors hmem)
    have hhi := valuation_above_layer_prime (by have := hm t; omega : 0 < m t)
      (by omega : 1 ≤ (2 : ℕ)) hprime
      (by dsimp only [Q] at habove; exact_mod_cast habove)
    omega
  have hPprime := largestPrime_prime (hm t)
  have hPval : (m t).factorization (largestPrime (m t)) = 1 := hval _ hPprime le_rfl hQP
  have hUval (p : ℕ) (hu : p ∈ U) : (m t).factorization p = 1 :=
    hval p (hU p hu).1 (hpP p hu).le (hU p hu).2.1
  have hlogs := window_log_mass (by linarith : 1 < Q t) hUcard
    (fun p hu => (hU p hu).2)
  have hrlog : log (r t) = 2 * H t - log 2 - X t := by
    dsimp [r, H, X]
    rw [log_div (pow_ne_zero 2 hQ0.ne') (mul_ne_zero (by norm_num) hP0.ne'),
      log_pow, log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne']
    norm_num only [Nat.cast_ofNat]
    ring
  have hrpos : 0 < r t := div_pos (pow_pos hQ0 2) (by positivity)
  have hrle := log_le_sub_one_of_pos hrpos
  let eta := log 2 + X t - logMass U
  have heta : 0 < eta := by
    have hlower : -log (r t) - 2 / H t ^ 3 ≤ eta := by
      dsimp only [eta]
      rw [hrlog]
      linarith only [hlogs.2]
    have hmul : 0 < X t * (-log (r t) - 2 / H t ^ 3) := by
      have hh := mul_le_mul_of_nonneg_left hrle hXp.le
      simp only [div_eq_mul_inv] at hXd' ⊢
      nlinarith only [hh, hsecond', hXd', hb]
    exact (pos_of_mul_pos_right hmul hXp.le).trans_le hlower
  have heta_upper : eta ≤ -log (r t) := by
    dsimp only [eta]
    rw [hrlog]
    linarith only [hlogs.1]
  let D : Finset ℕ := {largestPrime (m t)}
  have hD : ∀ p ∈ D, p.Prime ∧ 2 < p ∧ p ∣ m t := by
    intro p hd
    have heq : p = largestPrime (m t) := mem_singleton.mp hd
    subst p
    refine ⟨hPprime, by exact_mod_cast (show (2 : ℝ) < largestPrime (m t) by linarith), ?_⟩
    exact (hPprime.dvd_iff_one_le_factorization (by have := hm t; omega)).mpr
      (by omega)
  have hUp : ∀ p ∈ U, p.Prime ∧ 2 < p := by
    intro p hu
    exact ⟨(hU p hu).1, by exact_mod_cast (show (2 : ℝ) < p by linarith [(hU p hu).2.1])⟩
  have hDU : Disjoint D U := by
    apply disjoint_left.mpr
    intro p hd hu
    have heq : p = largestPrime (m t) := mem_singleton.mp hd
    have hh := hpP p hu
    rw [heq] at hh
    exact (lt_irrefl (P t)) hh
  have hDmass : logMass D = X t := by simp [D, logMass, X, P]
  obtain ⟨n, _hn, _hnm, hmass, _hfac, _hobj, hcomparison⟩ :=
    actual_finite_predecessor (hm t) (hmu t) (hrecord t) (lambda := beta 1 (P t))
      D U hD hUp hDU (by rw [hDmass]; exact heta)
  have hfee : -auxiliaryGain (beta 1 (P t)) (m t) D U ≤ 2 * beta 1 (P t) * E t := by
    have hDfee : (∑ p ∈ D, (goldenLayerMarginal p ((m t).factorization p) -
        beta 1 (P t)) * log p) = 0 := by
      simp only [D, sum_singleton, hPval]
      rw [← beta_nat hPprime (by omega : 1 ≤ (1 : ℕ))]
      simp [P]
    have hpoint (p : ℕ) (hu : p ∈ U) :
        -(goldenLayerMarginal p ((m t).factorization p + 1) - beta 1 (P t)) *
          log p ≤ beta 1 (P t) * E t := by
      rw [hUval p hu]
      norm_num only [Nat.reduceAdd]
      rw [← beta_nat (hU p hu).1 (by omega : 1 ≤ (2 : ℕ))]
      have hh := window_fee (by linarith : 2 ≤ P t) hQ4 hPQ2 hloghalf
        (hU p hu).2.1 (hU p hu).2.2 (hpP p hu).le
      have hab := neg_le_abs ((beta 2 (p : ℝ) - beta 1 (P t)) * log p)
      dsimp only [E, X, H] at *
      linarith only [hh, hab]
    dsimp only [auxiliaryGain]
    rw [hDfee, sub_zero, ← sum_neg_distrib]
    calc
      _ ≤ ∑ _p ∈ U, beta 1 (P t) * E t := by
        apply sum_le_sum
        intro p hu
        simpa only [neg_mul] using hpoint p hu
      _ = _ := by simp [hUcard]; ring
  have hmass' : log (m t : ℝ) - log (n : ℝ) = eta := by
    simpa only [hDmass] using hmass
  rw [hmass'] at hcomparison
  have hdeficit : topGain (beta 1 (P t)) (m t) ≤ beta 1 (P t) * (log 2 / 4) := by
    have hmueta := mul_pos (hmu t) heta
    have hbudget : eta + 2 * E t < log 2 / 4 := by linarith only [heta_upper, hsmall']
    have hbnd := mul_lt_mul_of_pos_left hbudget hlam
    nlinarith only [hcomparison, hfee, hmueta, hbnd]
  dsimp only [topGain] at hdeficit
  have hmul : (3 * beta 1 (P t) / 4) * log 2 ≤
      goldenLayerMarginal 2 ((m t).factorization 2) * log 2 := by linarith only [hdeficit]
  exact le_of_mul_le_mul_right hmul hb

private theorem uniform_prime_threshold :
    ∃ T : ℝ, 0 < T ∧ ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu →
      FullRecord m mu → T ≤ (largestPrime m : ℝ) →
      m.factorization 2 ≤ optimalLayerCount (ownPrice m) 2 + 1 := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧ FullRecord v.1 v.2}
  let m : S → ℕ := fun t => t.1.1
  let mu : S → ℝ := fun t => t.1.2
  let P : S → ℝ := fun t => largestPrime (m t)
  let l : Filter S := comap P atTop
  have hfloor := eventual_top_layer_floor (l := l) m mu (fun t => t.2.1)
    (fun t => t.2.2.1) (fun t => t.2.2.2) (show Tendsto P l atTop from tendsto_comap)
  obtain ⟨Tf, hTf⟩ := eventually_atTop.mp (eventually_comap.mp hfloor)
  obtain ⟨Tc, hTc, hclock⟩ := ActualRecordSingleTwoTail.uniform_price_and_error 0
  refine ⟨max Tf Tc, hTc.trans_le (le_max_right _ _), ?_⟩
  intro n hn nu hnu hrecord hlarge
  let t : S := ⟨(n, nu), hn, hnu, hrecord⟩
  have htop := hTf (largestPrime n : ℝ) ((le_max_left Tf Tc).trans hlarge) t rfl
  obtain ⟨hP2, hc, hcprice, _herror⟩ :=
    hclock n hn nu hnu hrecord ((le_max_right Tf Tc).trans hlarge)
  change 0 < ownPrice n at hc
  change ownPrice n ≤ 5 * beta 1 (largestPrime n : ℝ) / 4 at hcprice
  change 3 * beta 1 (largestPrime n : ℝ) / 4 ≤
    goldenLayerMarginal 2 (n.factorization 2) at htop
  obtain ⟨U, hU, hcounts, hopt, _hleast⟩ := optimal_layer_count_spec hc
  have hnext : goldenLayerMarginal 2 (optimalLayerCount (ownPrice n) 2 + 1) ≤
      ownPrice n := by
    have hh := ((golden_resource_optimal_iff_layer_thresholds hc hU).mp hopt).1
      2 Nat.prime_two
    simpa only [hcounts 2] using hh
  by_contra hnot
  have hval : optimalLayerCount (ownPrice n) 2 + 2 ≤ n.factorization 2 := by omega
  have hhalf := ActualRecordSingleTwoTail.two_layer_halving
    (j := optimalLayerCount (ownPrice n) 2 + 1) (by omega)
  have hmono := ActualRecordSingleTwoTail.marginal_antitone
    (i := optimalLayerCount (ownPrice n) 2 + 2) (j := n.factorization 2) (by omega) hval
  have hlam : 0 < beta 1 (largestPrime n : ℝ) := beta_pos hP2 (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hhalf
  linarith only [hnext, hhalf, hmono, htop, hcprice, hlam]

/-- One natural threshold for every original strict full record and every
positive original price, at the integer's exact own clock and strict canonical
layer count. The assertion also allows an empty eventual record tail. -/
theorem eventual_actual_record_single_two_tail :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
      m.factorization 2 ≤ optimalLayerCount (ownPrice m) 2 + 1 := by
  obtain ⟨T, _hT, hbound⟩ := uniform_prime_threshold
  let B := max T 2
  have hB : 2 ≤ B := le_max_right _ _
  have hB0 : 0 < B := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (exp (B * log (4 * B ^ 2) + 2))
  refine ⟨max N 2, ?_⟩
  intro m hm mu hmu hrecord
  have hm2 : 2 ≤ m := (le_max_right N 2).trans hm
  have hNm : (N : ℝ) ≤ m := by exact_mod_cast (le_max_left N 2).trans hm
  have hmlog : B * log (4 * B ^ 2) + 2 < log (m : ℝ) := by
    have hh := log_lt_log (exp_pos _) (hN.trans_le hNm)
    simpa only [log_exp] using hh
  apply hbound m hm2 mu hmu hrecord
  by_contra hnot
  have hP2 : (2 : ℝ) ≤ largestPrime m := by
    exact_mod_cast (largestPrime_prime hm2).two_le
  have hPB : (largestPrime m : ℝ) ≤ B :=
    (le_of_not_ge hnot).trans (le_max_left T 2)
  have hlogle : log (4 * (largestPrime m : ℝ) ^ 2) ≤ log (4 * B ^ 2) := by
    apply log_le_log (by positivity)
    nlinarith only [hPB, hP2, hB, sq_nonneg (B - (largestPrime m : ℝ))]
  have hlog0 : 0 ≤ log (4 * (largestPrime m : ℝ) ^ 2) := by
    apply log_nonneg
    nlinarith only [hP2, sq_nonneg ((largestPrime m : ℝ) - 2)]
  have hmass := FullArithmeticCorrectionSecondOrder.record_log_envelope hm2 hmu hrecord
  have hh := mul_le_mul hPB hlogle hlog0 hB0.le
  linarith only [hmass, hh, hmlog]

#print axioms eventual_actual_record_single_two_tail

end D5.S3.Arith.Robin.PriceRecord.ActualRecordElementarySingleTwoTail
