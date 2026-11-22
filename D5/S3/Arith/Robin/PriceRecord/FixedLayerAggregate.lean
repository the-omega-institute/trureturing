/- GID: D5/S3/Arith/Robin/PriceRecord/FixedLayerAggregate
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedLayerAggregate
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: Fixed-layer approximation and residual limit for the supported integer infimum. -/

import D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation
import D5.S3.Arith.Robin.PriceRecord.FixedLayerPrimeTail
import D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSecondOrder
import D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSharpLimit
import Mathlib.Tactic

/-!
# Fixed activation layers of the supported integer Robin infimum

The finite cap estimate controls every omitted Euler layer. The retained layers
can then be replaced by their clipped reciprocal powers with a summable error.
A comparison of the full nonlinear and linear cost images transfers these
bounds to the supported integer infimum at the literal prime-prefix price.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate

open Finset Filter Real
open scoped BigOperators Topology
open FixedLayerFiniteActivation
  (layerGain layerGain_eq_eulerTerm_sub clippedLayers fixedPriceMinimum fixed_price_omitted_layers)
open FixedLayerPrimeTail (activationLayer activation_layer_tendsto)
open FixedLayerRigidity (golden_layer_gain_lower)
open D5.S3.Arith.GoldenLayerMarginalDecay (golden_layer_marginal_le_inv_pow)
open FixedSupportIntegerActivationEnvelope
  (supportedAdmissible integerValues integerInfimum clockIncrement eulerTerm tailCost linearCost)
open RealInfimumPrimeBoundary
  (prefixH prefixEll prefixPrice prefixH_atTop prefixEll_atTop eventual_prefix_domains)
open IntegerInfimumSecondOrder (log_pow_over_H_rpow)
open IntegerInfimumSharpLimit (fixed_price_tangent_bound)
open OwnClockFixedSupport (primeSupport admissible theta clock terminalCost phi baseline
  tangentRemainder theta_gt_one theta_le_clock tangent_remainder_nonnegative)
open BoundaryPrimePrice (benefit probability benefit_log)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (finite_cubic_tail)
open D5.S3.Arith.Lattices.Klartag (neg_log_one_sub_le)

local notation "H" => prefixH
local notation "ℓ" => prefixEll
private def I (P : ℕ) : ℝ := integerInfimum (Nat.primesLE P)

private lemma inv_pow_le_half {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    1 / (p : ℝ) ^ k ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpow : (p : ℝ) ≤ (p : ℝ) ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p) hk
  exact one_div_le_one_div_of_le (by norm_num) (hp2.trans hpow)

lemma eulerTerm_le_twice_power {p k : ℕ} (hp : p.Prime) :
    0 ≤ eulerTerm p k ∧ eulerTerm p k ≤ 2 / (p : ℝ) ^ (k + 1) := by
  let x : ℝ := 1 / (p : ℝ) ^ (k + 1)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x ≤ 1 / 2 := inv_pow_le_half hp (by omega)
  have hlog : 0 ≤ -log (1 - x) :=
    neg_nonneg.mpr (log_nonpos (by linarith) (by linarith))
  have hquad := neg_log_one_sub_le hx0 hx2
  have hmul := mul_nonneg hx0 (show 0 ≤ 1 - x by linarith)
  refine ⟨hlog, ?_⟩
  rw [show 2 / (p : ℝ) ^ (k + 1) = 2 * x by dsimp [x]; ring]
  change -log (1 - x) ≤ 2 * x
  nlinarith only [hquad, hmul]

/-- The difference between clipping the reciprocal power and clipping the Euler increment
vanishes up to the power cutoff. Beyond the cutoff it is bounded by the next power. -/
private lemma clipped_layer_error {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j)
    {B : ℝ} (hB : 1 < B) :
    let q := 1 / (B * log B) * log (p : ℝ)
    let d := min q (1 / (p : ℝ) ^ j) -
      min q (eulerTerm p (j - 1) - eulerTerm p j)
    0 ≤ d ∧ d ≤ (if B ^ (1 / (j : ℝ)) < (p : ℝ) then
      1 / (p : ℝ) ^ (j + 1) else 0) := by
  dsimp only
  let q := 1 / (B * log B) * log (p : ℝ)
  let x : ℝ := 1 / (p : ℝ) ^ j
  let y : ℝ := 1 / (p : ℝ) ^ (j + 1)
  let u : ℝ := B ^ (1 / (j : ℝ))
  let D : ℝ := eulerTerm p (j - 1) - eulerTerm p j
  change 0 ≤ min q x - min q D ∧ min q x - min q D ≤ if u < (p : ℝ) then y else 0
  have hj1 : 1 ≤ j := by omega
  have hD : layerGain p j = D := layerGain_eq_eulerTerm_sub hp hj1
  have hlo : x - y ≤ D := by
    rw [← hD, layerGain]
    calc
      x - y = (1 - (p : ℝ)⁻¹) * (p : ℝ)⁻¹ ^ j := by
        dsimp only [x, y]
        simp only [one_div, ← inv_pow]
        rw [pow_succ]
        ring
      _ ≤ _ := golden_layer_gain_lower hp hj1
  have hhi : D ≤ x := by
    rw [← hD, layerGain]
    simpa only [x, one_div, inv_pow] using
      (le_div_iff₀ hp.log_pos).mp (golden_layer_marginal_le_inv_pow hp hj1)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hlog := log_pos hB
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  refine ⟨sub_nonneg.mpr (min_le_min le_rfl hhi), ?_⟩
  split_ifs with hcut
  · by_cases h : q ≤ D
    · rw [min_eq_left h, min_eq_left (h.trans hhi), sub_self]
      dsimp [y]; positivity
    · rw [min_eq_right (le_of_not_ge h)]
      linarith only [min_le_right q x, hlo]
  · have hlogp : log (p : ℝ) ≤ log B / 2 := by
      have hlogu := log_le_log hp0 (le_of_not_gt hcut)
      rw [show log u = (1 / (j : ℝ)) * log B by
        dsimp only [u]; exact log_rpow hB0 _] at hlogu
      calc
        _ ≤ (1 / (j : ℝ)) * log B := hlogu
        _ ≤ (1 / 2) * log B :=
          mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) hjR) hlog.le
        _ = _ := by ring
    have hu : u ^ j = B := by
      dsimp only [u]
      rw [← rpow_natCast, ← rpow_mul hB0.le, div_mul_cancel₀ _ hj0.ne', rpow_one]
    have hpow : (p : ℝ) ^ j ≤ B :=
      (pow_le_pow_left₀ hp0.le (le_of_not_gt hcut) j).trans_eq hu
    have hq : q ≤ x / 2 := by
      calc
        q ≤ (1 / (B * log B)) * (log B / 2) :=
          mul_le_mul_of_nonneg_left hlogp (by positivity)
        _ = (1 / B) / 2 := by field_simp [hB0.ne', hlog.ne']
        _ ≤ x / 2 := div_le_div_of_nonneg_right
          (one_div_le_one_div_of_le (pow_pos hp0 _) hpow) (by norm_num)
    have hhalf : x / 2 ≤ x - y := by
      have heq : x = (p : ℝ) * y := by
        dsimp only [x, y]
        rw [pow_succ]
        field_simp [hp0.ne']
      have hy : 0 ≤ y := by dsimp [y]; positivity
      nlinarith only [heq, mul_le_mul_of_nonneg_right hp2 hy]
    have h := hq.trans (hhalf.trans hlo)
    simp only [min_eq_left h, min_eq_left (h.trans hhi), sub_self, le_refl]

/-- The public finite cubic estimate supplies all the larger integer power tails. -/
private lemma finite_inverse_power_tail {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 2 ≤ j)
    (S : Finset ℕ) (hS : ∀ p ∈ S, u < (p : ℝ)) :
    (∑ p ∈ S, 1 / (p : ℝ) ^ (j + 1)) ≤ 2 / u ^ j := by
  have hj' : j - 2 + 2 = j := Nat.sub_add_cancel hj
  calc
    _ ≤ (1 / u ^ (j - 2)) * ∑ p ∈ S, 1 / (p : ℝ) ^ 3 := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hcmp := one_div_le_one_div_of_le (pow_pos hu (j - 2))
        (pow_le_pow_left₀ hu.le (hS p hp).le (j - 2))
      calc
        1 / (p : ℝ) ^ (j + 1) =
            (1 / (p : ℝ) ^ (j - 2)) * (1 / (p : ℝ) ^ 3) := by
          rw [one_div_mul_one_div, ← pow_add, show j - 2 + 3 = j + 1 by omega]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcmp (by positivity)
    _ ≤ (1 / u ^ (j - 2)) * (2 / u ^ 2) :=
      mul_le_mul_of_nonneg_left (finite_cubic_tail hu S hS) (by positivity)
    _ = 2 / u ^ j := by
      rw [show (1 / u ^ (j - 2)) * (2 / u ^ 2) = 2 / (u ^ (j - 2) * u ^ 2) by ring,
        ← pow_add, hj']

/-- The error at a single retained layer is supported above the exact root cutoff. -/
private lemma retained_layer_bounds {S : Finset ℕ} (hS : primeSupport S)
    {B : ℝ} (hB : 1 < B) {j : ℕ} (hj : 2 ≤ j) :
    let q := fun p : ℕ => 1 / (B * log B) * log (p : ℝ)
    let E := (∑ p ∈ S, min (q p) (1 / (p : ℝ) ^ j)) -
      (∑ p ∈ S, min (q p) (layerGain p j))
    0 ≤ E ∧ E ≤ 2 / B := by
  classical
  dsimp only
  let u : ℝ := B ^ (1 / (j : ℝ))
  have hB0 := zero_lt_one.trans hB
  have hu : 0 < u := rpow_pos_of_pos hB0 _
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have huPow : u ^ j = B := by
    dsimp only [u]
    rw [← rpow_natCast, ← rpow_mul hB0.le, div_mul_cancel₀ _ hj0, rpow_one]
  have hpoint (p : ℕ) (hp : p ∈ S) := clipped_layer_error (hS p hp) hj hB
  have hgain (p : ℕ) (hp : p ∈ S) :
      layerGain p j = eulerTerm p (j - 1) - eulerTerm p j :=
    layerGain_eq_eulerTerm_sub (hS p hp) (by omega)
  rw [← sum_sub_distrib]
  constructor
  · exact sum_nonneg (fun p hp => by simpa only [hgain p hp] using (hpoint p hp).1)
  · calc
      _ ≤ ∑ p ∈ S, (if u < (p : ℝ) then 1 / (p : ℝ) ^ (j + 1) else 0) := by
        apply sum_le_sum
        intro p hp
        simpa only [hgain p hp] using (hpoint p hp).2
      _ = ∑ p ∈ S.filter (fun p : ℕ => u < (p : ℝ)), 1 / (p : ℝ) ^ (j + 1) :=
        by rw [sum_filter]
      _ ≤ 2 / u ^ j := finite_inverse_power_tail hu hj _ (fun p hp => (mem_filter.mp hp).2)
      _ = 2 / B := by rw [huPow]

/-- Finite aggregate of the retained reciprocal-power layers. -/
private def reciprocalLayers (S : Finset ℕ) (lam : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Ioc 1 m, ∑ p ∈ S, min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ j)

/-- Finite aggregate of the same layers with their exact Euler marginals. -/
private def exactLayers (S : Finset ℕ) (lam : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Ioc 1 m, ∑ p ∈ S, min (lam * log (p : ℝ)) (layerGain p j)

private lemma retained_layers_bounds {S : Finset ℕ} (hS : primeSupport S)
    {B : ℝ} (hB : 1 < B) {m : ℕ} (hm : 2 ≤ m) :
    let lam := 1 / (B * log B)
    0 ≤ reciprocalLayers S lam m - exactLayers S lam m ∧
      reciprocalLayers S lam m - exactLayers S lam m ≤ 2 * ((m : ℝ) - 1) / B := by
  dsimp only [reciprocalLayers, exactLayers]
  rw [← sum_sub_distrib]
  have hbound (j : ℕ) (hj : j ∈ Ioc 1 m) :=
    retained_layer_bounds hS hB (by have := (mem_Ioc.mp hj).1; omega : 2 ≤ j)
  refine ⟨sum_nonneg (fun j hj => (hbound j hj).1), ?_⟩
  calc
    _ ≤ ∑ _j ∈ Ioc 1 m, 2 / B := sum_le_sum (fun j hj => (hbound j hj).2)
    _ = _ := by
      rw [sum_const, Nat.card_Ioc, nsmul_eq_mul,
        Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      ring

private def remainderConstant : ℝ := (3 + 2 / log 2) * log 4 + 4

/-- Every omitted exact marginal is covered by one finite cap per prime.
The head uses a uniform logarithmic cap and the tail uses just the retained cap. -/
private theorem omitted_layers_aggregate {S : Finset ℕ} (hS : primeSupport S)
    {B : ℝ} (hB : 1 < B) (hlog : 1 ≤ log B) {m : ℕ} (hm : 2 ≤ m) :
    let lam := 1 / (B * log B)
    let R := fixedPriceMinimum S lam - exactLayers S lam m
    0 ≤ R ∧ R ≤ remainderConstant / B ^ ((m : ℝ) / ((m : ℝ) + 1)) := by
  classical
  let L := log B
  let lam := 1 / (B * L)
  let n := ⌈log (2 * B) / log 2⌉₊
  let K := m + n + 1
  let Y : ℝ := B ^ (1 / ((m : ℝ) + 1))
  let C : ℝ := 3 + 2 / log 2
  let cap := fun p : ℕ => if (p : ℝ) ≤ Y then K else m
  let head := S.filter (fun p : ℕ => (p : ℝ) ≤ Y)
  let tail := S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y)
  have hB0 := zero_lt_one.trans hB
  have hL0 : 0 < L := log_pos hB
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlam : 0 < lam := one_div_pos.mpr (mul_pos hB0 hL0)
  have hY : 0 < Y := rpow_pos_of_pos hB0 _
  have hKm : m ≤ K := by dsimp [K]; omega
  have hcap (p : ℕ) : m ≤ cap p := by dsimp only [cap]; split_ifs <;> omega
  have hexact : exactLayers S lam m =
      ∑ p ∈ S, clippedLayers p (lam * log (p : ℝ)) m := by
    unfold exactLayers clippedLayers
    rw [sum_comm]
  have hR := fixed_price_omitted_layers hS hlam hm cap (fun p _ => hcap p)
  rw [← hexact] at hR
  refine ⟨hR.1, hR.2.trans ?_⟩
  have hn_lower : log (2 * B) / log 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hn_upper : (n : ℝ) ≤ L / log 2 + 2 := by
    have h := (Nat.ceil_lt_add_one
      (div_nonneg (log_nonneg (by linarith : 1 ≤ 2 * B)) h2.le)).le
    change (n : ℝ) ≤ log (2 * B) / log 2 + 1 at h
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hB0.ne'] at h
    change (n : ℝ) ≤ (log 2 + L) / log 2 + 1 at h
    rwa [add_div, div_self h2.ne', show 1 + L / log 2 + 1 = L / log 2 + 2 by ring] at h
  have hKn : ((K - m : ℕ) : ℝ) = (n : ℝ) + 1 := by
    rw [show K - m = n + 1 by dsimp [K]; omega, Nat.cast_add, Nat.cast_one]
  have hcharge : ((K - m : ℕ) : ℝ) * lam ≤ (3 + 1 / log 2) / B := by
    rw [hKn]
    dsimp only [lam]
    have hL1 : 1 ≤ L := hlog
    calc
      ((n : ℝ) + 1) * (1 / (B * L)) ≤ (L / log 2 + 3) * (1 / (B * L)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hn_upper]) hlam.le
      _ = ((L / log 2 + 3) / L) / B := by
        rw [mul_one_div, div_div, mul_comm L B]
      _ ≤ (3 + 1 / log 2) / B := by
        apply div_le_div_of_nonneg_right _ hB0.le
        apply (div_le_iff₀ hL0).mpr
        rw [show (3 + 1 / log 2) * L = 3 * L + L / log 2 by ring]
        linarith only [hL1]
  have hlarge : B ≤ (2 : ℝ) ^ K := by
    have hn : 2 * B ≤ (2 : ℝ) ^ n := by
      apply le_of_not_gt
      intro hcontra
      have hlt := log_lt_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hcontra
      rw [log_pow] at hlt
      have hle := (div_le_iff₀ h2).mp hn_lower
      exact (not_lt_of_ge hle) hlt
    have hmono : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ K :=
      pow_le_pow_right₀ (by norm_num) (by dsimp [K]; omega)
    exact (by linarith : B ≤ 2 * B).trans (hn.trans hmono)
  let f := fun p : ℕ =>
    ((cap p - m : ℕ) : ℝ) * (lam * log (p : ℝ)) + eulerTerm p (cap p)
  have hhead_term (p : ℕ) (hp : p ∈ head) : f p ≤ (C / B) * log (p : ℝ) := by
    obtain ⟨hpS, hpY⟩ := mem_filter.mp hp
    have hprime := hS p hpS
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hlogp : log 2 ≤ log (p : ℝ) := log_le_log (by norm_num) hp2
    have hEuler : eulerTerm p K ≤ 1 / B := by
      calc
        _ ≤ 2 / (p : ℝ) ^ (K + 1) := (eulerTerm_le_twice_power hprime).2
        _ ≤ 2 / (2 : ℝ) ^ (K + 1) := div_le_div_of_nonneg_left (by norm_num)
          (pow_pos (by norm_num) _) (pow_le_pow_left₀ (by norm_num) hp2 _)
        _ = 1 / (2 : ℝ) ^ K := by
          rw [pow_succ]
          field_simp [pow_ne_zero K (by norm_num : (2 : ℝ) ≠ 0)] <;> ring
        _ ≤ 1 / B := one_div_le_one_div_of_le hB0 hlarge
    have hEuler' : 1 / B ≤ (1 / log 2) / B * log (p : ℝ) := by
      have hfrac : 1 ≤ log (p : ℝ) / log 2 :=
        (le_div_iff₀ h2).2 (by simpa only [one_mul] using hlogp)
      calc
        1 / B = (1 / B) * 1 := by ring
        _ ≤ (1 / B) * (log (p : ℝ) / log 2) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = _ := by ring
    dsimp only [f, cap]
    rw [ite_eq_left hpY, ← mul_assoc]
    calc
      _ ≤ ((3 + 1 / log 2) / B) * log (p : ℝ) + (1 / log 2) / B * log (p : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_right hcharge (h2.le.trans hlogp))
          (hEuler.trans hEuler')
      _ = _ := by dsimp only [C]; ring
  have hhead_sum : (∑ p ∈ head, f p) ≤ (C / B) * (log 4 * Y) := by
    have hsubset : head ⊆ Nat.primesLE ⌊Y⌋₊ := by
      intro p hp
      obtain ⟨hpS, hpY⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hY.le).2 hpY, hS p hpS⟩
    have hCB : 0 ≤ C / B := by dsimp only [C]; positivity
    calc
      _ ≤ ∑ p ∈ head, (C / B) * log (p : ℝ) := sum_le_sum hhead_term
      _ = (C / B) * ∑ p ∈ head, log (p : ℝ) := (mul_sum ..).symm
      _ ≤ (C / B) * Chebyshev.theta Y := by
        rw [Chebyshev.theta_eq_sum_primesLE]
        apply mul_le_mul_of_nonneg_left _ hCB
        exact sum_le_sum_of_subset_of_nonneg hsubset
          (fun p hp _ => (Nat.mem_primesLE.mp hp).2.log_pos.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hY.le) hCB
  have htail_sum : (∑ p ∈ tail, f p) ≤ 4 / Y ^ m := by
    calc
      _ ≤ ∑ p ∈ tail, 2 * (1 / (p : ℝ) ^ (m + 1)) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpS, hpY⟩ := mem_filter.mp hp
        simpa only [f, cap, ite_eq_right hpY, Nat.sub_self, Nat.cast_zero, zero_mul, zero_add,
          mul_one_div] using (eulerTerm_le_twice_power (hS p hpS) (k := m)).2
      _ = 2 * ∑ p ∈ tail, 1 / (p : ℝ) ^ (m + 1) := (mul_sum ..).symm
      _ ≤ 2 * (2 / Y ^ m) := mul_le_mul_of_nonneg_left
        (finite_inverse_power_tail hY hm tail (fun p hp => lt_of_not_ge (mem_filter.mp hp).2))
        (by norm_num)
      _ = _ := by ring
  have hmplus : 0 < (m : ℝ) + 1 := by positivity
  have hYpow : Y ^ m = B ^ ((m : ℝ) / ((m : ℝ) + 1)) := by
    dsimp only [Y]
    rw [← rpow_natCast, ← rpow_mul hB0.le]
    rw [show 1 / ((m : ℝ) + 1) * (m : ℝ) =
      (m : ℝ) / ((m : ℝ) + 1) by ring]
  have hYquot : Y / B = 1 / B ^ ((m : ℝ) / ((m : ℝ) + 1)) := by
    have hsum : 1 / ((m : ℝ) + 1) + (m : ℝ) / ((m : ℝ) + 1) = 1 := by
      field_simp [hmplus.ne']
      ring
    apply (div_eq_div_iff hB0.ne' (rpow_pos_of_pos hB0 _).ne').2
    dsimp only [Y]
    rw [← rpow_add hB0, hsum, rpow_one, one_mul]
  change (∑ p ∈ S, f p) ≤ _
  rw [← sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ Y) f]
  change (∑ p ∈ head, f p) + (∑ p ∈ tail, f p) ≤ _
  calc
    _ ≤ (C / B) * (log 4 * Y) + 4 / Y ^ m := add_le_add hhead_sum htail_sum
    _ = C * log 4 * (Y / B) + 4 / Y ^ m := by ring
    _ = _ := by rw [hYquot, hYpow]; dsimp only [remainderConstant, C]; ring

/-- Exact normalizations on the full admissible integer image. -/
lemma integer_loss_forms {S : Finset ℕ} (hS : primeSupport S)
    {a : ℕ → ℕ} (ha : supportedAdmissible S a) :
    let x : ℕ → ℝ := fun p => (a p : ℝ)
    phi S x - baseline S =
      terminalCost (clock S x) - terminalCost (theta S) + tailCost S a ∧
    linearCost S (g (theta S)) a =
      phi S x - baseline S + tangentRemainder (theta S) (clock S x) := by
  let x : ℕ → ℝ := fun p => (a p : ℝ)
  have hbenefit : (∑ p ∈ S, benefit (p : ℝ) (x p)) =
      -tailCost S a - ∑ p ∈ S, log (1 - (p : ℝ) ^ (-1 : ℝ)) := by
    calc
      _ = ∑ p ∈ S, (-eulerTerm p (a p) - log (1 - (p : ℝ) ^ (-1 : ℝ))) := by
        apply sum_congr rfl
        intro p hp
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
        have ha1 : (1 : ℝ) ≤ x p := by
          dsimp only [x]
          exact_mod_cast ha p hp
        rw [benefit_log hp1 ha1]
        dsimp only [x, probability, eulerTerm]
        rw [show (a p : ℝ) + 1 = ((a p + 1 : ℕ) : ℝ) by simp,
          rpow_neg (Nat.cast_nonneg p : (0 : ℝ) ≤ p), rpow_natCast]
        simp only [one_div, neg_neg]
      _ = _ := by rw [sum_sub_distrib, sum_neg_distrib]; rfl
  have hclock : clock S x = theta S + clockIncrement S a := by
    unfold clock theta clockIncrement
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    dsimp only [x]
    ring
  have hlin : linearCost S (g (theta S)) a =
      g (theta S) * clockIncrement S a + tailCost S a := by
    simp only [linearCost, clockIncrement, tailCost, mul_sum, sum_add_distrib, mul_assoc]
  have hobj : phi S x - baseline S =
      terminalCost (clock S x) - terminalCost (theta S) + tailCost S a := by
    unfold phi baseline
    rw [hbenefit]
    ring
  refine ⟨hobj, ?_⟩
  change linearCost S (g (theta S)) a = phi S x - baseline S + _
  rw [hlin, hobj, tangentRemainder, hclock]
  ring

/-- Sublevel estimate comparing the infima of the full admissible integer
cost images at the nonlinear clock and at its tangent price. -/
private theorem integer_fixed_price_envelope {S : Finset ℕ} (hS : primeSupport S)
    (hcard : 3 ≤ S.card) (hlog : 1 ≤ log (theta S)) {r : ℝ} (hr : 0 < r) :
    let B := theta S
    let L := log B
    let V := fixedPriceMinimum S (g B)
    let A := exp (L * (exp r - 1)) - 1
    min r (V - A ^ 2 / L) ≤ integerInfimum S ∧ integerInfimum S ≤ V := by
  let B := theta S
  let L := log B
  let A := exp (L * (exp r - 1)) - 1
  let V := fixedPriceMinimum S (g B)
  change min r (V - A ^ 2 / L) ≤ integerInfimum S ∧ integerInfimum S ≤ V
  have hH : 1 < B := theta_gt_one hS hcard
  have hB0 : 0 < B := zero_lt_one.trans hH
  have hL0 : 0 < L := log_pos hH
  let linearValues : Set ℝ :=
    {v | ∃ a : ℕ → ℕ, supportedAdmissible S a ∧ linearCost S (g B) a = v}
  have hprice : 0 < g B := one_div_pos.mpr (mul_pos hB0 hL0)
  have honeVector : supportedAdmissible S (fun _ => 1) := fun _ _ => le_rfl
  have hlinearNonempty : linearValues.Nonempty :=
    ⟨linearCost S (g B) (fun _ => 1), ⟨fun _ => 1, honeVector, rfl⟩⟩
  have hlinearBounded : BddBelow linearValues := by
    refine ⟨0, ?_⟩
    rintro v ⟨a, ha, rfl⟩
    change 0 ≤ linearCost S (g B) a
    unfold linearCost
    apply sum_nonneg
    intro p hp
    have haR : (1 : ℝ) ≤ a p := by exact_mod_cast ha p hp
    exact add_nonneg (mul_nonneg (mul_nonneg hprice.le (sub_nonneg.mpr haR))
      (hS p hp).log_pos.le) (eulerTerm_le_twice_power (hS p hp)).1
  have hadm (a : ℕ → ℕ) (ha : supportedAdmissible S a) :
      admissible S (fun p => (a p : ℝ)) := by
    intro p hp
    change (1 : ℝ) ≤ (a p : ℝ)
    exact_mod_cast ha p hp
  have hT (a : ℕ → ℕ) (ha : supportedAdmissible S a) :
      B ≤ clock S (fun p => (a p : ℝ)) := theta_le_clock hS (hadm a ha)
  have htail (a : ℕ → ℕ) : 0 ≤ tailCost S a :=
    sum_nonneg (fun p hp => (eulerTerm_le_twice_power (hS p hp)).1)
  have hbounded : BddBelow (integerValues S) := by
    refine ⟨0, ?_⟩
    rintro v ⟨a, ha, rfl⟩
    have hlogT := log_le_log hB0 (hT a ha)
    have htt := log_le_log hL0 hlogT
    have hforms := (integer_loss_forms hS ha).1
    change terminalCost B ≤ terminalCost (clock S (fun p => (a p : ℝ))) at htt
    linarith only [hforms, htt, htail a]
  have hnonempty : (integerValues S).Nonempty :=
    ⟨phi S (fun _ => ((1 : ℕ) : ℝ)) - baseline S, ⟨fun _ => 1, honeVector, rfl⟩⟩
  constructor
  · change min r (V - A ^ 2 / L) ≤ sInf (integerValues S)
    apply le_csInf hnonempty
    rintro v ⟨a, ha, rfl⟩
    let T := clock S (fun p => (a p : ℝ))
    let D := phi S (fun p => (a p : ℝ)) - baseline S
    change min r (V - A ^ 2 / L) ≤ D
    by_cases hlarge : r ≤ D
    · exact (min_le_left _ _).trans hlarge
    · have hrem : tangentRemainder B T ≤ A ^ 2 / L :=
        fixed_price_tangent_bound hS hcard hlog hr (hadm a ha) (lt_of_not_ge hlarge)
      have hv : V ≤ linearCost S (g B) a :=
        csInf_le hlinearBounded (show linearCost S (g B) a ∈ linearValues from ⟨a, ha, rfl⟩)
      have hid : linearCost S (g B) a = D + tangentRemainder B T :=
        (integer_loss_forms hS ha).2
      exact (min_le_right _ _).trans (by linarith only [hv, hid, hrem])
  · change integerInfimum S ≤ sInf linearValues
    apply le_csInf hlinearNonempty
    rintro v ⟨a, ha, rfl⟩
    have hmem : phi S (fun p => (a p : ℝ)) - baseline S ∈ integerValues S :=
      ⟨a, ha, rfl⟩
    have hid := (integer_loss_forms hS ha).2
    have hrem := (tangent_remainder_nonnegative hH (hH.trans_le (hT a ha))).1
    exact (csInf_le hbounded hmem).trans (by linarith only [hid, hrem])

/-- The existing integer second-order theorem implies that the full infimum is
little-o of the sublevel radius `1 / sqrt H`. -/
private theorem sqrt_H_mul_integerInfimum_tendsto_zero :
    Tendsto (fun P : ℕ => sqrt (H P) * I P) atTop (𝓝 0) := by
  have h₂ := IntegerInfimumSecondOrder.actual_integer_infimum_second_order
  have h₁ : Tendsto (fun P : ℕ => sqrt (H P) * ℓ P * I P - 2 * sqrt 2)
      atTop (𝓝 0) := by
    apply (h₂.div_atTop prefixEll_atTop).congr'
    filter_upwards [prefixEll_atTop.eventually_gt_atTop 0] with P hP
    exact mul_div_cancel_left₀ _ hP.ne'
  have h₀ := h₁.add_const (2 * sqrt 2)
  simp only [sub_add_cancel, zero_add] at h₀
  apply (h₀.div_atTop prefixEll_atTop).congr'
  filter_upwards [prefixEll_atTop.eventually_gt_atTop 0] with P hP
  field_simp [hP.ne'] <;> ring

private def radius (P : ℕ) : ℝ := 1 / sqrt (H P)

private theorem eventually_integerInfimum_lt_radius : ∀ᶠ P in atTop, I P < radius P := by
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1,
    sqrt_H_mul_integerInfimum_tendsto_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
    with P hB hI
  apply (lt_div_iff₀ (sqrt_pos.2 (zero_lt_one.trans hB))).2
  simpa only [mul_comm] using hI

private theorem eventually_small_radius : ∀ᶠ P in atTop, 2 * ℓ P * radius P ≤ 1 := by
  have h := (log_pow_over_H_rpow 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2
  rw [mul_zero] at h
  filter_upwards [h.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with P hP
  calc
    2 * ℓ P * radius P = 2 * (ℓ P ^ 1 / (H P) ^ (1 / 2 : ℝ)) := by
      rw [pow_one, ← sqrt_eq_rpow, radius]
      ring
    _ ≤ 1 := hP.le

lemma exp_sub_one_bounds {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ exp x - 1 ∧ exp x - 1 ≤ 2 * x := by
  have hpos : 0 ≤ exp x - 1 := sub_nonneg.mpr (by simpa only [exp_zero] using exp_le_exp.mpr hx)
  refine ⟨hpos, ?_⟩
  have h := abs_exp_sub_one_le (show |x| ≤ 1 by simpa only [abs_of_nonneg hx] using hx1)
  simpa only [abs_of_nonneg hx, abs_of_nonneg hpos] using h

/-- The tangent error of the exact envelope, after the sublevel branch is
eliminated by the existing integer second-order limit. -/
private theorem eventually_tangent_bounds : ∀ᶠ P : ℕ in atTop,
    let D := fixedPriceMinimum (Nat.primesLE P) (prefixPrice P) - I P
    0 ≤ D ∧ D ≤ 16 * ℓ P / H P := by
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1, eventual_prefix_domains,
    eventually_integerInfimum_lt_radius, eventually_small_radius] with P hB hdomain hI hrscale
  let S := Nat.primesLE P
  let L := ℓ P
  let B := H P
  let r := radius P
  let V := fixedPriceMinimum S (prefixPrice P)
  let w := L * (exp r - 1)
  let A := exp w - 1
  change 0 ≤ V - I P ∧ V - I P ≤ 16 * L / B
  obtain ⟨hS, hcard, hlog, _⟩ := hdomain
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hL0 : 0 < L := log_pos hB
  have hr : 0 < r := one_div_pos.mpr (sqrt_pos.2 hB0)
  have hr1 : r ≤ 1 := by
    have hs : (1 : ℝ) < sqrt B :=
      (lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2 (by simpa only [one_pow] using hB)
    exact (div_le_iff₀ (sqrt_pos.2 hB0)).2 (by simpa only [one_mul] using hs.le)
  have henv := integer_fixed_price_envelope hS hcard hlog hr
  change min r (V - A ^ 2 / L) ≤ I P ∧ I P ≤ V at henv
  have hV : V - A ^ 2 / L ≤ I P :=
    (min_le_iff.mp henv.1).resolve_left (not_le_of_gt hI)
  have her := exp_sub_one_bounds hr.le hr1
  have hw0 : 0 ≤ w := mul_nonneg hL0.le her.1
  have hw2 : w ≤ 2 * L * r := by
    dsimp only [w]
    nlinarith only [mul_le_mul_of_nonneg_left her.2 hL0.le]
  have hA := exp_sub_one_bounds hw0 (hw2.trans hrscale)
  have hA4 : A ≤ 4 * L * r := by
    change exp w - 1 ≤ 4 * L * r
    linarith only [hA.2, hw2]
  have hr2 : r ^ 2 = 1 / B := by
    dsimp only [r, radius, B]
    rw [div_pow, one_pow, sq_sqrt hB0.le]
  have herror : A ^ 2 / L ≤ 16 * L / B := by
    calc
      _ ≤ (4 * L * r) ^ 2 / L := div_le_div_of_nonneg_right
        ((sq_le_sq₀ hA.1 (by positivity)).2 hA4) hL0.le
      _ = 16 * L * r ^ 2 := by field_simp [hL0.ne'] <;> ring
      _ = _ := by rw [hr2]; ring
  exact ⟨sub_nonneg.mpr henv.2, by linarith only [hV, herror]⟩

/-- Quantitative approximation of the entire nonlinear integer infimum by
exact finite subtraction at the common prefix price. -/
private theorem eventually_all_fixed_layers_bound {m : ℕ} (hm : 2 ≤ m) :
    ∀ᶠ P : ℕ in atTop,
      |I P - reciprocalLayers (Nat.primesLE P) (prefixPrice P) m| ≤
        (16 + 2 * (m : ℝ)) * ℓ P / H P +
          remainderConstant / (H P) ^ ((m : ℝ) / ((m : ℝ) + 1)) := by
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1, prefixEll_atTop.eventually_ge_atTop 1,
    eventually_tangent_bounds] with P hB hlog hD
  let S := Nat.primesLE P
  let lam := prefixPrice P
  let V := fixedPriceMinimum S lam
  let A := reciprocalLayers S lam m
  let B := exactLayers S lam m
  have hS : primeSupport S := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hE := retained_layers_bounds hS hB hm
  have hR := omitted_layers_aggregate hS hB hlog hm
  change 0 ≤ A - B ∧ A - B ≤ 2 * ((m : ℝ) - 1) / H P at hE
  change 0 ≤ V - B ∧ V - B ≤
    remainderConstant / (H P) ^ ((m : ℝ) / ((m : ℝ) + 1)) at hR
  change 0 ≤ V - I P ∧ V - I P ≤ 16 * ℓ P / H P at hD
  have hterm : 2 * ((m : ℝ) - 1) / H P ≤ 2 * (m : ℝ) * ℓ P / H P := by
    apply div_le_div_of_nonneg_right _ (zero_lt_one.trans hB).le
    nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) m)
      (sub_nonneg.mpr (show 1 ≤ ℓ P from hlog))]
  have hmain : 0 ≤ (16 + 2 * (m : ℝ)) * ℓ P / H P :=
    div_nonneg (mul_nonneg (by positivity) (log_pos hB).le) (zero_lt_one.trans hB).le
  have htail : 0 ≤ remainderConstant / (H P) ^ ((m : ℝ) / ((m : ℝ) + 1)) :=
    hR.1.trans hR.2
  have hid : I P - A = (V - B) - (A - B) - (V - I P) := by ring
  change |I P - A| ≤ _
  rw [hid, abs_le]
  constructor
  · have hsplit : (16 + 2 * (m : ℝ)) * ℓ P / H P =
        16 * ℓ P / H P + 2 * (m : ℝ) * ℓ P / H P := by ring
    linarith only [hsplit, hR.1, hE.2, hD.2, hterm, htail]
  · linarith only [hR.2, hE.1, hD.1, hmain]

/-- For each fixed `m ≥ 2`, the retained reciprocal-power layers approximate
the full integer Robin infimum at the scale of its `m`th layer. -/
theorem actual_integer_infimum_all_fixed_layers {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun P : ℕ =>
      (prefixH P) ^ (((m : ℝ) - 1) / (m : ℝ)) * log (prefixH P) *
        (integerInfimum (Nat.primesLE P) -
          ∑ j ∈ Finset.Ioc 1 m, ∑ p ∈ Nat.primesLE P,
            min (prefixPrice P * log (p : ℝ)) (1 / (p : ℝ) ^ j)))
      atTop (𝓝 0) := by
  let t : ℝ := (m : ℝ)
  let a : ℝ := (t - 1) / t
  let b : ℝ := t / (t + 1)
  let d : ℝ := 1 / t
  let e : ℝ := 1 / (t * (t + 1))
  let M : ℝ := 16 + 2 * t
  have ht : 0 < t := by dsimp [t]; exact_mod_cast (by omega : 0 < m)
  have ht1 : 0 < t + 1 := by positivity
  have hd : 0 < d := one_div_pos.mpr ht
  have he : 0 < e := one_div_pos.mpr (mul_pos ht ht1)
  have ha : a - 1 = -d := by dsimp only [a, d]; field_simp [ht.ne'] <;> ring
  have hab : a - b = -e := by dsimp only [a, b, e]; field_simp [ht.ne', ht1.ne'] <;> ring
  have hmajor := ((log_pow_over_H_rpow 2 hd).const_mul M).add
    ((log_pow_over_H_rpow 1 he).const_mul remainderConstant)
  simp only [mul_zero, zero_add, pow_one] at hmajor
  change Tendsto (fun P : ℕ => (H P) ^ a * ℓ P *
    (I P - reciprocalLayers (Nat.primesLE P) (prefixPrice P) m)) atTop (𝓝 0)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_all_fixed_layers_bound hm, prefixH_atTop.eventually_gt_atTop 1]
    with P hP hB
  have hB0 := zero_lt_one.trans hB
  have hL0 := log_pos hB
  have hW : 0 ≤ (H P) ^ a * ℓ P := mul_nonneg (rpow_nonneg hB0.le _) hL0.le
  have hleft : (H P) ^ a / H P = 1 / (H P) ^ d := by
    calc
      _ = (H P) ^ (a - 1) := by
        rw [rpow_sub hB0, rpow_one]
      _ = _ := by rw [ha, rpow_neg hB0.le, one_div]
  have hright : (H P) ^ a / (H P) ^ b = 1 / (H P) ^ e := by
    rw [← rpow_sub hB0, hab, rpow_neg hB0.le, one_div]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hW]
  calc
    _ ≤ (H P) ^ a * ℓ P *
        (M * ℓ P / H P + remainderConstant / (H P) ^ b) :=
      mul_le_mul_of_nonneg_left hP hW
    _ = M * ℓ P ^ 2 * ((H P) ^ a / H P) +
        remainderConstant * ℓ P * ((H P) ^ a / (H P) ^ b) := by ring
    _ = _ := by rw [hleft, hright]; ring

/-- At the scale of layer `m`, the residual after subtracting layers two through
`m - 1` has the same limit as layer `m` at the exact prefix price.
For `m = 2` the lower-layer sum is empty. -/
theorem actual_integer_infimum_fixed_layer_residual {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun P : ℕ =>
      prefixH P ^ (((m : ℝ) - 1) / (m : ℝ)) * prefixEll P *
        (integerInfimum (Nat.primesLE P) -
          ∑ j ∈ Finset.Ioc 1 (m - 1), activationLayer j P))
      atTop (𝓝 (((m : ℝ) / ((m : ℝ) - 1)) * (m : ℝ) ^ (1 / (m : ℝ)))) := by
  let scale : ℕ → ℝ := fun P => prefixH P ^ (((m : ℝ) - 1) / (m : ℝ)) * prefixEll P
  have happrox : Tendsto (fun P : ℕ => scale P *
      (integerInfimum (Nat.primesLE P) - ∑ j ∈ Finset.Ioc 1 m, activationLayer j P))
      atTop (𝓝 0) :=
    actual_integer_infimum_all_fixed_layers hm
  have hlimit := happrox.add (activation_layer_tendsto m hm)
  rw [zero_add] at hlimit
  apply hlimit.congr
  intro P
  have hprev : 1 ≤ m - 1 := by omega
  have hsucc : (m - 1) + 1 = m := Nat.sub_add_cancel (by omega)
  have hsplit : (∑ j ∈ Finset.Ioc 1 m, activationLayer j P) =
      (∑ j ∈ Finset.Ioc 1 (m - 1), activationLayer j P) + activationLayer m P := by
    have htop := Finset.sum_Ioc_succ_top hprev (fun j => activationLayer j P)
    simpa only [hsucc] using htop
  change scale P * (integerInfimum (Nat.primesLE P) -
      (∑ j ∈ Finset.Ioc 1 m, activationLayer j P)) + scale P * activationLayer m P =
    scale P * (integerInfimum (Nat.primesLE P) -
      (∑ j ∈ Finset.Ioc 1 (m - 1), activationLayer j P))
  rw [hsplit]
  ring

end D5.S3.Arith.Robin.PriceRecord.FixedLayerAggregate
