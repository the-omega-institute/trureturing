/- GID: D5/S3/PrimeGaps/SmoothCovers
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the smooth-number count and the greedy cover parameters. -/

/- Ported from openai/LongGapsBetweenPrimes commit 8f5fa88c88b4750028c05b66b081d56a92418054.
   Modified by trureturing on 2026-09-04: repository routing and module split. -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import D5.S3.PrimeGaps.ShortTranslateClosure

namespace LongGapsBetweenPrimes

noncomputable section

/-- A uniform geometric factor for the smooth-number estimate. -/
def smoothEulerConstant : ℝ := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

/-- The smooth Euler constant is positive. -/
lemma smoothEulerConstant_pos : 0 < smoothEulerConstant := by
  exact inv_pos.mpr (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)))

/-- The scale constant used to choose the smoothness cutoff and tilt. -/
def smoothScaleConstant : ℝ := 3 * smoothEulerConstant + 10

/-- The smoothness scale constant is positive. -/
lemma smoothScaleConstant_pos : 0 < smoothScaleConstant := by
  unfold smoothScaleConstant
  linarith [smoothEulerConstant_pos]

/-- Bound the cost of shifting an Euler factor to exponent `1 - t`. -/
lemma euler_factor_left_comparison {p t : ℝ} (hp : 2 ≤ p) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    (1 - p ^ (-(1 - t)))⁻¹ ≤ (1 - p ^ (-(1 : ℝ)))⁻¹ *
      Real.exp (smoothEulerConstant * (p ^ t - 1) / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hpow : p ^ (-(1 - t)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ p ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by norm_num)
  have hcden : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hden : 0 < 1 - p ^ (-(1 - t)) := by linarith
  have hnum : 0 ≤ p ^ t - 1 := sub_nonneg.mpr (Real.one_le_rpow hp1 ht)
  have hsplit : p ^ (-(1 - t)) = p ^ t / p := by
    rw [show -(1 - t) = t + -1 by ring, Real.rpow_add hp0, Real.rpow_neg_one,
      div_eq_mul_inv]
  have he : (1 - p⁻¹) * (1 - p ^ (-(1 - t)))⁻¹ =
      1 + ((p ^ t - 1) / p) / (1 - p ^ (-(1 - t))) := by
    have hpt : p ^ t < p := (div_lt_one hp0).mp (by rw [← hsplit]; linarith)
    rw [hsplit]
    field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hpt)]
    ring
  have hratio : (1 - p⁻¹) * (1 - p ^ (-(1 - t)))⁻¹ ≤
      Real.exp (smoothEulerConstant * (p ^ t - 1) / p) := by
    rw [he]
    calc
      _ ≤ 1 + ((p ^ t - 1) / p) / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
        exact add_le_add le_rfl
          (div_le_div_of_nonneg_left (div_nonneg hnum hp0.le) hcden (by linarith))
      _ = 1 + smoothEulerConstant * (p ^ t - 1) / p := by
        unfold smoothEulerConstant
        ring
      _ ≤ _ := by simpa only [add_comm] using
        Real.add_one_le_exp (smoothEulerConstant * (p ^ t - 1) / p)
  rw [Real.rpow_neg_one, inv_mul_eq_div]
  apply (le_div_iff₀ (show 0 < 1 - p⁻¹ by
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith)))).mpr
  simpa only [mul_comm] using hratio

/-- Bound the cost of shifting the Euler product to exponent `1 - t`. -/
lemma eulerProduct_left_comparison (N : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    eulerProduct N (1 - t) ≤ eulerProduct N 1 *
      Real.exp (smoothEulerConstant * ∑ p ∈ N.primesLE, ((p : ℝ) ^ t - 1) / p) := by
  unfold eulerProduct
  calc
    _ ≤ ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ *
        Real.exp (smoothEulerConstant * ((p : ℝ) ^ t - 1) / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)).le)
      · intro p hp
        exact euler_factor_left_comparison
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) ht ht'
    _ = _ := by
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- A secant bound controls `p ^ t - 1` using the ratio `log p / log z`. -/
lemma rpow_secant_log {p z t : ℝ} (hp : 1 ≤ p) (hpz : p ≤ z) (hz : 1 < z)
    (ht : 0 ≤ t) : p ^ t - 1 ≤ (Real.log p / Real.log z) * (Real.exp (t * Real.log z) - 1) := by
  rcases ht.eq_or_lt with rfl | _
  · simp
  have hlogz := Real.log_pos hz
  have hratio : Real.log p / Real.log z ≤ 1 :=
    (div_le_one hlogz).mpr (Real.log_le_log (zero_lt_one.trans_le hp) hpz)
  have h := convexOn_exp.2 (Set.mem_univ (t * Real.log z)) (Set.mem_univ 0)
    (div_nonneg (Real.log_nonneg hp) hlogz.le) (sub_nonneg.mpr hratio)
    (show Real.log p / Real.log z + (1 - Real.log p / Real.log z) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have harg : Real.log p / Real.log z * (t * Real.log z) = Real.log p * t := by
    field_simp
  rw [harg, ← Real.rpow_def_of_pos (zero_lt_one.trans_le hp)] at h
  linarith

/-- Bound the shifted Euler product using the tilt and the largest prime cutoff. -/
lemma eulerProduct_left_bound {N : ℕ} {z t : ℝ} (hN : 2 ≤ N) (hNz : (N : ℝ) ≤ z)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    eulerProduct N (1 - t) ≤ eulerProduct N 1 *
      Real.exp (3 * smoothEulerConstant * Real.exp (t * Real.log z)) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hz : 1 < z := by linarith
  have hlogz := Real.log_pos hz
  have hlogN : Real.log N ≤ Real.log z :=
    Real.log_le_log (by linarith) hNz
  have hlog4 : Real.log 4 ≤ 2 * Real.log z := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ z ^ 2 by nlinarith)
  have hlogs : (∑ p ∈ N.primesLE, Real.log p / p) ≤ 3 * Real.log z := by
    linarith [sum_prime_log_div_le (by omega : 1 ≤ N)]
  have hsum : (∑ p ∈ N.primesLE, ((p : ℝ) ^ t - 1) / p) ≤
      3 * Real.exp (t * Real.log z) := by
    calc
      _ ≤ ∑ p ∈ N.primesLE,
          (Real.log p / p) * (Real.exp (t * Real.log z) / Real.log z) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpN, hp⟩ := Nat.mem_primesLE.mp hp
        calc
          _ ≤ (Real.log p / Real.log z) * (Real.exp (t * Real.log z) - 1) / p :=
            div_le_div_of_nonneg_right
              (rpow_secant_log (by exact_mod_cast hp.one_lt.le)
                ((by exact_mod_cast hpN : (p : ℝ) ≤ N).trans hNz) hz ht)
              (Nat.cast_nonneg p)
          _ ≤ (Real.log p / Real.log z) * Real.exp (t * Real.log z) / p := by
            gcongr
            exact sub_le_self _ zero_le_one
          _ = _ := by ring
      _ = (∑ p ∈ N.primesLE, Real.log p / p) *
          (Real.exp (t * Real.log z) / Real.log z) := (Finset.sum_mul ..).symm
      _ ≤ (3 * Real.log z) * (Real.exp (t * Real.log z) / Real.log z) :=
        mul_le_mul_of_nonneg_right hlogs (by positivity)
      _ = 3 * Real.exp (t * Real.log z) := by field_simp
  apply (eulerProduct_left_comparison N ht ht').trans
  apply mul_le_mul_of_nonneg_left _ (eulerProduct_pos N (by norm_num)).le
  apply Real.exp_le_exp.mpr
  simpa [mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hsum smoothEulerConstant_pos.le

/-- A finite Euler-product bound for the count of smooth integers up to `H`. -/
lemma smooth_count_rankin {N H : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 H)
    (hsmooth : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (S.card : ℝ) ≤ (H : ℝ) ^ σ * eulerProduct N σ := by
  have hsum := sum_smooth_le_eulerProduct hσ S hsmooth
  have hpoint (n : ℕ) (hn : n ∈ S) : (1 : ℝ) ≤ (H : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by
    have hnI := Finset.mem_Icc.mp (hS hn)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnH : (n : ℝ) ≤ H := by exact_mod_cast hnI.2
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hn0 σ)).mpr
      (by simpa only [one_mul] using Real.rpow_le_rpow hn0.le hnH hσ.le)
  calc
    (S.card : ℝ) = ∑ _n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, (H : ℝ) ^ σ * (n : ℝ) ^ (-σ) := Finset.sum_le_sum hpoint
    _ = (H : ℝ) ^ σ * ∑ n ∈ S, (n : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg H) σ)

/-- The logarithmic smoothness cutoff in the covering construction. -/
def coverLogZ (x : ℝ) : ℝ :=
  Real.log x * Real.log (Real.log (Real.log x)) /
    (smoothScaleConstant * Real.log (Real.log x))

/-- The smoothness cutoff in the covering construction, rounded down to an integer. -/
def coverZ (x : ℝ) : ℕ := ⌊Real.exp (coverLogZ x)⌋₊

/-- The small-prime cutoff, given by the integer part of `(log x)^4`. -/
def coverW (x : ℝ) : ℕ := ⌊(Real.log x) ^ 4⌋₊

/-- The Rankin tilt used to count smooth integers. -/
def coverTilt (x : ℝ) : ℝ := smoothScaleConstant * Real.log (Real.log x) / Real.log x

/-- The integer interval length targeted by the covering argument. -/
def coverLength (η x : ℝ) : ℕ :=
  ⌊η * x * Real.log x ^ 2 * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) ^ 2⌋₊

/-- The smoothness scale constant exceeds ten. -/
lemma smoothScaleConstant_gt_ten : 10 < smoothScaleConstant := by
  unfold smoothScaleConstant
  linarith [smoothEulerConstant_pos]

/-- The covering tilt times the logarithmic cutoff equals the third iterated logarithm. -/
lemma coverTilt_mul_coverLogZ {x : ℝ} (hx : 1 < x) (hlog : 1 < Real.log x) :
    coverTilt x * coverLogZ x = Real.log (Real.log (Real.log x)) := by
  have hl1 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hl2 : Real.log (Real.log x) ≠ 0 := (Real.log_pos hlog).ne'
  unfold coverTilt coverLogZ
  field_simp [hl1, hl2, smoothScaleConstant_pos.ne']

/-- The size, ordering, and tilt bounds for the covering parameters hold eventually. -/
lemma eventually_cover_parameters : ∀ᶠ x : ℝ in Filter.atTop,
    2 ≤ x ∧ 2 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x) ∧ 1 ≤ Real.log (Real.log (Real.log x)) ∧
    4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 ≤ Real.log x ∧
    0 ≤ coverTilt x ∧ coverTilt x ≤ 1 / 2 ∧
    4 * Real.log (Real.log x) ≤ coverLogZ x ∧ coverLogZ x ≤ Real.log x := by
  have hlog := Real.tendsto_log_atTop
  have hloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x))
      Filter.atTop Filter.atTop := hlog.comp hlog
  have hlogloglog : Filter.Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x)))
      Filter.atTop Filter.atTop := hlog.comp hloglog
  have hsmall : Filter.Tendsto
      (fun x : ℝ => 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 / Real.log x)
      Filter.atTop (nhds 0) := by
    simpa [mul_div_assoc] using ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      hlog).const_mul (4 * smoothScaleConstant)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ), hlog.eventually_ge_atTop 2,
    hloglog.eventually_ge_atTop 1, hlogloglog.eventually_ge_atTop 1,
    hsmall.eventually_le_const zero_lt_one] with x hx hl hll hlll hsmall
  have hl0 : 0 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hquad : 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 ≤ Real.log x :=
    (div_le_one hl0).mp hsmall
  have hlinear : 4 * smoothScaleConstant * Real.log (Real.log x) ≤ Real.log x := by
    calc
      _ ≤ 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith)
          (mul_nonneg (by norm_num) smoothScaleConstant_pos.le)
      _ ≤ _ := hquad
  refine ⟨hx, hl, hll, hlll, hquad, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg smoothScaleConstant_pos.le hll0.le) hl0.le
  · unfold coverTilt
    apply (div_le_iff₀ hl0).mpr
    nlinarith
  · unfold coverLogZ
    apply (le_div_iff₀ (mul_pos smoothScaleConstant_pos hll0)).mpr
    calc
      _ = 4 * smoothScaleConstant * Real.log (Real.log x) ^ 2 := by ring
      _ ≤ Real.log x := hquad
      _ ≤ Real.log x * Real.log (Real.log (Real.log x)) :=
        le_mul_of_one_le_right hl0.le hlll
  · unfold coverLogZ
    apply (div_le_iff₀ (mul_pos smoothScaleConstant_pos hll0)).mpr
    apply mul_le_mul_of_nonneg_left _ hl0.le
    calc
      _ ≤ Real.log (Real.log x) := by
        linarith [Real.log_le_sub_one_of_pos hll0]
      _ ≤ smoothScaleConstant * Real.log (Real.log x) :=
        le_mul_of_one_le_left hll0.le (by linarith [smoothScaleConstant_gt_ten])

/-- The small-prime cutoff does not exceed the smoothness cutoff. -/
lemma coverW_le_coverZ {x : ℝ} (hx : 1 < x)
    (hz : 4 * Real.log (Real.log x) ≤ coverLogZ x) : coverW x ≤ coverZ x := by
  apply Nat.floor_mono
  calc
    (Real.log x) ^ 4 = Real.exp ((4 : ℕ) * Real.log (Real.log x)) := by
      rw [Real.exp_nat_mul, Real.exp_log (Real.log_pos hx)]
    _ ≤ Real.exp (coverLogZ x) := Real.exp_le_exp.mpr hz

/-- The smoothness cutoff is at most the integer part of `x`. -/
lemma coverZ_le_floor {x : ℝ} (hx : 0 < x) (hz : coverLogZ x ≤ Real.log x) : coverZ x ≤ ⌊x⌋₊ := by
  exact Nat.floor_mono ((Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hx))

/-- The small-prime cutoff is at least two when `log x ≥ 2`. -/
lemma coverW_ge_two {x : ℝ} (hL : 2 ≤ Real.log x) : 2 ≤ coverW x := by
  apply Nat.le_floor
  exact (by norm_num : (2 : ℝ) ≤ 2 ^ 4).trans
    (pow_le_pow_left₀ (by norm_num) hL 4)

/-- Eventually, at most `H / (log x)^3` integers up to `H` are `coverZ x`-smooth. -/
lemma eventually_smooth_count : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x ≤ H → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H →
    (∀ n ∈ S, ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x) →
    (S.card : ℝ) ≤ (H : ℝ) / Real.log x ^ 3 := by
  filter_upwards [eventually_cover_parameters,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 2]
    with x hparameters hlarge
  simp only [Function.comp_apply] at hlarge
  obtain ⟨hx, hl, hll, _, _, ht, ht', hZlow, hZhigh⟩ := hparameters
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hl1 : 1 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hZ : 2 ≤ coverZ x :=
    (coverW_ge_two hl).trans (coverW_le_coverZ hx1 hZlow)
  have hlogZ : Real.log (coverZ x) ≤ Real.log x :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < coverZ x))
      ((by exact_mod_cast coverZ_le_floor hx0 hZhigh : (coverZ x : ℝ) ≤ ⌊x⌋₊).trans
        (Nat.floor_le hx0.le))
  have hEulerOne : eulerProduct (coverZ x) 1 ≤
      Real.exp (7 * Real.log (Real.log x)) := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log (coverZ x)) := eulerProduct_one_le hZ
      _ ≤ Real.exp 6 * Real.log x ^ 2 := by
        gcongr
        nlinarith
      _ = Real.exp (6 + 2 * Real.log (Real.log x)) := by
        rw [Real.exp_add, show Real.exp (2 * Real.log (Real.log x)) =
          Real.log x ^ 2 by
            simpa [Real.exp_log hl0] using Real.exp_nat_mul (Real.log (Real.log x)) 2]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hEuler : eulerProduct (coverZ x) (1 - coverTilt x) ≤
      Real.exp ((smoothScaleConstant - 3) * Real.log (Real.log x)) := by
    have hbound := eulerProduct_left_bound hZ
      (Nat.floor_le (Real.exp_pos (coverLogZ x)).le) ht ht'
    rw [Real.log_exp, coverTilt_mul_coverLogZ hx1 hl1, Real.exp_log hll0] at hbound
    calc
      _ ≤ eulerProduct (coverZ x) 1 *
          Real.exp (3 * smoothEulerConstant * Real.log (Real.log x)) := hbound
      _ ≤ Real.exp (7 * Real.log (Real.log x)) *
          Real.exp (3 * smoothEulerConstant * Real.log (Real.log x)) := by
        gcongr
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        unfold smoothScaleConstant
        ring
  intro H hxH S hS hsmooth
  have hH0 : 0 < (H : ℝ) := hx0.trans_le hxH
  have hpower : (H : ℝ) ^ (1 - coverTilt x) ≤
      H * Real.exp (-smoothScaleConstant * Real.log (Real.log x)) := by
    rw [sub_eq_add_neg, Real.rpow_add hH0, Real.rpow_one]
    apply mul_le_mul_of_nonneg_left _ hH0.le
    calc
      _ ≤ x ^ (-coverTilt x) := Real.rpow_le_rpow_of_nonpos hx0 hxH (neg_nonpos.mpr ht)
      _ = _ := by
        rw [Real.rpow_def_of_pos hx0]
        congr 1
        unfold coverTilt
        field_simp
  calc
    (S.card : ℝ) ≤ (H : ℝ) ^ (1 - coverTilt x) *
        eulerProduct (coverZ x) (1 - coverTilt x) := by
      apply smooth_count_rankin (by linarith) S hS
      intro n hn
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp (hS hn)).1; omega
      apply Nat.mem_smoothNumbers.mpr
      refine ⟨hn0, ?_⟩
      intro p hp
      obtain ⟨hp, hpn⟩ := (Nat.mem_primeFactorsList hn0).mp hp
      exact Nat.lt_succ_of_le (hsmooth n hn p hp hpn)
    _ ≤ (H * Real.exp (-smoothScaleConstant * Real.log (Real.log x))) *
        Real.exp ((smoothScaleConstant - 3) * Real.log (Real.log x)) :=
      mul_le_mul hpower hEuler (eulerProduct_pos _ (by linarith)).le (by positivity)
    _ = (H : ℝ) / Real.log x ^ 3 := by
      rw [mul_assoc, ← Real.exp_add,
        show -smoothScaleConstant * Real.log (Real.log x) +
          (smoothScaleConstant - 3) * Real.log (Real.log x) =
          -(3 * Real.log (Real.log x)) by ring,
        Real.exp_neg, show Real.exp (3 * Real.log (Real.log x)) = Real.log x ^ 3 by
          simpa [Real.exp_log hl0] using Real.exp_nat_mul (Real.log (Real.log x)) 3,
        div_eq_mul_inv]

/-- A logarithmic upper bound for the product of greedy survival factors. -/
lemma greedy_product_le {W Z : ℕ} (hW : 2 ≤ W) (hWZ : W ≤ Z) :
    (∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ))) ≤
      Real.exp 6 * (1 + Real.log W) / Real.log Z := by
  have hprod : 0 < ∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    simpa only [one_div] using sub_pos.mpr
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (auxiliaryPrimes_prime hp).one_lt))
  have hfactor := auxiliary_euler_factorization hWZ 1
  simp only [Real.rpow_neg_one] at hfactor
  rw [Finset.prod_inv_distrib, inv_mul_eq_div] at hfactor
  simp only [← one_div] at hfactor
  have hcancel := (div_eq_iff hprod.ne').mp hfactor
  have hlog : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  apply (le_div_iff₀ hlog).mpr
  calc
    _ ≤ (∏ p ∈ auxiliaryPrimes W Z, (1 - 1 / (p : ℝ))) * eulerProduct Z 1 :=
      mul_le_mul_of_nonneg_left (log_le_eulerProduct_one Z) hprod.le
    _ = eulerProduct W 1 := (mul_comm _ _).trans hcancel.symm
    _ ≤ Real.exp 6 * (1 + Real.log W) := eulerProduct_one_le hW

/-- The chosen cutoffs give an explicit bound for the greedy survival product. -/
lemma eventually_greedy_product_bound : ∀ᶠ x : ℝ in Filter.atTop,
    (∏ p ∈ auxiliaryPrimes (coverW x) (coverZ x), (1 - 1 / (p : ℝ))) ≤
      10 * smoothScaleConstant * Real.exp 6 * Real.log (Real.log x) ^ 2 /
        (Real.log x * Real.log (Real.log (Real.log x))) := by
  filter_upwards [eventually_cover_parameters] with x hparameters
  obtain ⟨hx, hl, hll, hlll, _, _, _, hZlow, _⟩ := hparameters
  have hx1 : 1 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hlll0 : 0 < Real.log (Real.log (Real.log x)) := by linarith
  have hW : 2 ≤ coverW x := coverW_ge_two hl
  have hWZ : coverW x ≤ coverZ x := coverW_le_coverZ hx1 hZlow
  have hW0 : 0 < (coverW x : ℝ) := by exact_mod_cast (by omega : 0 < coverW x)
  have hnum : 1 + Real.log (coverW x) ≤ 5 * Real.log (Real.log x) := by
    have hlogW : Real.log (coverW x) ≤ 4 * Real.log (Real.log x) := by
      calc
        _ ≤ Real.log (Real.log x ^ 4) :=
          Real.log_le_log hW0 (Nat.floor_le (by positivity))
        _ = _ := by rw [Real.log_pow]; norm_num
    linarith
  have hlogZ : coverLogZ x / 2 ≤ Real.log (coverZ x) := by
    have hexp : 2 ≤ Real.exp (coverLogZ x / 2) := by
      linarith [Real.add_one_le_exp (coverLogZ x / 2)]
    have hsquare : Real.exp (coverLogZ x) = Real.exp (coverLogZ x / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add, add_halves]
    have hfloor : Real.exp (coverLogZ x) < (coverZ x : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    calc
      _ = Real.log (Real.exp (coverLogZ x / 2)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by nlinarith)
  calc
    _ ≤ Real.exp 6 * (1 + Real.log (coverW x)) / Real.log (coverZ x) :=
      greedy_product_le hW hWZ
    _ ≤ Real.exp 6 * (5 * Real.log (Real.log x)) / (coverLogZ x / 2) := by
      gcongr
      linarith
    _ = _ := by
      unfold coverLogZ
      field_simp [smoothScaleConstant_pos.ne', hl0.ne', hll0.ne', hlll0.ne']
      ring

/-- Primes assigned residue zero before the greedy covering step. -/
def zeroCoverPrimes (x : ℝ) : Finset ℕ :=
  (coverW x).primesLE ∪ (⌊x / 2⌋₊.primesLE \ (coverZ x).primesLE)

/-- Integers in `[1, H]` surviving the initial zero-residue sieve. -/
def zeroSurvivors (x : ℝ) (H : ℕ) : Finset ℕ :=
  survivors (Finset.Icc 1 H) (zeroCoverPrimes x) (fun _ => 0)

/-- Combine a zero-residue sieve with greedy choices on a disjoint set of moduli. -/
lemma combine_greedy_residues (S ps₀ ps₁ ps : Finset ℕ)
    (h₀ : ps₀ ⊆ ps) (h₁ : ps₁ ⊆ ps) (hdisj : Disjoint ps₀ ps₁)
    (hpos : ∀ p ∈ ps, 0 < p) :
    ∃ a : ℕ → ℕ, (∀ p ∈ ps, a p < p) ∧
      ((survivors S ps a).card : ℝ) ≤
        ((survivors S ps₀ (fun _ => 0)).card : ℝ) * ∏ p ∈ ps₁, (1 - 1 / (p : ℝ)) := by
  classical
  obtain ⟨b, hb, hcard⟩ := greedy_residue_classes
    (survivors S ps₀ (fun _ => 0)) ps₁ (fun p hp => hpos p (h₁ hp))
  let a : ℕ → ℕ := fun p => if p ∈ ps₁ then b p else 0
  refine ⟨a, ?_, ?_⟩
  · intro p hp
    by_cases hp₁ : p ∈ ps₁
    · simpa [a, hp₁] using hb p hp₁
    · simpa [a, hp₁] using hpos p hp
  · have hsubset : survivors S ps a ⊆
        survivors (survivors S ps₀ (fun _ => 0)) ps₁ b := by
      intro n hn
      obtain ⟨hnS, hn⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnS, ?_⟩, ?_⟩
      · intro p hp
        have hp₁ : p ∉ ps₁ := Finset.disjoint_left.mp hdisj hp
        simpa [a, hp₁] using hn p (h₀ hp)
      · intro p hp
        simpa [a, hp] using hn p (h₁ hp)
    exact (Nat.cast_le.mpr (Finset.card_le_card hsubset)).trans hcard

/-- A zero-sieve survivor is prime or has all prime factors at most the smoothness cutoff. -/
lemma zeroSurvivors_prime_or_smooth {x : ℝ} {H n : ℕ} (hx : 0 < x)
    (hsmall : 2 * (H : ℝ) < x * (coverW x : ℝ)) (hn : n ∈ zeroSurvivors x H) :
    n.Prime ∨ ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x := by
  obtain ⟨hnI, hsurvives⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1, hnH⟩ := Finset.mem_Icc.mp hnI
  have h := prime_or_smooth_of_survives hn1 hnH hx hsmall (z := (coverZ x : ℝ))
  apply Or.imp_right (fun hs p hp hpn => by exact_mod_cast hs p hp hpn) (h ?_)
  intro p hp hrange hpn
  apply hsurvives p ?_ (Nat.mod_eq_zero_of_dvd hpn)
  simp only [zeroCoverPrimes, Finset.mem_union, Finset.mem_sdiff, Nat.mem_primesLE]
  rcases hrange with hpW | ⟨hpZ, hpx⟩
  · exact Or.inl ⟨by exact_mod_cast hpW, hp⟩
  · refine Or.inr ⟨⟨Nat.le_floor hpx, hp⟩, ?_⟩
    rintro ⟨hpZ', _⟩
    exact (not_le_of_gt hpZ) (by exact_mod_cast hpZ')

/-- The small-prime cutoff exceeds `2 * (log x)^2`. -/
lemma coverW_large {x : ℝ} (hL : 2 ≤ Real.log x) :
    2 * Real.log x ^ 2 < (coverW x : ℝ) := by
  have hfloor : Real.log x ^ 4 < (coverW x : ℝ) + 1 := Nat.lt_floor_add_one _
  nlinarith [sq_nonneg (Real.log x ^ 2 - 2)]

/-- An explicit `H / log x` bound for the initial sieve's survivors. -/
lemma eventually_zeroSurvivors_bound : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ H : ℕ, x ≤ H → (H : ℝ) ≤ x * Real.log x ^ 2 →
      ((zeroSurvivors x H).card : ℝ) ≤ (Real.log 4 + 2) * H / Real.log x := by
  classical
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  filter_upwards [Filter.eventually_ge_atTop B, eventually_smooth_count,
    eventually_cover_parameters] with x hxB hsmooth hp
  obtain ⟨hx, hL, _, _, _, _, _, _, _⟩ := hp
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  intro H hxH hH
  have hprime := hB (H : ℝ) (hxB.trans hxH)
  rw [Nat.floor_natCast, ← Nat.primesLE_card_eq_primeCounting] at hprime
  have hlog : Real.log x ≤ Real.log (H : ℝ) := Real.log_le_log hx0 hxH
  have hC : 0 < Real.log 4 + 1 := by
    have h := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    linarith
  have hprime := hprime.trans (div_le_div_of_nonneg_left (by positivity) hL0 hlog)
  have hsmall : 2 * (H : ℝ) < x * (coverW x : ℝ) := by
    have hw := mul_lt_mul_of_pos_left (coverW_large hL) hx0
    nlinarith
  let smooth : Finset ℕ := (Finset.Icc 1 H).filter
    (fun n => ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x)
  have hsub : zeroSurvivors x H ⊆ H.primesLE ∪ smooth := by
    intro n hn
    have hnI := (Finset.mem_filter.mp hn).1
    rcases zeroSurvivors_prime_or_smooth hx0 hsmall hn with hpn | hsn
    · exact Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hnI).2, hpn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hsn⟩)
  have hcard : ((zeroSurvivors x H).card : ℝ) ≤ (H.primesLE.card : ℝ) + smooth.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le H.primesLE smooth)
  have hsm := hsmooth H hxH smooth (Finset.filter_subset _ _)
    (fun n hn => (Finset.mem_filter.mp hn).2)
  have hpow : Real.log x ≤ Real.log x ^ 3 := by
    have hsq : (1 : ℝ) ≤ Real.log x ^ 2 := one_le_pow₀ (by linarith : 1 ≤ Real.log x)
    have hm := mul_le_mul_of_nonneg_left hsq hL0.le
    nlinarith
  have hdiv : (H : ℝ) / Real.log x ^ 3 ≤ (H : ℝ) / Real.log x :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hL0 hpow
  calc
    _ ≤ (H.primesLE.card : ℝ) + smooth.card := hcard
    _ ≤ (Real.log 4 + 1) * H / Real.log x + (H : ℝ) / Real.log x :=
      add_le_add hprime (hsm.trans hdiv)
    _ = _ := by ring

end

end LongGapsBetweenPrimes
