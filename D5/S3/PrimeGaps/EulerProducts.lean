/- GID: D5/S3/PrimeGaps/EulerProducts
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the Euler-product comparisons that bound the divisor moment from below. -/

/- Ported from openai/LongGapsBetweenPrimes commit 8f5fa88c88b4750028c05b66b081d56a92418054.
   Modified by trureturing on 2026-09-04: repository routing and module split. -/
/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import D5.S3.PrimeGaps.SieveCoefficients

namespace LongGapsBetweenPrimes

noncomputable section

/-- Divisors divisible by p are parametrized by the divisors of P/p. -/
theorem sum_divisors_dvd_eq {P p : ℕ} (hP : P ≠ 0) (hp : 0 < p) (hpP : p ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors.filter (fun d => p ∣ d), f d) =
      ∑ e ∈ (P / p).divisors, f (p * e) := by
  symm
  refine Finset.sum_bij (fun e _ => p * e) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro e he
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr
        ⟨(Nat.dvd_div_iff_mul_dvd hpP).mp (Nat.dvd_of_mem_divisors he), hP⟩,
        dvd_mul_right p e⟩
  · intro e₁ _ e₂ _ h
    exact Nat.mul_left_cancel hp h
  · intro d hd
    obtain ⟨hd, hpd⟩ := Finset.mem_filter.mp hd
    refine ⟨d / p, Nat.mem_divisors.mpr ⟨?_, ?_⟩, Nat.mul_div_cancel' hpd⟩
    · exact Nat.div_dvd_div hpd (Nat.dvd_of_mem_divisors hd)
    · intro h
      apply hP
      rw [← Nat.mul_div_cancel' hpP, h, mul_zero]

/-- Multiplying a nontrivial divisor by a prime decreases the absolute coefficient. -/
theorem abs_coefficient_mul_le {P p e : ℕ} (hP : 1 < P) (hp : 1 ≤ p) (he : 1 < e) :
    |coefficient P (p * e)| ≤ |coefficient P e| := by
  have hpe : e ≤ p * e := by simpa using Nat.mul_le_mul_right e hp
  have hpe1 : 1 < p * e := he.trans_le hpe
  rw [abs_of_neg (coefficient_neg hP hpe1), abs_of_neg (coefficient_neg hP he)]
  simp only [coefficient, if_neg (ne_of_gt hpe1), if_neg (ne_of_gt he),
    neg_div, neg_neg]
  apply one_div_le_one_div_of_le
  · exact mul_pos (normalizer_pos hP) (Real.log_pos (by exact_mod_cast he))
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by exact_mod_cast (zero_lt_one.trans he))
        (by exact_mod_cast hpe)) (normalizer_pos hP).le

/-- The absolute coefficient moment at exponent zero equals one. -/
lemma coefficientAbsMoment_zero {P : ℕ} (hP : 1 < P) : coefficientAbsMoment P 0 = 1 := by
  have h := partial_cancellation hP {1}
    (by simpa using Nat.one_mem_divisors.mpr (by omega : P ≠ 0)) (by simp)
  simpa [coefficientAbsMoment, coefficient, Finset.sdiff_singleton_eq_erase] using h.symm

/-- The sum of absolute coefficients divided by totients equals two. -/
lemma sum_abs_coefficient_div_totient {P : ℕ} (hP : 1 < P) :
    (∑ d ∈ P.divisors, |coefficient P d| / d.totient) = 2 := by
  rw [← Finset.sum_erase_add _ _ (Nat.one_mem_divisors.mpr (by omega : P ≠ 0))]
  have h := coefficientAbsMoment_zero hP
  simp only [coefficientAbsMoment, Real.rpow_zero, mul_one] at h
  rw [h]
  norm_num [coefficient]

/-- The incidence bound (3.7), with an explicit constant once |a(p)| ≤ 1. -/
theorem coefficient_prime_incidence {P p : ℕ} (hP : 1 < P) (hsq : Squarefree P)
    (hp : p.Prime) (hpP : p ∣ P) (hcoeff : |coefficient P p| ≤ 1) :
    (∑ d ∈ P.divisors.filter (fun d => p ∣ d), |coefficient P d| / d.totient) ≤
      4 / (p : ℝ) := by
  have hP0 : P ≠ 0 := by omega
  have hpR : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  rw [sum_divisors_dvd_eq hP0 hp.pos hpP]
  calc
    _ ≤ ∑ e ∈ (P / p).divisors,
        (|coefficient P e| / e.totient) / ((p : ℝ) - 1) := by
      apply Finset.sum_le_sum
      intro e he
      have hcop : p.Coprime e := by
        apply hp.coprime_iff_not_dvd.mpr
        intro hpe
        have hpeP := (Nat.dvd_div_iff_mul_dvd hpP).mp (Nat.dvd_of_mem_divisors he)
        exact hp.ne_one (Nat.isUnit_iff.mp (hsq p ((mul_dvd_mul_left p hpe).trans hpeP)))
      have hcoeff' : |coefficient P (p * e)| ≤ |coefficient P e| := by
        by_cases he1 : e = 1
        · simpa [he1, coefficient] using hcoeff
        · exact abs_coefficient_mul_le hP hp.one_le
            (by have := Nat.pos_of_mem_divisors he; omega)
      rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.cast_mul,
        Nat.cast_sub hp.one_le, Nat.cast_one]
      calc
        _ ≤ |coefficient P e| / (((p : ℝ) - 1) * e.totient) :=
          div_le_div_of_nonneg_right hcoeff' (mul_nonneg hpR.le (Nat.cast_nonneg _))
        _ = _ := by rw [mul_comm, div_mul_eq_div_div]
    _ = (∑ e ∈ (P / p).divisors, |coefficient P e| / e.totient) /
        ((p : ℝ) - 1) := by rw [Finset.sum_div]
    _ ≤ 2 / ((p : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right _ hpR.le
      calc
        _ ≤ ∑ e ∈ P.divisors, |coefficient P e| / e.totient :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Nat.divisors_subset_of_dvd hP0 (Nat.div_dvd_of_dvd hpP))
            (fun _ _ _ => by positivity)
        _ = 2 := sum_abs_coefficient_div_totient hP
    _ ≤ 4 / (p : ℝ) := by
      apply (div_le_div_iff₀ hpR (by exact_mod_cast hp.pos)).mpr
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith

/-- The logarithms of distinct prime divisors sum to at most `log n`. -/
lemma sum_log_prime_divisors_le_log {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (∑ p ∈ N.primesLE, if p ∣ n then Real.log p else 0) ≤ Real.log n := by
  have hfilter : N.primesLE.filter (fun p => p ∣ n) = n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
    exact ⟨fun h => ⟨h.1.2, h.2, hn.ne'⟩,
      fun h => ⟨⟨(Nat.le_of_dvd hn h.2.1).trans hnN, h.1⟩, h.2.1⟩⟩
  rw [← Finset.sum_filter, hfilter, ← Real.log_prod (fun p hp =>
    Nat.cast_ne_zero.mpr (Nat.mem_primeFactors.mp hp).1.ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp =>
      Nat.cast_pos.mpr (Nat.mem_primeFactors.mp hp).1.pos
  · rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- An elementary upper bound for the logarithmically weighted prime harmonic sum. -/
theorem sum_prime_log_div_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ N.primesLE, Real.log p / p) ≤ Real.log N + Real.log 4 := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcount (p : ℕ) (_hp : p ∈ N.primesLE) :
      (N : ℝ) / p - 1 ≤ (N / p : ℕ) := by
    simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using
      (Nat.sub_one_lt_floor ((N : ℝ) / p)).le
  have hsum : (∑ p ∈ N.primesLE, ((N / p : ℕ) : ℝ) * Real.log p) ≤
      (N : ℝ) * Real.log N := by
    calc
      _ = ∑ p ∈ N.primesLE, ∑ n ∈ Finset.range N,
          if p ∣ n + 1 then Real.log p else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← Nat.card_multiples N p, ← Finset.sum_boole]
        simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      _ = ∑ n ∈ Finset.range N, ∑ p ∈ N.primesLE,
          if p ∣ n + 1 then Real.log p else 0 := Finset.sum_comm
      _ ≤ ∑ n ∈ Finset.range N, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN : n + 1 ≤ N := by simpa using Finset.mem_range.mp hn
        exact (sum_log_prime_divisors_le_log (by omega : 0 < n + 1) hnN).trans
          (Real.log_le_log (by positivity) (by exact_mod_cast hnN))
      _ = (N : ℝ) * Real.log N := by simp
  have hlower : (N : ℝ) * (∑ p ∈ N.primesLE, Real.log p / p) -
      Chebyshev.theta N ≤ (N : ℝ) * Real.log N := by
    apply le_trans _ hsum
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have h := mul_le_mul_of_nonneg_right (hcount p hp)
      (Nat.mem_primesLE.mp hp).2.log_pos.le
    calc
      (N : ℝ) * (Real.log p / p) - Real.log p =
        ((N : ℝ) / p - 1) * Real.log p := by ring
      _ ≤ _ := h
  have htheta := Chebyshev.theta_le_log4_mul_x hNr.le
  apply (mul_le_mul_iff_right₀ hNr).mp
  nlinarith

/-- The finite Euler product over primes at most N. -/
def eulerProduct (N : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ N.primesLE, (1 - (p : ℝ) ^ (-σ))⁻¹

/-- The multiplicative weight `n ↦ n ^ (-σ)`. -/
def natPowerHom (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-σ)
  map_one' := by simp
  map_mul' a b := by
    simp only [Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The weighted sum over smooth numbers is bounded by the finite Euler product. -/
lemma sum_smooth_le_eulerProduct {N : ℕ} {σ : ℝ} (hσ : 0 < σ)
    (S : Finset ℕ) (hS : ∀ n ∈ S, n ∈ (N + 1).smoothNumbers) :
    (∑ n ∈ S, (n : ℝ) ^ (-σ)) ≤ eulerProduct N σ := by
  classical
  have hprime {p : ℕ} (hp : p.Prime) : ‖natPowerHom σ p‖ < 1 := by
    change ‖(p : ℝ) ^ (-σ)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hσ)
  have hsum :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := natPowerHom σ) hprime (N + 1)).2
  rw [← Finset.sum_subtype_of_mem _ hS]
  exact sum_le_hasSum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum

/-- The lower half of the weak Mertens product estimate. -/
theorem log_le_eulerProduct_one (N : ℕ) : Real.log N ≤ eulerProduct N 1 := by
  have h := sum_smooth_le_eulerProduct (N := N) (by norm_num : (0 : ℝ) < 1)
    (Finset.Icc 1 N) (fun n hn => Nat.mem_smoothNumbers_of_lt
      (by have := Finset.mem_Icc.mp hn; omega)
      (by have := Finset.mem_Icc.mp hn; omega))
  have hlog := log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg _)
  rw [Nat.floor_natCast, harmonic_eq_sum_Icc] at hlog
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlog
  simp only [Real.rpow_neg_one] at h
  exact hlog.trans h

/-- The elementary zeta-function bound obtained by integrating t^(-σ). -/
theorem tsum_succ_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hexp : -σ < -1 := neg_lt_neg hσ
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Ici 1) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral 1 (by simpa using hanti)
    (integrableOn_Ioi_rpow_of_lt hexp (by norm_num))
    (fun x hx => Real.rpow_nonneg (le_of_lt (lt_trans (by norm_num) hx)) _)
  rw [integral_Ioi_rpow_of_lt hexp (by norm_num), Nat.cast_one, Real.one_rpow,
    show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq] at htail
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hexp)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  apply add_le_add le_rfl
  simpa only [Nat.cast_add, Nat.cast_one] using htail

/-- For `σ > 1`, the finite Euler product is at most `1 + 1 / (σ - 1)`. -/
lemma eulerProduct_le_zeta_bound {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    eulerProduct N σ ≤ 1 + 1 / (σ - 1) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht := Summable.tsum_subtype_le (fun n : ℕ => (n : ℝ) ^ (-σ))
    ((N + 1).smoothNumbers) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hs
  have hseries := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := natPowerHom σ) (fun {p} hp => by
      change ‖(p : ℝ) ^ (-σ)‖ < 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
        (by linarith)) (N + 1)).2
  change HasSum (fun n : (N + 1).smoothNumbers => (n.val : ℝ) ^ (-σ))
    (eulerProduct N σ) at hseries
  rw [hseries.tsum_eq] at ht
  rw [hs.tsum_eq_zero_add, Nat.cast_zero, Real.zero_rpow (by linarith : -σ ≠ 0), zero_add] at ht
  simp only [Nat.cast_add, Nat.cast_one] at ht
  exact ht.trans (tsum_succ_rpow_le hσ)

/-- Compare an Euler factor at exponent one with its shift by `r`. -/
lemma euler_factor_comparison {p r : ℝ} (hp : 2 ≤ p) (hr : 0 ≤ r) :
    (1 - p ^ (-(1 : ℝ)))⁻¹ ≤
      (1 - p ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hden : 0 < 1 - p ^ (-(1 + r)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
  have hpm : 0 < p - 1 := sub_pos.mpr hp1
  have hlog : 0 ≤ r * Real.log p := mul_nonneg hr (Real.log_pos hp1).le
  have hpow : 1 - p ^ (-r) ≤ r * Real.log p := by
    rw [Real.rpow_def_of_pos hp0]
    have h := Real.add_one_le_exp (Real.log p * -r)
    nlinarith
  rw [Real.rpow_neg_one, ← div_eq_inv_mul]
  apply (le_div_iff₀ hden).mpr
  rw [← div_eq_inv_mul]
  calc
    (1 - p ^ (-(1 + r))) / (1 - p⁻¹) =
        1 + (1 - p ^ (-r)) / (p - 1) := by
      rw [neg_add, Real.rpow_add hp0, Real.rpow_neg_one]
      field_simp
      ring
    _ ≤ 1 + (r * Real.log p) / (p - 1) :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hpow hpm.le)
    _ ≤ 1 + 2 * r * Real.log p / p := by
      apply add_le_add le_rfl
      apply (div_le_div_iff₀ hpm hp0).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) hlog]
    _ ≤ Real.exp (2 * r * Real.log p / p) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * r * Real.log p / p)

/-- Moving the Euler product to the right of its pole has bounded cost. -/
theorem eulerProduct_comparison (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    eulerProduct N 1 ≤ eulerProduct N (1 + r) *
      Real.exp (2 * r * ∑ p ∈ N.primesLE, Real.log p / p) := by
  unfold eulerProduct
  calc
    _ ≤ ∏ p ∈ N.primesLE,
        (1 - (p : ℝ) ^ (-(1 + r)))⁻¹ * Real.exp (2 * r * Real.log p / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        apply inv_nonneg.mpr
        apply sub_nonneg.mpr
        exact (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt)
          (by norm_num : -(1 : ℝ) < 0)).le
      · intro p hp
        exact euler_factor_comparison
          (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le) hr
    _ = _ := by
      simp_rw [mul_div_assoc]
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

/-- An explicit weak Mertens upper bound, sufficient throughout the proof. -/
theorem eulerProduct_one_le {N : ℕ} (hN : 2 ≤ N) :
    eulerProduct N 1 ≤ Real.exp 6 * (1 + Real.log N) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog4 : Real.log 4 ≤ 2 * Real.log N := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (by norm_num : (0 : ℝ) < 4)
        (show (4 : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
  have hsum : (∑ p ∈ N.primesLE, Real.log p / p) ≤ 3 * Real.log N := by
    linarith [sum_prime_log_div_le (by omega : 1 ≤ N)]
  have hcost : 2 * (Real.log N)⁻¹ * (∑ p ∈ N.primesLE, Real.log p / p) ≤ 6 := by
    calc
      _ ≤ 2 * (Real.log N)⁻¹ * (3 * Real.log N) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 6 := by field_simp; norm_num
  have hzeta : eulerProduct N (1 + (Real.log N)⁻¹) ≤ 1 + Real.log N := by
    simpa using eulerProduct_le_zeta_bound
      (lt_add_of_pos_right 1 (inv_pos.mpr hlog)) N
  calc
    _ ≤ eulerProduct N (1 + (Real.log N)⁻¹) *
        Real.exp (2 * (Real.log N)⁻¹ * ∑ p ∈ N.primesLE, Real.log p / p) :=
      eulerProduct_comparison N (inv_nonneg.mpr hlog.le)
    _ ≤ (1 + Real.log N) * Real.exp 6 :=
      mul_le_mul hzeta (Real.exp_le_exp.mpr hcost) (Real.exp_nonneg _) (by positivity)
    _ = _ := mul_comm _ _

/-- The power moment of divisors weighted by reciprocal totients. -/
def divisorEulerMoment (P : ℕ) (γ : ℝ) : ℝ :=
  ∑ d ∈ P.divisors, (d : ℝ) ^ γ / d.totient

/-- Factor the divisor Euler moment of a product of distinct primes. -/
lemma divisorEulerMoment_primeProduct (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime) (γ : ℝ) :
    divisorEulerMoment (∏ p ∈ ps, p) γ =
      ∏ p ∈ ps, (1 + (p : ℝ) ^ γ / ((p : ℝ) - 1)) := by
  let f : ArithmeticFunction ℝ :=
    ⟨fun n => (n : ℝ) ^ γ / n.totient, by simp⟩
  have hf : f.IsMultiplicative := by
    constructor
    · simp [f]
    · intro a b hab
      change ((a * b : ℕ) : ℝ) ^ γ / ((a * b).totient : ℝ) =
        ((a : ℝ) ^ γ / a.totient) * ((b : ℝ) ^ γ / b.totient)
      rw [Nat.totient_mul hab, Nat.cast_mul, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact (div_mul_div_comm _ _ _ _).symm
  have hsq : Squarefree (∏ p ∈ ps, p) :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hps p hp) (hps q hq)).mpr hpq))
      (fun p hp => (hps p hp).squarefree)
  have h := hf.prodPrimeFactors_one_add_of_squarefree hsq
  rw [Nat.primeFactors_prod hps] at h
  calc
    _ = ∏ p ∈ ps, (1 + f p) := h.symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      change 1 + (p : ℝ) ^ γ / p.totient = _
      rw [Nat.totient_prime (hps p hp), Nat.cast_sub (hps p hp).one_le, Nat.cast_one]

/-- The finite Euler product is positive at every positive exponent. -/
lemma eulerProduct_pos (N : ℕ) {σ : ℝ} (hσ : 0 < σ) : 0 < eulerProduct N σ := by
  apply Finset.prod_pos
  intro p hp
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)))

/-- The finite Euler product decreases as its positive exponent increases. -/
lemma eulerProduct_antitone (N : ℕ) {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ ≤ τ) :
    eulerProduct N τ ≤ eulerProduct N σ := by
  apply Finset.prod_le_prod
  · intro p hp
    exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt) (by linarith)).le)
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    have hden : 0 < 1 - (p : ℝ) ^ (-σ) :=
      sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith))
    rw [← one_div, ← one_div]
    apply one_div_le_one_div_of_le hden
    have h := Real.rpow_le_rpow_of_exponent_le hp1.le (show -τ ≤ -σ by linarith)
    linarith

/-- Primes in the interval `(Z, Y]`. -/
def auxiliaryPrimes (Z Y : ℕ) : Finset ℕ := Y.primesLE \ Z.primesLE

/-- The product of primes in the interval `(Z, Y]`. -/
def auxiliaryProduct (Z Y : ℕ) : ℕ := ∏ p ∈ auxiliaryPrimes Z Y, p

/-- Every auxiliary prime is prime. -/
lemma auxiliaryPrimes_prime {Z Y p : ℕ} (hp : p ∈ auxiliaryPrimes Z Y) : p.Prime :=
  (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2

/-- Membership in the auxiliary primes means primality and `Z < p ≤ Y`. -/
lemma mem_auxiliaryPrimes {Z Y p : ℕ} :
    p ∈ auxiliaryPrimes Z Y ↔ p.Prime ∧ Z < p ∧ p ≤ Y := by
  simp only [auxiliaryPrimes, Finset.mem_sdiff, Nat.mem_primesLE, not_and_or, not_le]
  tauto

/-- The auxiliary prime product is squarefree. -/
lemma auxiliaryProduct_squarefree (Z Y : ℕ) : Squarefree (auxiliaryProduct Z Y) := by
  exact Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (auxiliaryPrimes_prime hp) (auxiliaryPrimes_prime hq)).mpr hpq))
    (fun p hp => (auxiliaryPrimes_prime hp).squarefree)

/-- The auxiliary prime product is positive. -/
lemma auxiliaryProduct_pos (Z Y : ℕ) : 0 < auxiliaryProduct Z Y :=
  Finset.prod_pos (fun _ hp => (auxiliaryPrimes_prime hp).pos)

/-- Split the Euler product at the lower cutoff `Z`. -/
lemma auxiliary_euler_factorization {Z Y : ℕ} (hZY : Z ≤ Y) (σ : ℝ) :
    (∏ p ∈ auxiliaryPrimes Z Y, (1 - (p : ℝ) ^ (-σ))⁻¹) * eulerProduct Z σ =
      eulerProduct Y σ := Finset.prod_sdiff (Nat.primesLE_mono hZY)

/-- A squarefree Euler factor dominates the corresponding shifted geometric factor. -/
lemma squarefree_euler_factor_ge {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    (1 - p ^ (-(1 + t)))⁻¹ ≤ 1 + p ^ (-t) / (p - 1) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpow : p ^ (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos ht)
  have hden : 0 < 1 - p ^ (-(1 + t)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith))
  rw [← one_div, div_le_iff₀ hden, neg_add, Real.rpow_add hp0, Real.rpow_neg_one]
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  field_simp
  nlinarith [mul_nonneg (Real.rpow_nonneg hp0.le (-t)) (sub_nonneg.mpr hpow.le)]

/-- A lower bound for the squarefree-divisor Euler product by a usual Euler product. -/
theorem divisorEulerMoment_ge_eulerProduct {Z Y : ℕ} (hZY : Z ≤ Y) {t : ℝ} (ht : 0 < t) :
    eulerProduct Y (1 + t) ≤
      divisorEulerMoment (auxiliaryProduct Z Y) (-t) * eulerProduct Z (1 + t) := by
  classical
  rw [← auxiliary_euler_factorization hZY (1 + t)]
  apply mul_le_mul_of_nonneg_right _ (eulerProduct_pos Z (by linarith)).le
  rw [auxiliaryProduct, divisorEulerMoment_primeProduct _
    (fun _ hp => auxiliaryPrimes_prime hp)]
  apply Finset.prod_le_prod
  · intro p hp
    exact (inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (auxiliaryPrimes_prime hp).one_lt) (by linarith)))).le
  · intro p hp
    exact squarefree_euler_factor_ge
      (by exact_mod_cast (auxiliaryPrimes_prime hp).one_lt) ht

/-- Bound the Euler product below by an integral of a negative power. -/
lemma eulerProduct_ge_power_integral (Y : ℕ) {t : ℝ} (ht : 0 < t) :
    (1 - ((Y : ℝ) + 1) ^ (-t)) / t ≤ eulerProduct Y (1 + t) := by
  calc
    _ = ∫ x : ℝ in 1..(Y : ℝ) + 1, x ^ (-(1 + t)) := by
      rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
      · rw [show -(1 + t) + 1 = -t by ring, Real.one_rpow]
        ring
      · rw [Set.uIcc_of_le (le_add_of_nonneg_left (Nat.cast_nonneg Y))]
        norm_num
    _ ≤ ∑ n ∈ Finset.Ico 1 (Y + 1), (n : ℝ) ^ (-(1 + t)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        AntitoneOn.integral_le_sum_Ico (a := 1) (b := Y + 1)
          (f := fun x : ℝ => x ^ (-(1 + t))) (by omega) (by
            intro x hx y _ hxy
            exact Real.rpow_le_rpow_of_nonpos
              (lt_of_lt_of_le (by norm_num) hx.1) hxy (by linarith))
    _ ≤ _ := sum_smooth_le_eulerProduct (by linarith)
      (Finset.Ico 1 (Y + 1)) (fun n hn => Nat.mem_smoothNumbers_of_lt
        (by have := Finset.mem_Ico.mp hn; omega) (Finset.mem_Ico.mp hn).2)

/-- The Euler product at `1 + t` is at least `1 / (2 * t)` when `t * log (Y + 1) ≥ 1`. -/
lemma eulerProduct_ge_one_div_two_mul (Y : ℕ) {t : ℝ} (ht : 0 < t)
    (hscale : 1 ≤ t * Real.log ((Y : ℝ) + 1)) :
    1 / (2 * t) ≤ eulerProduct Y (1 + t) := by
  have hpow : ((Y : ℝ) + 1) ^ (-t) ≤ 1 / 2 := by
    rw [Real.rpow_def_of_pos (by positivity),
      show Real.log ((Y : ℝ) + 1) * -t = -(t * Real.log ((Y : ℝ) + 1)) by ring,
      Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num)
      (by linarith [Real.add_one_le_exp (t * Real.log ((Y : ℝ) + 1))])
  calc
    1 / (2 * t) = (1 / 2) / t := by ring
    _ ≤ (1 - ((Y : ℝ) + 1) ^ (-t)) / t :=
      div_le_div_of_nonneg_right (by linarith) ht.le
    _ ≤ eulerProduct Y (1 + t) := eulerProduct_ge_power_integral Y ht

/-- The divisor Euler moment is nonnegative. -/
lemma divisorEulerMoment_nonneg (P : ℕ) (γ : ℝ) : 0 ≤ divisorEulerMoment P γ :=
  Finset.sum_nonneg (fun _d _ => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Nat.cast_nonneg _))

/-- The lower bound whose integral supplies a positive normalization B. -/
theorem divisorEulerMoment_lower {Z Y : ℕ} (hZY : Z ≤ Y) {t A : ℝ}
    (ht : 0 < t) (hA : 0 < A) (hZA : eulerProduct Z 1 ≤ A)
    (hscale : 1 ≤ t * Real.log ((Y : ℝ) + 1)) :
    1 / (2 * t * A) ≤ divisorEulerMoment (auxiliaryProduct Z Y) (-t) := by
  have hZ := (eulerProduct_antitone Z (by norm_num : (0 : ℝ) < 1)
    (by linarith : 1 ≤ 1 + t)).trans hZA
  have h := (eulerProduct_ge_one_div_two_mul Y ht hscale).trans
    ((divisorEulerMoment_ge_eulerProduct hZY ht).trans
      (mul_le_mul_of_nonneg_left hZ (divisorEulerMoment_nonneg _ _)))
  calc
    1 / (2 * t * A) = (1 / (2 * t)) / A := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ divisorEulerMoment (auxiliaryProduct Z Y) (-t) := (div_le_iff₀ hA).mpr h

/-- The negatively tilted divisor Euler moment is continuous. -/
lemma continuous_divisorEulerMoment (P : ℕ) :
    Continuous (fun t : ℝ => divisorEulerMoment P (-t)) := by
  unfold divisorEulerMoment
  apply continuous_finsetSum
  intro d hd
  have hdpos : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hd)
  simp only [Real.rpow_def_of_pos hdpos]
  fun_prop

/-- An exponential decay integral starting at a nonnegative point is at most `1 / L`. -/
lemma integral_exp_decay_le {L a : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (b : ℝ) :
    (∫ t : ℝ in a..b, Real.exp (-L * t)) ≤ 1 / L := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hL.ne'),
    integral_exp, smul_eq_mul, inv_neg, neg_mul, ← mul_neg, neg_sub, ← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right
    ((sub_le_self _ (Real.exp_nonneg _)).trans
      (Real.exp_le_one_iff.mpr (by nlinarith))) hL.le

end

end LongGapsBetweenPrimes
