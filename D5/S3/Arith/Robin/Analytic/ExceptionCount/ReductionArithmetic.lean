/- GID: D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-power majorants for the real-power divisor transform. -/

import D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal
import D5.S3.Arith.Robin.Analytic.LcmPowerEndpointExpansion
import D5.S3.Arith.Robin.FibonacciPrimeSupport
import D5.S3.Arith.ExponentExchange.IntegerSwap
import D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope
import D5.S3.Weil.Mertens.Third
import D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Exact normalized prime-power identities and their finite-product bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Finset
open scoped BigOperators

namespace D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic
open LcmPowerEndpointExpansion LcmPowerLocalFactorBound ReductionLocal

private lemma sigma_normalized {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) / (p : ℝ) ^ a =
      (1 - (1 / (p : ℝ)) ^ (a + 1)) / (1 - 1 / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  calc
    _ = D5.S3.Arith.RobinExponentSwap.reciprocalGeomSum p a := by
      simpa only [Nat.cast_pow] using
        D5.S3.Arith.ExponentExchange.IntegerSwap.normalized_sigma_prime_pow hp a
    _ = ((p : ℝ) ^ (a + 1) - 1) / ((p : ℝ) ^ a * (p - 1)) :=
      D5.S3.Arith.Robin.PriceRecord.PrimePowerEnvelope.geom_closed hp a
    _ = _ := by
      rw [div_pow, one_pow, pow_succ]
      field_simp [hp0, hp1]
      <;> ring

/-- The normalized real-power divisor transform at a prime power is exactly
the local factor used in the convexity estimate. -/
private theorem prime_power_normalized {p : ℕ} (hp : p.Prime) (a : ℕ) (κ : ℝ) :
    sigmaKappa κ (p ^ (a + 1)) / ((p : ℝ) ^ (a + 1)) ^ κ =
      normalizedLocalFactor κ (1 / p) (a + 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : 0 < 1 - 1 / (p : ℝ) := by
    have := (div_lt_one hp0).mpr hp1
    linarith
  have hS0 : 0 ≤ (ArithmeticFunction.sigma 1 (p ^ (a + 1)) : ℝ) := by positivity
  have hU0 : 0 ≤ (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) := by positivity
  have hσS := sigma_normalized hp (a + 1)
  have hσU := sigma_normalized hp a
  have hq1 : 1 / (p : ℝ) ≤ 1 := by
    exact (div_le_one hp0).mpr hp1.le
  have hqpow (b : ℕ) : 0 ≤ 1 - (1 / (p : ℝ)) ^ b := by
    exact sub_nonneg.mpr (pow_le_one₀ (by positivity) hq1)
  have hprev : (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) /
      (p : ℝ) ^ (a + 1) =
        (1 / (p : ℝ)) * ((1 - (1 / (p : ℝ)) ^ (a + 1)) /
          (1 - 1 / (p : ℝ))) := by
    rw [← hσU, pow_succ]
    field_simp
  rw [sigmaKappa_prime_power κ hp, sub_div,
    ← Real.div_rpow hS0 (by positivity), ← Real.div_rpow hU0 (by positivity), hσS, hprev]
  rw [Real.mul_rpow (by positivity : 0 ≤ 1 / (p : ℝ))
      (div_nonneg (hqpow (a + 1)) hd.le),
    Real.div_rpow (hqpow (a + 1 + 1)) hd.le,
    Real.div_rpow (hqpow (a + 1)) hd.le]
  dsimp only [normalizedLocalFactor]
  rw [Real.rpow_neg hd.le]
  norm_cast
  ring

/-- Each arithmetic prime-power ratio is bounded by the endpoint Euler factor. -/
private theorem prime_power_upper {κ : ℝ} (hκ : 1 ≤ κ) {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) :
    sigmaKappa κ (p ^ a) / ((p : ℝ) ^ a) ^ κ ≤
      (1 - 1 / (p : ℝ)) ^ (-κ) * (1 - (1 / (p : ℝ)) ^ κ) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  rw [prime_power_normalized hp]
  apply local_factor_upper_bound hκ (by positivity)
  · apply (div_le_div_iff₀ (by exact_mod_cast hp.pos) (by norm_num : (0 : ℝ) < 2)).mpr
    norm_num
    exact_mod_cast hp.two_le
  · exact_mod_cast (show 1 ≤ b + 1 by omega)

/-- The transform ratio is bounded by the product of endpoint factors on
the actual prime support. -/
private theorem kappa_product_upper {κ : ℝ} (hκ : 1 ≤ κ) {n : ℕ} (hn : n ≠ 0) :
    sigmaKappa κ n / (n : ℝ) ^ κ ≤
      ∏ p ∈ n.primeFactors,
        (1 - 1 / (p : ℝ)) ^ (-κ) * (1 - (1 / (p : ℝ)) ^ κ) := by
  have hnprod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  rw [sigmaKappa_factorization κ hn, hnprod,
    ← Real.finsetProd_rpow _ _ (fun _ _ => by positivity), ← prod_div_distrib]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact div_nonneg (sigmaKappa_pos (by linarith) (pow_ne_zero _
      (Nat.prime_of_mem_primeFactors hp).ne_zero)).le (by positivity)
  · intro p hp
    exact prime_power_upper hκ (Nat.prime_of_mem_primeFactors hp)
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn
        (Nat.dvd_of_mem_primeFactors hp))

private lemma endpoint_one_le {κ r : ℝ} (hκ : 1 ≤ κ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    1 ≤ (1 - r) ^ (-κ) * (1 - r ^ κ) := by
  have hκ0 : κ ≠ 0 := by linarith
  simpa [hκ0] using endpoint_monotone hκ (show (0 : ℝ) ∈ Set.Ico 0 1 by simp)
    (show r ∈ Set.Ico 0 1 from ⟨hr0, hr1⟩) hr0

/-- The endpoint product on a support with at most as many primes as a
prime prefix is bounded by the product on that prefix. -/
private theorem kappa_prefix_upper {κ P : ℝ} (hκ : 1 ≤ κ) (hP : 1 < P)
    {n : ℕ} (hn : n ≠ 0)
    (hcard : n.primeFactors.card ≤ Nat.primeCounting ⌊P⌋₊) :
    sigmaKappa κ n / (n : ℝ) ^ κ ≤
      ∏ p ∈ Nat.primesLE ⌊P⌋₊,
        (1 - 1 / (p : ℝ)) ^ (-κ) * (1 - (1 / (p : ℝ)) ^ κ) := by
  apply (kappa_product_upper hκ hn).trans
  have hP0 : 0 < P := by linarith
  have hqP1 : 1 / P < 1 := (div_lt_one hP0).mpr hP
  apply support_product_le (B := (1 - 1 / P) ^ (-κ) * (1 - (1 / P) ^ κ))
  · simpa only [Nat.primesLE_card_eq_primeCounting] using hcard
  · exact endpoint_one_le hκ (by positivity) hqP1
  · intro p hp
    exact (endpoint_one_le hκ (by positivity)
      ((div_lt_one (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)).mpr
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt))).trans' zero_le_one
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
    have hpP : P < p := by
      have hnot : ¬ p ≤ ⌊P⌋₊ := by
        intro h
        exact (mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨h, hprime⟩)
      exact (Nat.floor_lt (by positivity : 0 ≤ P)).mp (lt_of_not_ge hnot)
    apply endpoint_monotone hκ
      (show 1 / (p : ℝ) ∈ Set.Ico 0 1 from ⟨by positivity,
        (div_lt_one (by exact_mod_cast hprime.pos)).mpr (by exact_mod_cast hprime.one_lt)⟩)
      (show 1 / P ∈ Set.Ico 0 1 from ⟨by positivity, hqP1⟩)
    exact one_div_le_one_div_of_le hP0 hpP.le
  · intro p hp
    have hpp := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
    have hpP : (p : ℝ) ≤ P := (Nat.le_floor_iff hP0.le).mp hpp.1
    apply endpoint_monotone hκ
      (show 1 / P ∈ Set.Ico 0 1 from ⟨by positivity, hqP1⟩)
      (show 1 / (p : ℝ) ∈ Set.Ico 0 1 from ⟨by positivity,
        (div_lt_one (by exact_mod_cast hpp.2.pos)).mpr (by exact_mod_cast hpp.2.one_lt)⟩)
    exact one_div_le_one_div_of_le (by exact_mod_cast hpp.2.pos) hpP

private lemma reciprocal_factor_antitone {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q) :
    q / (q - 1) ≤ p / (p - 1) := by
  apply (div_le_div_iff₀ (by linarith : 0 < q - 1) (by linarith : 0 < p - 1)).mpr
  nlinarith

/-- The ordinary divisor ratio is bounded by the reciprocal Euler product
on any prime prefix with enough primes. -/
private theorem robin_prefix_upper {P : ℝ} (hP : 1 < P) {n : ℕ} (hn : n ≠ 0)
    (hcard : n.primeFactors.card ≤ Nat.primeCounting ⌊P⌋₊) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n ≤
      ∏ p ∈ Nat.primesLE ⌊P⌋₊, (p : ℝ) / ((p : ℝ) - 1) := by
  apply (FibonacciPrimeSupport.ratio_le_prod n hn).trans
  apply support_product_le (B := P / (P - 1))
  · simpa only [Nat.primesLE_card_eq_primeCounting] using hcard
  · apply (le_div_iff₀ (by linarith : 0 < P - 1)).mpr
    linarith
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_nonneg (by positivity) (by linarith)
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
    have hpP : P < p := by
      have hnot : ¬ p ≤ ⌊P⌋₊ := by
        intro h
        exact (mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨h, hprime⟩)
      exact (Nat.floor_lt (by positivity : 0 ≤ P)).mp (lt_of_not_ge hnot)
    exact reciprocal_factor_antitone hP hpP.le
  · intro p hp
    have hpp := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
    have hpP : (p : ℝ) ≤ P := (Nat.le_floor_iff (by positivity : 0 ≤ P)).mp hpp.1
    exact reciprocal_factor_antitone (by exact_mod_cast hpp.2.one_lt) hpP

private lemma reciprocal_product_exact (P : ℝ) :
    (∏ p ∈ Nat.primesLE ⌊P⌋₊, (p : ℝ) / ((p : ℝ) - 1)) =
      (∏ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹) := by
  have hfactor (p : ℕ) (hp : p ∈ Nat.primesLE ⌊P⌋₊) :
      (p : ℝ) / ((p : ℝ) - 1) = (1 - 1 / (p : ℝ))⁻¹ := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.ne_zero
    field_simp
  rw [prod_congr rfl hfactor, Nat.primesLE_eq_filter_Ioc_zero]

/-- The ordinary divisor ratio is bounded by the Mertens product whenever
the cutoff contains at least as many primes as the integer's prime support. -/
theorem robin_product_upper {P : ℝ} (hP : 1 < P) {n : ℕ} (hn : n ≠ 0)
    (hcard : n.primeFactors.card ≤ Nat.primeCounting ⌊P⌋₊) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n ≤ (∏ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹) := by
  rw [← reciprocal_product_exact P]
  exact robin_prefix_upper hP hn hcard

/-- The same prime prefix bounds the kappa divisor ratio after paying a
power-decaying omitted Euler tail, uniformly for kappa bounded away from one. -/
theorem kappa_product_tail_upper {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ P : ℝ) (n : ℕ), 1 + delta ≤ κ → 2 ≤ P →
      n ≠ 0 → n.primeFactors.card ≤ Nat.primeCounting ⌊P⌋₊ →
      (riemannZeta (κ : ℂ)).re * sigmaKappa κ n / (n : ℝ) ^ κ ≤
        ((∏ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹) * exp (C * P ^ (-(delta / 2)))) ^ κ := by
  obtain ⟨C, hC, htail⟩ := ZetaTail.uniform_tail hdelta
  refine ⟨C, hC, ?_⟩
  intro κ P n hκ hP hn hcard
  have hκ1 : 1 < κ := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hz : 0 < (riemannZeta (κ : ℂ)).re := riemannZeta_re_pos_of_one_lt hκ1
  have hratio : 0 < sigmaKappa κ n / (n : ℝ) ^ κ :=
    div_pos (sigmaKappa_pos (by linarith) hn) (Real.rpow_pos_of_pos (by positivity) _)
  have hprimes (p : ℕ) (hp : p ∈ Nat.primesLE ⌊P⌋₊) :
      0 < 1 - 1 / (p : ℝ) ∧ 0 < 1 - (1 / (p : ℝ)) ^ κ := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    have hq0 : 0 ≤ 1 / (p : ℝ) := by positivity
    have hq1 : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith : (0 : ℝ) < p)).mpr hp1
    exact ⟨by linarith, sub_pos.mpr (Real.rpow_lt_one hq0 hq1 (by linarith))⟩
  have hendpoint (p : ℕ) (hp : p ∈ Nat.primesLE ⌊P⌋₊) :
      0 < (1 - 1 / (p : ℝ)) ^ (-κ) * (1 - (1 / (p : ℝ)) ^ κ) :=
    mul_pos (Real.rpow_pos_of_pos (hprimes p hp).1 _) (hprimes p hp).2
  have hlog := Real.log_le_log hratio (kappa_prefix_upper (by linarith) (by linarith) hn hcard)
  rw [Real.log_prod (fun p hp => (hendpoint p hp).ne')] at hlog
  have hsplit :
      (∑ p ∈ Nat.primesLE ⌊P⌋₊,
        log ((1 - 1 / (p : ℝ)) ^ (-κ) * (1 - (1 / (p : ℝ)) ^ κ))) =
      κ * log ((∏ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹)) +
        ∑ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, log (1 - (p : ℝ) ^ (-κ)) := by
    rw [← reciprocal_product_exact P, Real.log_prod (fun p hp => by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
      exact (div_pos (by linarith) (by linarith)).ne')]
    rw [← Nat.primesLE_eq_filter_Ioc_zero, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    have hfactor : (p : ℝ) / ((p : ℝ) - 1) = (1 - 1 / (p : ℝ))⁻¹ := by field_simp
    have hqpow : (1 / (p : ℝ)) ^ κ = (p : ℝ) ^ (-κ) := by
      rw [one_div, Real.inv_rpow hp0.le, Real.rpow_neg hp0.le]
    rw [Real.log_mul (Real.rpow_pos_of_pos (hprimes p hp).1 _).ne'
      (hprimes p hp).2.ne', Real.log_rpow (hprimes p hp).1, hfactor, Real.log_inv, hqpow]
    ring
  rw [hsplit] at hlog
  have hlogtotal : log ((riemannZeta (κ : ℂ)).re * sigmaKappa κ n / (n : ℝ) ^ κ) ≤
      κ * log ((∏ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹)) + C * P ^ (-(delta / 2)) := by
    rw [mul_div_assoc, Real.log_mul hz.ne' hratio.ne']
    linarith [htail κ P hκ hP]
  have hM : 0 < (∏ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ))⁻¹) := by
    rw [← reciprocal_product_exact P]
    apply Finset.prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    exact div_pos (by linarith) (by linarith)
  have hsmall : C * P ^ (-(delta / 2)) ≤ κ * (C * P ^ (-(delta / 2))) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  have htotal : 0 < (riemannZeta (κ : ℂ)).re * sigmaKappa κ n / (n : ℝ) ^ κ := by
    rw [mul_div_assoc]
    exact mul_pos hz hratio
  apply (Real.log_le_log_iff htotal
    (Real.rpow_pos_of_pos (mul_pos hM (exp_pos _)) _)).mp
  rw [Real.log_rpow (mul_pos hM (exp_pos _)),
    Real.log_mul hM.ne' (exp_ne_zero _), Real.log_exp]
  nlinarith

end D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic
