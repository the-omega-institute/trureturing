/- GID: D5/S3/Arith/ExponentExchange/AbundancyRecord5040
   generality: I
   mirror-B: D5/B/S3/Arith/ExponentExchange/AbundancyRecord5040
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual one-layer prime exchange forces the literal 5040 core of large abundancy records. -/

import D5.S3.Arith.GoldenResource.EightStepAbundancy
import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import Mathlib.Algebra.BigOperators.Intervals

/-! The one-prime transfer is the classical superabundant-number exchange of
Alaoglu and Erdős, Library/Arith/alaoglu1944highly.md. All comparisons here use
actual natural integers and the actual sigma ratio, including the predecessor one. -/

noncomputable section
namespace D5.S3.Arith.ExponentExchange.AbundancyRecord5040

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.EightStepAbundancy
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison

/-- Removing one q and inserting one p gives an actual smaller integer with larger
abundancy whenever the missing p-layer has denominator below q. -/
theorem one_layer_abundancy_exchange {m p q k : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hq : q.Prime) (hk : 1 ≤ k) (hqm : q ∣ m)
    (hden : layerDenominator p k < q) (ha : m.factorization p < k) :
    0 < (m / q) * p ∧ (m / q) * p < m ∧
      (ArithmeticFunction.sigma 1 m : ℝ) / m <
        (ArithmeticFunction.sigma 1 ((m / q) * p) : ℝ) / ((m / q) * p) := by
  have hpden : p ≤ layerDenominator p k := by
    simpa [layerDenominator] using denominator_mono p hk
  have hpq : p < q := hpden.trans_lt hden
  have hpne : p ≠ q := hpq.ne
  have ht : 0 < m / q := Nat.div_pos (Nat.le_of_dvd hm hqm) hq.pos
  have heq : m / q * q = m := Nat.div_mul_cancel hqm
  have hfacp : (m / q).factorization p = m.factorization p := by
    have h := congrArg (fun n : ℕ => n.factorization p) heq
    simpa [Nat.factorization_mul ht.ne' hq.ne_zero, hq.factorization, hpne] using h
  have hfacq : (m / q).factorization q + 1 = m.factorization q := by
    have h := congrArg (fun n : ℕ => n.factorization q) heq
    simpa [Nat.factorization_mul ht.ne' hq.ne_zero, hq.factorization] using h
  have hqexp : 1 ≤ m.factorization q := by omega
  have hdenq : q ≤ layerDenominator q (m.factorization q) := by
    simpa [layerDenominator] using denominator_mono q hqexp
  have hdenp : layerDenominator p (m.factorization p + 1) <
      layerDenominator q (m.factorization q) :=
    (denominator_mono p (by omega : m.factorization p + 1 ≤ k)).trans_lt
      (hden.trans_le hdenq)
  have hdp : (0 : ℝ) < layerDenominator p (m.factorization p + 1) := by
    exact_mod_cast denominator_pos hp (by omega : 1 ≤ m.factorization p + 1)
  have hdelta : goldenLayerMarginal q (m.factorization q) * Real.log q <
      goldenLayerMarginal p (m.factorization p + 1) * Real.log p := by
    unfold goldenLayerMarginal
    rw [div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hq.one_lt)).ne',
      div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hp.one_lt)).ne',
      layer_ratio_identity hq hqexp, layer_ratio_identity hp (by omega)]
    apply Real.log_lt_log (by positivity)
    exact add_lt_add_left (one_div_lt_one_div_of_lt hdp (by exact_mod_cast hdenp)) 1
  have hpstep := golden_resource_objective_single_layer_delta 0 (by omega : 1 ≤ m / q) hp
  have hqstep := golden_resource_objective_single_layer_delta 0 (by omega : 1 ≤ m / q) hq
  rw [heq, hfacq] at hqstep
  rw [hfacp] at hpstep
  rw [golden_resource_sigma_identity 0 (by nlinarith [hp.pos] : 1 ≤ (m / q) * p),
    golden_resource_sigma_identity 0 (by omega : 1 ≤ m / q)] at hpstep
  rw [golden_resource_sigma_identity 0 (by omega : 1 ≤ m),
    golden_resource_sigma_identity 0 (by omega : 1 ≤ m / q)] at hqstep
  simp only [zero_mul, sub_zero] at hpstep hqstep
  refine ⟨Nat.mul_pos ht hp.pos, ?_, ?_⟩
  · calc
      (m / q) * p < (m / q) * q := Nat.mul_lt_mul_of_pos_left hpq ht
      _ = m := heq
  · apply (Real.log_lt_log_iff
      (div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 m hm.ne')
        (by exact_mod_cast hm))
      (div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 ((m / q) * p)
        (Nat.mul_pos ht hp.pos).ne') (by exact_mod_cast Nat.mul_pos ht hp.pos))).mp
    linarith

private theorem large_prime_of_abundancy {m : ℕ} (hm : 0 < m)
    (hA : 30 < (ArithmeticFunction.sigma 1 m : ℝ) / m) :
    ∃ q : ℕ, q.Prime ∧ q ∣ m ∧ 30 < q := by
  by_contra h
  have hsupport : m.primeFactors ⊆ Icc 2 30 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    refine mem_Icc.mpr ⟨hprime.two_le, ?_⟩
    by_contra hn
    exact h ⟨p, hprime, Nat.dvd_of_mem_primeFactors hp, by omega⟩
  have hgeom (p : ℕ) (hp : p.Prime) (a : ℕ) :
      (∑ i ∈ range (a + 1), (p : ℝ) ^ i) / (p : ℝ) ^ a ≤ p / (p - 1) := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpow : (0 : ℝ) < (p : ℝ) ^ a := pow_pos hp0 a
    rw [geom_sum_eq hp1.ne']
    calc
      _ ≤ (p : ℝ) ^ (a + 1) / (p - 1) / p ^ a :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (by linarith)) hpow.le
      _ = _ := by rw [pow_succ]; field_simp; ring
  have hnprod : (m : ℝ) = ∏ p ∈ m.primeFactors, (p : ℝ) ^ m.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hm.ne'
  have hsprod : (ArithmeticFunction.sigma 1 m : ℝ) =
      ∏ p ∈ m.primeFactors, ∑ i ∈ range (m.factorization p + 1), (p : ℝ) ^ i := by
    simpa only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, mul_one] using
      congrArg (fun k : ℕ => (k : ℝ))
        (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
          (k := 1) hm.ne')
  have hb : (ArithmeticFunction.sigma 1 m : ℝ) / m ≤
      ∏ p ∈ m.primeFactors, (p : ℝ) / (p - 1) := by
    rw [hsprod, hnprod, ← prod_div_distrib]
    exact prod_le_prod₀
      (fun p _ => div_nonneg (sum_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg p) i)
        (pow_nonneg (Nat.cast_nonneg p) _))
      (fun p hp => hgeom p (Nat.prime_of_mem_primeFactors hp) _)
  have hpad : (∏ p ∈ m.primeFactors, (p : ℝ) / (p - 1)) ≤
      ∏ p ∈ Icc 2 30, (p : ℝ) / (p - 1) := by
    apply prod_le_prod_of_subset_of_one_le₀ hsupport
    · intro p hp
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      apply div_nonneg (Nat.cast_nonneg p)
      have : (2 : ℝ) ≤ p := by exact_mod_cast this
      linarith
    · intro p hp _
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp hp).1
      exact (one_le_div (by linarith)).mpr (by linarith)
  have htel : (∏ p ∈ Icc 2 30, (p : ℝ) / (p - 1)) = 30 := by
    norm_num [show Icc (2 : ℕ) 30 = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30} by decide]
  linarith [hb.trans (hpad.trans_eq htel)]

/-- A strict record among every smaller positive integer with abundancy above thirty
contains all four prime-power layers of the literal integer 5040. -/
theorem strict_abundancy_record_divisible_5040 {m : ℕ} (hm : 0 < m)
    (hA : 30 < (ArithmeticFunction.sigma 1 m : ℝ) / m)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      (ArithmeticFunction.sigma 1 n : ℝ) / n < (ArithmeticFunction.sigma 1 m : ℝ) / m) :
    5040 ∣ m := by
  obtain ⟨q, hq, hqm, hq30⟩ := large_prime_of_abundancy hm hA
  have hlayer (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k)
      (hd : layerDenominator p k ≤ 30) : p ^ k ∣ m := by
    apply (hp.pow_dvd_iff_le_factorization hm.ne').mpr
    by_contra h
    obtain ⟨ht, htm, hgain⟩ := one_layer_abundancy_exchange hm hp hq hk hqm
      (hd.trans_lt hq30) (by omega)
    exact (hrecord _ ht htm).not_gt hgain
  have h2 : 16 ∣ m := by
    simpa using hlayer 2 4 (by norm_num) (by norm_num)
      (by norm_num [layerDenominator, sum_range_succ])
  have h3 : 9 ∣ m := by
    simpa using hlayer 3 2 (by norm_num) (by norm_num)
      (by norm_num [layerDenominator, sum_range_succ])
  have h5 : 5 ∣ m := by
    simpa using hlayer 5 1 (by norm_num) (by norm_num)
      (by norm_num [layerDenominator, sum_range_succ])
  have h7 : 7 ∣ m := by
    simpa using hlayer 7 1 (by norm_num) (by norm_num)
      (by norm_num [layerDenominator, sum_range_succ])
  have h23 : 144 ∣ m := (show Nat.Coprime 16 9 by norm_num).mul_dvd_of_dvd_of_dvd h2 h3
  have h235 : 720 ∣ m := (show Nat.Coprime 144 5 by norm_num).mul_dvd_of_dvd_of_dvd h23 h5
  exact (show Nat.Coprime 720 7 by norm_num).mul_dvd_of_dvd_of_dvd h235 h7

#print axioms one_layer_abundancy_exchange
#print axioms strict_abundancy_record_divisible_5040

end D5.S3.Arith.ExponentExchange.AbundancyRecord5040
