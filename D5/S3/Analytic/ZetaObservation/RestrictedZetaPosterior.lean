/- GID: D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/RestrictedZetaPosterior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Single-prime conditional cofactor law, Euler split, and degenerate audits. -/

import D5.S3.Analytic.ZetaObservation.FinitePrimeObservationPosterior
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/- Library-search audit trail (2026-08-28):
   * Repository hits: `zetaDist`, `zeta_dist_apply`, `partitionFunction`,
     `measure_factorization_eq`, and `finite_prime_observation_posterior` are reused.
   * Mathlib hits: `ProbabilityTheory.cond`, `cond_apply'`, `PMF.toMeasure_apply_singleton`,
     `Nat.factorization_mul`, `Nat.Prime.factorization_pow`, and `Nat.Coprime` are used;
     `Finset.prod` was inspected but is unnecessary for the single-prime route.
   * Euler hits: `riemannZeta` and `riemannZeta_eulerProduct_tprod`; the latter is used
     only by the Euler split theorem.
   * Searches for `condCount`, `IndepFun`, and an existing restricted-zeta posterior found
     no exact declaration needed by this single-prime proof.
   * The source boundary is respected: the conditional result is for the concrete zeta law.
     The available `ZetaPrimeIndependence` anchor is not generalized to correlated laws.
   * Strength (b) is selected: one observed prime. The finite-set extension is not claimed.
   * Assumption audit: every explicit `1 < s`, prime, and coprimality premise is used;
     no extra typeclass premise is introduced. The posterior uses point masses and
     unique factorization, while the law itself comes from the Gibbs measure construction.
-/

namespace D5.S3.Analytic.ZetaObservation.RestrictedZetaPosterior

open scoped ENNReal BigOperators ProbabilityTheory
open MeasureTheory ProbabilityTheory Set
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.PrimeExponentLaw
open D5.S3.Analytic.ZetaObservation.FinitePrimeObservationPosterior

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The one-prime observation and the associated quotient are named source objects. -/
def singlePrimeObservation (p k : ℕ) : Set ℕ :=
  {n | n.factorization p = k}

def singlePrimeCofactor (p k n : ℕ) : ℕ :=
  n / p ^ k

def emptyPrimeObservation : Set ℕ := Set.univ

def restrictedZetaPartition (s : ℝ) (p : Nat.Primes) : ℝ≥0∞ :=
  partitionFunction s * ENNReal.ofReal (1 - (p.1 : ℝ) ^ (-s))

def restrictedZetaEulerProduct (s : ℝ) (p : Nat.Primes) : ℂ :=
  (∏' q : Nat.Primes, (1 - (q.1 : ℂ) ^ (-(s : ℂ)))⁻¹) *
    (1 - (p.1 : ℂ) ^ (-(s : ℂ)))

private lemma prime_factor_ne_zero (p : Nat.Primes) (k : ℕ) : p.1 ^ k ≠ 0 :=
  pow_ne_zero _ p.2.ne_zero

private lemma prime_factor_pos (p : Nat.Primes) (k : ℕ) : 0 < p.1 ^ k :=
  pow_pos p.2.pos _

private lemma prime_power_observation (p : Nat.Primes) (k m : ℕ)
    (hm : Nat.Coprime m p.1) (hm0 : m ≠ 0) :
    p.1 ^ k * m ∈ singlePrimeObservation p.1 k := by
  rw [singlePrimeObservation, Set.mem_setOf_eq, Nat.factorization_mul
    (prime_factor_ne_zero p k) hm0, Finsupp.add_apply]
  rw [p.2.factorization_pow]
  have hnotdvd : ¬p.1 ∣ m := by
    exact p.2.coprime_iff_not_dvd.mp hm.symm
  rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd]
  simp

private lemma observation_cofactor_inter_singleton (p : Nat.Primes) (k m : ℕ)
    (hm : Nat.Coprime m p.1) (hm0 : m ≠ 0) :
    singlePrimeObservation p.1 k ∩
        {n | singlePrimeCofactor p.1 k n = m} = {p.1 ^ k * m} := by
  ext n
  constructor
  · intro hn
    have hn0 : n ≠ 0 := by
      intro hnzero
      subst n
      exact hm0 (by simpa [singlePrimeCofactor] using hn.2.symm)
    have hdvd : p.1 ^ k ∣ n := by
      apply p.2.pow_dvd_iff_le_factorization hn0 |>.2
      have heq : n.factorization p.1 = k := by
        simpa [singlePrimeObservation] using hn.1
      exact heq.ge
    have hcof : singlePrimeCofactor p.1 k n = m := hn.2
    rw [singlePrimeCofactor] at hcof
    have hrec : n / p.1 ^ k * p.1 ^ k = n := Nat.div_mul_cancel hdvd
    rw [Set.mem_singleton_iff, ← hrec, hcof, Nat.mul_comm]
  · intro hn
    rw [Set.mem_singleton_iff] at hn
    subst n
    exact ⟨prime_power_observation p k m hm hm0, by
      simp [singlePrimeCofactor, Nat.mul_comm, prime_factor_pos p k]⟩

private lemma restricted_zeta_algebra (A B C P : ℝ≥0∞)
    (hA0 : A ≠ 0) (hAt : A ≠ ∞) (hB0 : B ≠ 0) (hBt : B ≠ ∞)
    (hP0 : P ≠ 0) (hPt : P ≠ ∞) :
    (A * B)⁻¹ * (B * C * P⁻¹) = C * (P * A)⁻¹ := by
  rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt)]
  calc
    A⁻¹ * B⁻¹ * (B * C * P⁻¹) =
        A⁻¹ * (B⁻¹ * (B * C)) * P⁻¹ := by ac_rfl
    _ = A⁻¹ * C * P⁻¹ := by rw [ENNReal.inv_mul_cancel_left hB0 hBt]
    _ = C * (P * A)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hP0) (Or.inl hPt)]
      ac_rfl

theorem restricted_zeta_euler_split (s : ℝ) (hs : 1 < s) (p : Nat.Primes) :
    restrictedZetaEulerProduct s p =
      riemannZeta (s : ℂ) * (1 - (p.1 : ℂ) ^ (-(s : ℂ))) := by
  unfold restrictedZetaEulerProduct
  rw [riemannZeta_eulerProduct_tprod (by simpa using hs)]

#print axioms restricted_zeta_euler_split

theorem single_prime_restricted_zeta_posterior (s : ℝ) (hs : 1 < s)
    (p : Nat.Primes) (k m : ℕ) (hm : Nat.Coprime m p.1) :
    ProbabilityTheory.cond (zetaDist s hs).toMeasure (singlePrimeObservation p.1 k)
        {n | singlePrimeCofactor p.1 k n = m} =
      weight s m * (restrictedZetaPartition s p)⁻¹ := by
  by_cases hm0 : m = 0
  · subst m
    rw [cond_apply' MeasurableSet.of_discrete]
    have hzero : (zetaDist s hs).toMeasure ({0} : Set ℕ) = 0 := by
      rw [PMF.toMeasure_apply_singleton (zetaDist s hs) 0 MeasurableSet.of_discrete]
      simp [zeta_dist_apply, weight_zero s (by linarith)]
    have hsubset : singlePrimeObservation p.1 k ∩
        {n | singlePrimeCofactor p.1 k n = 0} ⊆ ({0} : Set ℕ) := by
      intro n hn
      by_contra hn0
      have hdvd : p.1 ^ k ∣ n := by
        apply p.2.pow_dvd_iff_le_factorization hn0 |>.2
        have heq : n.factorization p.1 = k := by
          simpa [singlePrimeObservation] using hn.1
        exact heq.ge
      have hpos := (Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hn0) hdvd)
        (prime_factor_pos p k)).ne'
      exact hpos (by simpa [singlePrimeCofactor] using hn.2)
    have hinter :
        (zetaDist s hs).toMeasure
            (singlePrimeObservation p.1 k ∩ {n | singlePrimeCofactor p.1 k n = 0}) = 0 :=
      measure_mono_null hsubset hzero
    rw [hinter]
    simp only [mul_zero, weight_zero s (by linarith), zero_mul]
  · have hset := observation_cofactor_inter_singleton p k m hm hm0
    change ProbabilityTheory.cond (zetaDist s hs).toMeasure
        {n | n.factorization p.1 = k} {n | singlePrimeCofactor p.1 k n = m} = _
    have hset' : {n | n.factorization p.1 = k} ∩
        {n | singlePrimeCofactor p.1 k n = m} = {p.1 ^ k * m} := by
      simpa [singlePrimeObservation] using hset
    rw [cond_apply' MeasurableSet.of_discrete, hset',
      PMF.toMeasure_apply_singleton (zetaDist s hs) (p.1 ^ k * m)
        MeasurableSet.of_discrete,
      zeta_dist_apply, restrictedZetaPartition,
      measure_factorization_eq s hs p.1 k p.2]
    rw [weight, show ((p.1 ^ k * m : ℕ) : ℝ) = (p.1 : ℝ) ^ k * (m : ℝ) by norm_num,
      Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have hq : 0 < 1 - (p.1 : ℝ) ^ (-s) := by
      apply sub_pos.mpr
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
    have hpart : partitionFunction s ≠ 0 := partition_function_ne_zero s
    have hparttop : partitionFunction s ≠ ∞ := partition_function_ne_top s hs
    rw [ENNReal.ofReal_mul hq.le]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    simp only [weight]
    have hp_pos : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
    have hA0 : ENNReal.ofReal (1 - (p.1 : ℝ) ^ (-s)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hq
    have hB0 : ENNReal.ofReal ((p.1 : ℝ) ^ ((k : ℝ) * -s)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hp_pos _)
    have hBt : ENNReal.ofReal ((p.1 : ℝ) ^ ((k : ℝ) * -s)) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    have hPt : partitionFunction s ≠ ∞ := hparttop
    have hexp : (-(k : ℝ) * s) = (k : ℝ) * -s := by ring
    have hA_top : ENNReal.ofReal (1 - (p.1 : ℝ) ^ (-s)) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    simpa only [weight, partitionFunction, hexp] using
      (restricted_zeta_algebra
        (ENNReal.ofReal (1 - (p.1 : ℝ) ^ (-s)))
        (ENNReal.ofReal ((p.1 : ℝ) ^ ((k : ℝ) * -s)))
        (ENNReal.ofReal ((m : ℝ) ^ (-s))) (partitionFunction s)
        hA0 hA_top hB0 hBt hpart hPt)

#print axioms single_prime_restricted_zeta_posterior

theorem empty_prime_observation_recovers_zeta (s : ℝ) (hs : 1 < s) (m : ℕ) :
    ProbabilityTheory.cond (zetaDist s hs).toMeasure emptyPrimeObservation
        {n | n = m} = weight s m * (partitionFunction s)⁻¹ := by
  rw [emptyPrimeObservation, cond_apply' MeasurableSet.of_discrete]
  simp only [univ_inter]
  have hsingleton : {n : ℕ | n = m} = {m} := by ext n; simp
  rw [hsingleton, measure_univ, inv_one, one_mul,
      PMF.toMeasure_apply_singleton (zetaDist s hs) m MeasurableSet.of_discrete,
      zeta_dist_apply]
  rfl

#print axioms empty_prime_observation_recovers_zeta

theorem single_prime_zero_cofactor_posterior (s : ℝ) (hs : 1 < s) (p : Nat.Primes)
    (k : ℕ) :
    ProbabilityTheory.cond (zetaDist s hs).toMeasure (singlePrimeObservation p.1 k)
        {n | singlePrimeCofactor p.1 k n = 0} = 0 := by
  rw [cond_apply' MeasurableSet.of_discrete]
  have hsubset : singlePrimeObservation p.1 k ∩
      {n | singlePrimeCofactor p.1 k n = 0} ⊆ ({0} : Set ℕ) := by
    intro n hn
    by_contra hn0
    have hdvd : p.1 ^ k ∣ n := by
      apply p.2.pow_dvd_iff_le_factorization hn0 |>.2
      have heq : n.factorization p.1 = k := by
        simpa [singlePrimeObservation] using hn.1
      exact heq.ge
    have hpos := (Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hn0) hdvd)
      (prime_factor_pos p k)).ne'
    exact hpos (by simpa [singlePrimeCofactor] using hn.2)
  have hzero : (zetaDist s hs).toMeasure ({0} : Set ℕ) = 0 := by
    rw [PMF.toMeasure_apply_singleton (zetaDist s hs) 0 MeasurableSet.of_discrete]
    simp [zeta_dist_apply, weight_zero s (by linarith)]
  have hinter :
      (zetaDist s hs).toMeasure
          (singlePrimeObservation p.1 k ∩ {n | singlePrimeCofactor p.1 k n = 0}) = 0 :=
    measure_mono_null hsubset hzero
  rw [hinter]
  simp

#print axioms single_prime_zero_cofactor_posterior

theorem restricted_zeta_partition_ne_zero (s : ℝ) (hs : 1 < s) (p : Nat.Primes) :
    restrictedZetaPartition s p ≠ 0 := by
  unfold restrictedZetaPartition
  have hpR : 1 < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hpow : (p.1 : ℝ) ^ (-s) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  exact mul_ne_zero (partition_function_ne_zero s)
    (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hpow))

#print axioms restricted_zeta_partition_ne_zero

theorem zeta_exponent_above_one_is_necessary : partitionFunction 1 = ∞ := by
  simpa [partitionFunction] using weight_one_tsum_eq_top

#print axioms zeta_exponent_above_one_is_necessary

theorem coprimality_is_necessary :
    let p : Nat.Primes := ⟨2, by norm_num⟩
    singlePrimeObservation p.1 0 ∩
        {n | singlePrimeCofactor p.1 0 n = 2} = (∅ : Set ℕ) := by
  dsimp
  ext n
  constructor
  · intro hn
    have hnobs : n.factorization 2 = 0 := by
      simpa [singlePrimeObservation] using hn.1
    have hcof : n / 2 ^ 0 = 2 := by
      simpa [singlePrimeCofactor] using hn.2
    have hn_eq : n = 2 := by simpa using hcof
    subst n
    norm_num at hnobs
  · intro hn
    simp at hn

#print axioms coprimality_is_necessary

theorem restricted_zeta_posterior_at_unit (s : ℝ) (hs : 1 < s) (p : Nat.Primes) :
    ProbabilityTheory.cond (zetaDist s hs).toMeasure (singlePrimeObservation p.1 0)
        {n | singlePrimeCofactor p.1 0 n = 1} =
      weight s 1 * (restrictedZetaPartition s p)⁻¹ := by
  simpa using single_prime_restricted_zeta_posterior s hs p 0 1 (by simp)

#print axioms restricted_zeta_posterior_at_unit

theorem no_finite_observation_contains_all_primes :
    ¬ ∃ (S : Finset Nat.Primes), ∀ p : Nat.Primes, p ∈ S := by
  intro h
  rcases h with ⟨S, hS⟩
  have hfin : (Set.univ : Set Nat.Primes).Finite := S.finite_toSet.subset (by
    intro p hp
    exact hS p)
  exact Set.infinite_univ.not_finite hfin

#print axioms no_finite_observation_contains_all_primes

end

end D5.S3.Analytic.ZetaObservation.RestrictedZetaPosterior
