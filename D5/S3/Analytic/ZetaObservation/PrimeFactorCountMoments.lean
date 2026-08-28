/- GID: D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/PrimeFactorCountMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zeta prime-factor count has exact mean and variance, including 0 and 1. -/
/- Library-search audit trail (2026-08-28):
   * `ArithmeticFunction.cardDistinctFactors` is Mathlib's existing omega and is reused.
   * `prime_support_bits_independent_bernoulli` supplies the actual zeta-law Bernoulli family.
   * `primeEvidence_summable_iff_one_lt` supplies the exact prime-series threshold.
   * Mathlib hits `integral_tsum_of_summable_integral_norm`,
     `IndepFun.integral_fun_mul_eq_mul_integral`, and `variance_eq_sub` are used below.
   * Searches for an existing zeta-law omega expectation or variance theorem found no hit. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Probability.Moments.Variance
import D5.S3.Analytic.ZetaObservation.MultiplicativeComplexityActivation
import D5.S3.Analytic.ZetaObservation.PrimeSupportBernoulliIndependence
import D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaObservation.PrimeFactorCountMoments

open scoped ArithmeticFunction.omega BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.PrimeExponentLaw
open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
open D5.S3.Analytic.ZetaObservation.MultiplicativeComplexityActivation
open D5.S3.Analytic.ZetaObservation.PrimeSupportBernoulliIndependence

noncomputable section

/-!
This is the full zeta-law statement, not the assumption-based fallback. The probability measure
and the mutually independent Bernoulli support bits are imported from their existing single
sources of truth. The proof below supplies the missing countable-sum and moment arguments.

Primality load audit: the analytic summability of `primeEvidence` uses the prime-series threshold,
whose Mathlib proof carries the number-theoretic input. Independence uses primality through unique
factorization and the existing zeta prime-coordinate theorem. Neither assertion holds for an
arbitrary countable family merely because the index type is countable.

Degeneration and hypothesis audit: the pointwise count includes `0` and `1`, both with value zero.
The actual prime-support coordinate is zero at `0` and `1` and one at its own prime, so it is not a
constant or zero family. Empty and singleton finite subfamilies are included in `iIndepFun`. The
only theorem hypothesis is `1 < s`; it constructs the zeta probability measure and is also the
exact summability threshold. The named exponent-one theorem below shows that this inequality
cannot be weakened to `1 <= s`. There are no public typeclass or instance hypotheses to weaken.
-/

/-- The number of distinct prime factors, reusing Mathlib's arithmetic function `omega`. -/
def primeFactorCount (n : Nat) : Real :=
  ArithmeticFunction.cardDistinctFactors n

/-- The real indicator that the prime `p` occurs in the factorization of `n`. -/
def primeSupportIndicator (p : Nat.Primes) (n : Nat) : Real :=
  if 0 < n.factorization p.1 then 1 else 0

private theorem prime_support_indicator_nonneg (p : Nat.Primes) (n : Nat) :
    0 <= primeSupportIndicator p n := by
  unfold primeSupportIndicator
  split <;> norm_num

private theorem prime_support_indicator_le_one (p : Nat.Primes) (n : Nat) :
    primeSupportIndicator p n <= 1 := by
  unfold primeSupportIndicator
  split <;> norm_num

private theorem prime_support_indicator_mul_self (p : Nat.Primes) (n : Nat) :
    primeSupportIndicator p n * primeSupportIndicator p n = primeSupportIndicator p n := by
  simp [primeSupportIndicator]

private theorem prime_support_indicator_summable (n : Nat) :
    Summable (fun p : Nat.Primes => primeSupportIndicator p n) := by
  apply summable_of_hasFiniteSupport
  apply (occupied_prime_modes_finite n).subset
  intro p hp
  simp only [Function.mem_support] at hp
  simp only [Set.mem_setOf_eq]
  by_contra hzero
  have hfactorization : n.factorization p.1 = 0 := by
    simpa [primeOccupancy] using hzero
  simp [primeSupportIndicator, hfactorization] at hp

/-- The distinct-prime count is the pointwise sum of its prime support indicators. -/
theorem primeFactorCount_eq_tsum_support (n : Nat) :
    primeFactorCount n = ∑' p : Nat.Primes, primeSupportIndicator p n := by
  rw [primeFactorCount, ArithmeticFunction.cardDistinctFactors_apply,
    ← List.card_toFinset, Nat.toFinset_factors]
  change (n.primeFactors.card : Real) =
    ∑' p : Nat.Primes, if 0 < n.factorization p.1 then (1 : Real) else 0
  have hsub := tsum_subtype ({p : Nat | p.Prime} : Set Nat)
    (fun p => if 0 < n.factorization p then (1 : Real) else 0)
  let e : Nat.Primes ≃ ↑({p : Nat | p.Prime} : Set Nat) :=
    { toFun := fun p : Nat.Primes =>
        (⟨p.1, p.2⟩ : ↑({p : Nat | p.Prime} : Set Nat))
      invFun := fun p : ↑({p : Nat | p.Prime} : Set Nat) =>
        (⟨p.1, p.2⟩ : Nat.Primes)
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun p => Subtype.ext rfl }
  rw [show (∑' p : Nat.Primes,
      if 0 < n.factorization p.1 then (1 : Real) else 0) =
      ∑' p : ↑({p : Nat | p.Prime} : Set Nat),
        if 0 < n.factorization p.1 then (1 : Real) else 0 by
    simpa only [e, Equiv.coe_fn_mk] using e.tsum_eq
      (fun p => if 0 < n.factorization p.1 then (1 : Real) else 0)]
  rw [hsub]
  rw [tsum_eq_sum (s := n.factorization.support)]
  · rw [Nat.support_factorization]
    calc
      (n.primeFactors.card : Real) =
          ∑ p ∈ n.primeFactors, (1 : Real) := by simp
      _ = ∑ p ∈ n.primeFactors,
          ({p : Nat | p.Prime} : Set Nat).indicator
            (fun p => if 0 < n.factorization p then (1 : Real) else 0) p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hfactor : n.factorization p ≠ 0 := by
          rw [← Finsupp.mem_support_iff, Nat.support_factorization]
          exact hp
        simp [Set.indicator, hpprime, Nat.pos_iff_ne_zero.mpr hfactor]
  · intro p hp
    simp [Set.indicator, Finsupp.notMem_support_iff.mp hp]

#print axioms primeFactorCount_eq_tsum_support

private theorem prime_support_indicator_integrable
    (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    Integrable (primeSupportIndicator p) (zetaDist s hs).toMeasure := by
  apply (integrable_const (1 : Real)).mono (by fun_prop)
  filter_upwards with n
  unfold primeSupportIndicator
  split <;> norm_num

private theorem prime_support_indicator_memLp_two
    (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    MemLp (primeSupportIndicator p) 2 (zetaDist s hs).toMeasure := by
  apply memLp_of_bounded
  · filter_upwards with n
    exact Set.mem_Icc.mpr
      (And.intro (prime_support_indicator_nonneg p n) (prime_support_indicator_le_one p n))
  · fun_prop

private theorem prime_support_indicator_integral
    (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    integral (zetaDist s hs).toMeasure (primeSupportIndicator p) = primeEvidence s p := by
  let event : Set Nat := {n : Nat | 1 <= n.factorization p.1}
  have hindicator : primeSupportIndicator p = event.indicator (fun _ => (1 : Real)) := by
    funext n
    by_cases hpositive : 0 < n.factorization p.1
    · have hone : 1 <= n.factorization p.1 := by omega
      simp [primeSupportIndicator, event, hpositive, hone]
    · have hone : ¬1 <= n.factorization p.1 := by omega
      simp [primeSupportIndicator, event, hpositive, hone]
  rw [hindicator]
  rw [show integral (zetaDist s hs).toMeasure (event.indicator fun _ => (1 : Real)) =
      (zetaDist s hs).toMeasure.real event by
    exact
      (integral_indicator_one (μ := (zetaDist s hs).toMeasure)
        (s := event) MeasurableSet.of_discrete)]
  rw [measureReal_def]
  rw [show event = {n : Nat | 1 <= n.factorization p.1} by rfl]
  rw [measure_factorization_ge s hs p.1 1 p.2]
  simp [primeEvidence, Real.rpow_nonneg]

private theorem prime_support_indicators_iIndep
    (s : Real) (hs : 1 < s) :
    iIndepFun primeSupportIndicator (zetaDist s hs).toMeasure := by
  have hbits := (prime_support_bits_independent_bernoulli s hs).2
  have hreal := hbits.comp
    (fun (_ : Nat.Primes) (bit : Bool) => if bit then (1 : Real) else 0)
    (fun _ => Measurable.of_discrete)
  have heq :
      (fun p : Nat.Primes =>
        (fun bit : Bool => if bit then (1 : Real) else 0) ∘
          fun n : Nat => decide (0 < n.factorization p.1)) =
        fun p : Nat.Primes => fun n : Nat =>
          if 0 < n.factorization p.1 then (1 : Real) else 0 := by
    funext p n
    simp
  change iIndepFun
    (fun p : Nat.Primes => fun n : Nat =>
      if 0 < n.factorization p.1 then (1 : Real) else 0)
    (zetaDist s hs).toMeasure
  rw [← heq]
  exact hreal

/-- Under the zeta law, the expected distinct-prime count is the prime evidence sum. -/
theorem prime_factor_count_expectation (s : Real) (hs : 1 < s) :
    integral (zetaDist s hs).toMeasure primeFactorCount =
      ∑' p : Nat.Primes, primeEvidence s p := by
  rw [show primeFactorCount = fun n => ∑' p : Nat.Primes,
      primeSupportIndicator p n by
    funext n
    exact primeFactorCount_eq_tsum_support n]
  rw [← integral_tsum_of_summable_integral_norm
    (fun p => prime_support_indicator_integrable s hs p)]
  · apply tsum_congr
    exact prime_support_indicator_integral s hs
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (prime_support_indicator_nonneg _ _),
      prime_support_indicator_integral s hs] using primeEvidence_summable s hs

#print axioms prime_factor_count_expectation

private def pairMoment (s : Real) (pair : Nat.Primes × Nat.Primes) : Real :=
  if pair.1 = pair.2 then primeEvidence s pair.1
  else primeEvidence s pair.1 * primeEvidence s pair.2

private def primeVarianceTerm (s : Real) (p : Nat.Primes) : Real :=
  primeEvidence s p * (1 - primeEvidence s p)

private theorem prime_evidence_mem_unit_interval (s : Real) (hs : 1 < s) (p : Nat.Primes) :
    primeEvidence s p ∈ Set.Ioc 0 1 := by
  constructor
  · exact primeEvidence_pos s p
  · exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast p.2.one_lt.le) (by linarith)

private theorem prime_variance_terms_summable (s : Real) (hs : 1 < s) :
    Summable (primeVarianceTerm s) := by
  apply Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (primeEvidence_summable s hs)
  · exact mul_nonneg (primeEvidence_pos s p).le
      (sub_nonneg.mpr (prime_evidence_mem_unit_interval s hs p).2)
  · rw [primeVarianceTerm]
    nlinarith [primeEvidence_pos s p, (prime_evidence_mem_unit_interval s hs p).2]

private theorem diagonal_variance_summable (s : Real) (hs : 1 < s) :
    Summable (fun pair : Nat.Primes × Nat.Primes =>
      if pair.1 = pair.2 then primeVarianceTerm s pair.1 else 0) := by
  rw [summable_prod_of_nonneg (fun pair => by
    split_ifs
    · exact mul_nonneg (primeEvidence_pos s pair.1).le
        (sub_nonneg.mpr (prime_evidence_mem_unit_interval s hs pair.1).2)
    · exact le_rfl)]
  constructor
  · intro p
    exact summable_of_hasFiniteSupport ((Set.finite_singleton p).subset (by simp))
  · simpa using prime_variance_terms_summable s hs

private theorem pair_moments_summable (s : Real) (hs : 1 < s) :
    Summable (pairMoment s) := by
  have hproduct : Summable (fun pair : Nat.Primes × Nat.Primes =>
      primeEvidence s pair.1 * primeEvidence s pair.2) :=
    (primeEvidence_summable s hs).mul_of_nonneg (primeEvidence_summable s hs)
      (fun p => (primeEvidence_pos s p).le) (fun p => (primeEvidence_pos s p).le)
  have hsum := hproduct.add (diagonal_variance_summable s hs)
  apply hsum.congr
  rintro ⟨p, q⟩
  by_cases hpq : p = q
  · subst q
    simp [pairMoment, primeVarianceTerm]
    ring
  · simp [pairMoment, hpq]

private theorem pair_moment_tsum (s : Real) (hs : 1 < s) :
    ∑' pair, pairMoment s pair =
      (∑' p : Nat.Primes, primeEvidence s p) ^ 2 +
        ∑' p : Nat.Primes, primeVarianceTerm s p := by
  have hproduct : Summable (fun pair : Nat.Primes × Nat.Primes =>
      primeEvidence s pair.1 * primeEvidence s pair.2) :=
    (primeEvidence_summable s hs).mul_of_nonneg (primeEvidence_summable s hs)
      (fun p => (primeEvidence_pos s p).le) (fun p => (primeEvidence_pos s p).le)
  have hdiag := diagonal_variance_summable s hs
  have hdecomp : pairMoment s = fun pair =>
      primeEvidence s pair.1 * primeEvidence s pair.2 +
        if pair.1 = pair.2 then primeVarianceTerm s pair.1 else 0 := by
    funext pair
    rcases pair with ⟨p, q⟩
    by_cases hpq : p = q
    · subst q
      simp [pairMoment, primeVarianceTerm]
      ring
    · simp [pairMoment, hpq]
  calc
    (∑' pair, pairMoment s pair) = ∑' pair : Nat.Primes × Nat.Primes,
        (primeEvidence s pair.1 * primeEvidence s pair.2 +
          if pair.1 = pair.2 then primeVarianceTerm s pair.1 else 0) := by rw [hdecomp]
    _ = (∑' pair : Nat.Primes × Nat.Primes,
          primeEvidence s pair.1 * primeEvidence s pair.2) +
        (∑' pair : Nat.Primes × Nat.Primes,
          if pair.1 = pair.2 then primeVarianceTerm s pair.1 else 0) :=
      (hproduct.tsum_add hdiag)
    _ = (∑' p : Nat.Primes, primeEvidence s p) ^ 2 +
        ∑' pair : Nat.Primes × Nat.Primes,
          if pair.1 = pair.2 then primeVarianceTerm s pair.1 else 0 := by
      rw [pow_two]
      congr 1
      exact ((primeEvidence_summable s hs).tsum_mul_tsum
        (primeEvidence_summable s hs) hproduct).symm
    _ = (∑' p : Nat.Primes, primeEvidence s p) ^ 2 +
        ∑' p : Nat.Primes, primeVarianceTerm s p := by
      congr 1
      rw [hdiag.tsum_prod]
      simp

private theorem pair_indicator_integrable
    (s : Real) (hs : 1 < s) (pair : Nat.Primes × Nat.Primes) :
    Integrable (fun n => primeSupportIndicator pair.1 n * primeSupportIndicator pair.2 n)
      (zetaDist s hs).toMeasure :=
  (prime_support_indicator_memLp_two s hs pair.1).integrable_mul
    (prime_support_indicator_memLp_two s hs pair.2)

private theorem pair_indicator_integral
    (s : Real) (hs : 1 < s) (pair : Nat.Primes × Nat.Primes) :
    integral (zetaDist s hs).toMeasure
      (fun n => primeSupportIndicator pair.1 n * primeSupportIndicator pair.2 n) =
        pairMoment s pair := by
  rcases pair with ⟨p, q⟩
  by_cases hpair : p = q
  · subst q
    simp only [pairMoment]
    rw [show (fun n => primeSupportIndicator p n * primeSupportIndicator p n) =
        primeSupportIndicator p by
      funext n
      exact prime_support_indicator_mul_self p n]
    exact prime_support_indicator_integral s hs p
  · simp only [pairMoment, if_neg hpair]
    have hindep := (prime_support_indicators_iIndep s hs).indepFun hpair
    rw [hindep.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)]
    rw [prime_support_indicator_integral s hs, prime_support_indicator_integral s hs]

private theorem primeFactorCount_sq_eq_tsum_pairs (n : Nat) :
    primeFactorCount n ^ 2 = ∑' pair : Nat.Primes × Nat.Primes,
      primeSupportIndicator pair.1 n * primeSupportIndicator pair.2 n := by
  have hsupport := prime_support_indicator_summable n
  have hproduct := hsupport.mul_of_nonneg hsupport
    (fun p => prime_support_indicator_nonneg p n)
    (fun p => prime_support_indicator_nonneg p n)
  rw [primeFactorCount_eq_tsum_support, pow_two]
  exact hsupport.tsum_mul_tsum hsupport hproduct

private theorem prime_factor_count_second_moment (s : Real) (hs : 1 < s) :
    integral (zetaDist s hs).toMeasure (fun n => primeFactorCount n ^ 2) =
      (∑' p : Nat.Primes, primeEvidence s p) ^ 2 +
        ∑' p : Nat.Primes, primeVarianceTerm s p := by
  rw [show (fun n => primeFactorCount n ^ 2) = fun n =>
      ∑' pair : Nat.Primes × Nat.Primes,
        primeSupportIndicator pair.1 n * primeSupportIndicator pair.2 n by
    funext n
    exact primeFactorCount_sq_eq_tsum_pairs n]
  rw [← integral_tsum_of_summable_integral_norm
    (fun pair => pair_indicator_integrable s hs pair)]
  · rw [show (∑' pair : Nat.Primes × Nat.Primes,
        integral (zetaDist s hs).toMeasure (fun n =>
          primeSupportIndicator pair.1 n * primeSupportIndicator pair.2 n)
          ) = ∑' pair, pairMoment s pair by
      apply tsum_congr
      exact pair_indicator_integral s hs]
    exact pair_moment_tsum s hs
  · simpa only [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (prime_support_indicator_nonneg _ _)
        (prime_support_indicator_nonneg _ _)), pair_indicator_integral s hs,
      abs_of_nonneg] using pair_moments_summable s hs

private theorem primeFactorCount_sq_integrable (s : Real) (hs : 1 < s) :
    Integrable (fun n => primeFactorCount n ^ 2) (zetaDist s hs).toMeasure := by
  apply Integrable.of_integral_ne_zero
  rw [prime_factor_count_second_moment s hs]
  let twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hmean : 0 < ∑' p : Nat.Primes, primeEvidence s p :=
    (primeEvidence_summable s hs).tsum_pos
      (fun p => (primeEvidence_pos s p).le) twoPrime (primeEvidence_pos s twoPrime)
  have hvariance : 0 <= ∑' p : Nat.Primes, primeVarianceTerm s p :=
    tsum_nonneg fun p => mul_nonneg (primeEvidence_pos s p).le
      (sub_nonneg.mpr (prime_evidence_mem_unit_interval s hs p).2)
  nlinarith [sq_pos_of_pos hmean]

private theorem primeFactorCount_memLp_two (s : Real) (hs : 1 < s) :
    MemLp primeFactorCount 2 (zetaDist s hs).toMeasure := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  exact primeFactorCount_sq_integrable s hs

/-- Under the zeta law, the variance is the sum of the Bernoulli variances. -/
theorem prime_factor_count_variance (s : Real) (hs : 1 < s) :
    variance primeFactorCount (zetaDist s hs).toMeasure =
      ∑' p : Nat.Primes, primeEvidence s p * (1 - primeEvidence s p) := by
  rw [variance_eq_sub (primeFactorCount_memLp_two s hs)]
  change integral (zetaDist s hs).toMeasure (fun n => primeFactorCount n ^ 2) - _ = _
  rw [prime_factor_count_second_moment s hs, prime_factor_count_expectation s hs]
  change _ = ∑' p : Nat.Primes, primeVarianceTerm s p
  ring

#print axioms prime_factor_count_variance

/-- Zero, one, and a prime realize the finite-support degeneracies of the count. -/
theorem prime_factor_count_degenerate_audit (p : Nat.Primes) :
    primeFactorCount 0 = 0 ∧ primeFactorCount 1 = 0 ∧ primeFactorCount p.1 = 1 := by
  simp [primeFactorCount, ArithmeticFunction.cardDistinctFactors_apply_prime p.2]

#print axioms prime_factor_count_degenerate_audit

/-- Exponent one shows that the strict zeta-law threshold cannot be weakened. -/
theorem moment_threshold_is_necessary :
    Not (Summable (primeEvidence 1)) :=
  primeEvidence_one_not_summable

#print axioms moment_threshold_is_necessary

end

end D5.S3.Analytic.ZetaObservation.PrimeFactorCountMoments
