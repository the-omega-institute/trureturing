/- GID: D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Omega has finite prime support and independent zeta occupancies, including 0 and 1. -/
/- Library-search audit trail (2026-08-27):
   * Repository search found no FPOD multiplicative-complexity definition. Exact hits
     `measure_factorization_eq` and `iIndepFun_factorization` supply the geometric marginal and
     full prime-indexed mutual independence, so neither result is reproved.
   * Pinned Mathlib exact hits `ArithmeticFunction.cardFactors` and
     `cardFactors_eq_sum_factorization` are the existing Omega definition and decomposition.
     This module names the FPOD concept by a thin wrapper instead of creating a second source.
   * Exact repository hit `primeEvidence_summable` supplies the convergent prime majorant.
     `primeEvidence_one_not_summable` supplies the named threshold counterexample.
   * Searches of pinned Mathlib and D5 found no declaration packaging this decomposition,
     mutual-independence result, degeneracy audit, and mean-occupancy summability together. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import D5.S3.Analytic.Zeta.ZetaPrimeIndependence
import D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaObservation.MultiplicativeComplexityActivation

open scoped ArithmeticFunction.Omega BigOperators
open ProbabilityTheory
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.PrimeExponentLaw
open D5.S3.Analytic.Zeta.ZetaPrimeIndependence
open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

noncomputable section

/-!
The mathematical clause is formalized below: multiplicative complexity is Mathlib's `Omega`,
the number of prime factors counted with multiplicity; it decomposes over the finitely supported
factorization, and the prime-exponent coordinate functions are mutually independent under the
zeta law.

The source's second clause is interpretive.
此句为解读警告,不构成可形式化命题:
it specifies no model of physical computation, cost observable, or predicate saying that such a
cost obeys a law. This is not a mathematical claim whose prerequisites are absent; the clause
itself is not a mathematical assertion, so it is intentionally not formalized.

This result is related to, but distinct from, FPOD 136.1 in `PrimeChannelLogEvidence`. That module
adds expected log-likelihood evidence over prime channels. Here the summands are occupation counts
in a factorization. Log-evidence additivity cannot directly imply either the finite Omega
decomposition or independence of the occupation coordinates.

Repository totalization matters at two boundaries. Mathlib defines `Omega 0 = 0`, so the present
complexity is meaningful at zero even though zero is not a positive zeta sample. Also, a real
`tsum` of a nonsummable family is zero, not infinity. Thus the theorem at exponent one below is
stated as `Not (Summable ...)`; its bare `tsum` must not be read as an infinite expectation. At
exponent zero the closed quotient for `meanPrimeOccupancy` also totalizes division by zero, so it
has a probabilistic meaning only in the proved range `1 < s`.

Hypothesis and degeneration audit, theorem by theorem:
* The decomposition and finite-support theorems have no hypotheses. They include `n = 0` and
  `n = 1`, where both complexity and the factorization sum are zero.
* Primality is encoded by `Nat.Primes`. It is used by the prime and prime-power evaluations, by
  `measure_factorization_eq`, and by the unique-factorization proof behind independence. The
  concrete base `1` theorem shows that removing it makes both evaluations false.
* The zeta-law hypotheses `1 < s` are used to construct `zetaDist` and invoke the existing
  geometric marginal and independence theorems. In mean summability the inequality is also
  analytic load-bearing; exponent one is a concrete nonsummable counterexample.
* Empty and singleton index families are not separate input types: `iIndepFun` quantifies over all
  finite prime subfamilies, including the empty family and every singleton. The coordinate map is
  not constant, identity, or zero: its values at zero, one, and its own prime are checked below.
There are no typeclass or instance hypotheses in the public declarations. Every displayed
hypothesis is used; no weakening or deletion was available.
-/

/-- FPOD multiplicative complexity, reusing Mathlib's prime-factor count with multiplicity. -/
def multiplicativeComplexity (n : Nat) : Nat :=
  ArithmeticFunction.cardFactors n

/-- Occupation number of the prime mode `p` in the integer `n`. -/
def primeOccupancy (p : Nat.Primes) (n : Nat) : Nat :=
  n.factorization p.1

/-- Multiplicative complexity is the finite sum of the prime-factor exponents. -/
theorem multiplicativeComplexity_eq_factorization_sum (n : Nat) :
    multiplicativeComplexity n = n.factorization.sum fun _ exponent => exponent := by
  simpa [multiplicativeComplexity] using
    (ArithmeticFunction.cardFactors_eq_sum_factorization (n := n))

#print axioms multiplicativeComplexity_eq_factorization_sum

/-- For each fixed integer, only finitely many prime occupation coordinates are nonzero. -/
theorem occupied_prime_modes_finite (n : Nat) :
    Set.Finite {p : Nat.Primes | primeOccupancy p n ≠ 0} := by
  change Set.Finite (Subtype.val ⁻¹' Function.support n.factorization)
  exact n.factorization.hasFiniteSupport.preimage Subtype.coe_injective.injOn

#print axioms occupied_prime_modes_finite

/-- Zero, one, primes, and prime powers give the expected multiplicative complexities. -/
theorem multiplicative_complexity_degenerate_audit (p : Nat.Primes) (k : Nat) :
    multiplicativeComplexity 0 = 0 ∧
      multiplicativeComplexity 1 = 0 ∧
      multiplicativeComplexity p.1 = 1 ∧
      multiplicativeComplexity (p.1 ^ k) = k := by
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · simp [multiplicativeComplexity]
  · simp [multiplicativeComplexity]
  · simpa [multiplicativeComplexity] using
      (ArithmeticFunction.cardFactors_apply_prime p.2)
  · simpa [multiplicativeComplexity] using
      (ArithmeticFunction.cardFactors_apply_prime_pow p.2)

#print axioms multiplicative_complexity_degenerate_audit

/-- The primality restriction is necessary for both prime and prime-power evaluations. -/
theorem primality_is_necessary :
    multiplicativeComplexity 1 ≠ 1 ∧ multiplicativeComplexity (1 ^ 2) ≠ 2 := by
  simp [multiplicativeComplexity]

#print axioms primality_is_necessary

/-- One prime occupation has the existing geometric zeta marginal. -/
theorem prime_occupancy_geometric
    (s : Real) (hs : 1 < s) (p : Nat.Primes) (k : Nat) :
    (zetaDist s hs).toMeasure {n : Nat | primeOccupancy p n = k} =
      ENNReal.ofReal
        ((1 - (p.1 : Real) ^ (-s)) * (p.1 : Real) ^ (-(k : Real) * s)) := by
  simpa [primeOccupancy] using measure_factorization_eq s hs p.1 k p.2

#print axioms prime_occupancy_geometric

/-- All prime occupation coordinates are mutually independent under the zeta law. -/
theorem prime_occupancies_mutually_independent (s : Real) (hs : 1 < s) :
    iIndepFun primeOccupancy (zetaDist s hs).toMeasure := by
  change iIndepFun (fun p : Nat.Primes => fun n : Nat => n.factorization p.1)
    (zetaDist s hs).toMeasure
  exact iIndepFun_factorization s hs

#print axioms prime_occupancies_mutually_independent

/-- A prime coordinate is zero at zero and one, but is occupied once at its own prime. -/
theorem prime_occupancy_degenerate_audit (p : Nat.Primes) :
    primeOccupancy p 0 = 0 ∧
      primeOccupancy p 1 = 0 ∧
      primeOccupancy p p.1 = 1 := by
  simp [primeOccupancy, p.2]

#print axioms prime_occupancy_degenerate_audit

/-- The geometric mean occupation formula; it is probabilistic only when `1 < s`. -/
def meanPrimeOccupancy (s : Real) (p : Nat.Primes) : Real :=
  primeEvidence s p / (1 - primeEvidence s p)

/-- Above exponent one, the family of mean prime occupations is summable. -/
theorem mean_prime_occupancies_summable (s : Real) (hs : 1 < s) :
    Summable (meanPrimeOccupancy s) := by
  have hmajor : Summable (fun p : Nat.Primes => 2 * primeEvidence s p) :=
    (primeEvidence_summable s hs).mul_left 2
  apply Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hmajor
  · have hq0 : 0 < primeEvidence s p := primeEvidence_pos s p
    have hq1 : primeEvidence s p < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.2.one_lt) (by linarith)
    exact div_nonneg hq0.le (sub_pos.mpr hq1).le
  · let q : Real := primeEvidence s p
    have hp : 1 < (p.1 : Real) := by exact_mod_cast p.2.one_lt
    have hq0 : 0 < q := primeEvidence_pos s p
    have hq1 : q < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
    have hqhalf : q ≤ (2 : Real)⁻¹ := by
      calc
        q ≤ (p.1 : Real) ^ (-1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
        _ = (p.1 : Real)⁻¹ := Real.rpow_neg_one _
        _ ≤ (2 : Real)⁻¹ :=
          inv_anti₀ (by norm_num) (by exact_mod_cast p.2.two_le)
    dsimp [meanPrimeOccupancy, q]
    rw [div_le_iff₀ (sub_pos.mpr hq1)]
    nlinarith

#print axioms mean_prime_occupancies_summable

/-- Exponent one is a concrete counterexample to weakening the summability threshold. -/
theorem threshold_hypothesis_is_necessary :
    Not (Summable (meanPrimeOccupancy 1)) := by
  intro hmean
  apply primeEvidence_one_not_summable
  apply Summable.of_nonneg_of_le (fun p => (primeEvidence_pos 1 p).le) (fun p => ?_) hmean
  have hp : 1 < (p.1 : Real) := by exact_mod_cast p.2.one_lt
  have hq0 : 0 < primeEvidence 1 p := primeEvidence_pos 1 p
  have hq1 : primeEvidence 1 p < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  rw [meanPrimeOccupancy, le_div_iff₀ (sub_pos.mpr hq1)]
  nlinarith

#print axioms threshold_hypothesis_is_necessary

end


end D5.S3.Analytic.ZetaObservation.MultiplicativeComplexityActivation
