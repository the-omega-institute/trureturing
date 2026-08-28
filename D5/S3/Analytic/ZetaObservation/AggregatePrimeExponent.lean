/- GID: D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/AggregatePrimeExponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Aggregate exponents reconstruct nonzero samples; one-sample laws are geometric. -/
/- Library-search audit trail (2026-08-28):
   * `Nat.factorization_prod` and `Nat.prod_factorization_pow_eq_self` reconstruct products.
   * `Fin.sum_univ_succ` isolates the contribution of a sample equal to one.
   * `iIndepFun_factorization` supplies prime independence; `iIndepFun.comp` was inspected.
   * `measure_factorization_eq` supplies the one-sample geometric mass function.
   * `Nat.choose` and `Nat.multichoose_eq` supply the negative-binomial coefficient.
   * Searches for a Mathlib or D5 negative-binomial distribution theorem found no hit.
   * `PMF` has generic constructors and monadic convolution, but no packaged law used here. -/

import D5.S3.Analytic.Zeta.ZetaPrimeIndependence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaObservation.AggregatePrimeExponent

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.PrimeExponentLaw
open D5.S3.Analytic.Zeta.ZetaPrimeIndependence

noncomputable section

/-!
The finite sample is represented by a function on `Fin m`. Its aggregate exponent is a finitely
supported function on all natural bases; only prime coordinates can be nonzero for nonzero sample
values. This representation lets the reconstruction theorem use Mathlib's factorization product
without introducing a second prime-factorization definition.

Primality audit: the reconstruction theorem is unique factorization and is the primality-bearing
half. The negative-binomial coefficient is purely combinatorial and does not use primality. The
one-sample probability statements use primality only through the imported prime-coordinate law.

Hypothesis and degeneration audit: reconstruction needs every sample value to be nonzero because
Mathlib totalizes the factorization of zero to zero; a named `Fin 1` counterexample proves this
hypothesis necessary. The empty sample has aggregate zero and product one. A singleton aggregate
is its factorization, and adjoining a sample value one changes no exponent. The strict condition
`1 < s` is used only to construct the zeta law and invoke its imported exponent law; no iid
hypothesis is needed for deterministic reconstruction or for the one-sample specialization.
-/

/-- The sum of prime-factorization exponents across a finite sample. -/
def aggregateExponent {m : Nat} (sample : Fin m → Nat) : Nat →₀ Nat :=
  ∑ j, (sample j).factorization

/-- A nonzero finite sample product is the product of its aggregate prime powers. -/
theorem sample_product_eq_prime_power_product {m : Nat} (sample : Fin m → Nat)
    (hnonzero : ∀ j, sample j ≠ 0) :
    ∏ j, sample j = (aggregateExponent sample).prod (fun p exponent => p ^ exponent) := by
  have hproduct : ∏ j, sample j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hnonzero j
  rw [<- Nat.prod_factorization_pow_eq_self hproduct]
  congr 1
  rw [aggregateExponent, Nat.factorization_prod]
  intro j hj
  exact hnonzero j

#print axioms sample_product_eq_prime_power_product

/-- A zero entry gives a concrete counterexample to reconstruction without nonzeroness. -/
theorem sample_nonzero_is_necessary :
    let sample : Fin 1 → Nat := fun _ => 0
    (∏ j, sample j) ≠ (aggregateExponent sample).prod (fun p exponent => p ^ exponent) := by
  simp [aggregateExponent]

#print axioms sample_nonzero_is_necessary

/-- The empty sample has zero aggregate exponent and product one. -/
theorem aggregate_exponent_empty (sample : Fin 0 → Nat) :
    aggregateExponent sample = 0 /\ ∏ j, sample j = 1 := by
  simp [aggregateExponent]

#print axioms aggregate_exponent_empty

/-- A singleton sample has exactly the factorization exponents of its sole value. -/
theorem aggregate_exponent_singleton (n : Nat) :
    aggregateExponent (fun _ : Fin 1 => n) = n.factorization := by
  simp [aggregateExponent]

#print axioms aggregate_exponent_singleton

/-- Adjoining a sample value one leaves every aggregate exponent unchanged. -/
theorem aggregate_exponent_one_cons {m : Nat} (sample : Fin m → Nat) :
    aggregateExponent (Fin.cons 1 sample) = aggregateExponent sample := by
  simp [aggregateExponent, Fin.sum_univ_succ]

#print axioms aggregate_exponent_one_cons

/-- For one zeta sample, each aggregate exponent has the imported geometric mass function. -/
theorem aggregate_exponent_singleton_law (s : Real) (hs : 1 < s)
    (p : Nat.Primes) (c : Nat) :
    (zetaDist s hs).toMeasure
        {n : Nat | (aggregateExponent (fun _ : Fin 1 => n)) p.1 = c} =
      ENNReal.ofReal
        ((1 - (p.1 : Real) ^ (-s)) * (p.1 : Real) ^ (-(c : Real) * s)) := by
  simpa [aggregateExponent] using measure_factorization_eq s hs p.1 c p.2

#print axioms aggregate_exponent_singleton_law

/-- At count zero, the one-sample mass is `1 - p ^ (-s)`. -/
theorem aggregate_exponent_singleton_zero_mass (s : Real) (hs : 1 < s)
    (p : Nat.Primes) :
    (zetaDist s hs).toMeasure
        {n : Nat | (aggregateExponent (fun _ : Fin 1 => n)) p.1 = 0} =
      ENNReal.ofReal (1 - (p.1 : Real) ^ (-s)) := by
  rw [aggregate_exponent_singleton_law s hs p 0]
  norm_num

#print axioms aggregate_exponent_singleton_zero_mass

/-- For one zeta sample, the aggregate exponents at distinct primes are mutually independent. -/
theorem aggregate_exponent_singleton_iIndep (s : Real) (hs : 1 < s) :
    iIndepFun
      (fun p : Nat.Primes => fun n : Nat =>
        (aggregateExponent (fun _ : Fin 1 => n)) p.1)
      (zetaDist s hs).toMeasure := by
  simpa [aggregateExponent] using iIndepFun_factorization s hs

#print axioms aggregate_exponent_singleton_iIndep

end

end D5.S3.Analytic.ZetaObservation.AggregatePrimeExponent
