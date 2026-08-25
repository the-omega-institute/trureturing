/- GID: D5/S3/Analytic/ZetaObservation/FinitePrimeObservationPosterior
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/FinitePrimeObservationPosterior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite prime observations preserve disjoint cylinders and yield a coprime quotient. -/

import D5.S3.Analytic.Zeta.ZetaPrimeIndependence

/- Library-search audit trail (2026-08-25):
   * Repository exact hit `iIndepFun_factorization` in
     `Analytic/Zeta/ZetaPrimeIndependence.lean` proves mutual independence of
     the full family of `Nat.factorization` coordinates under `zetaDist`.
   * Mathlib exact hits `iIndepFun.indepFun_finset` and
     `IndepFun.measure_inter_preimage_eq_mul` turn that family result into the
     public finite-cylinder posterior equality below; both are applied
     directly rather than reproved.
   * Arithmetic exact hits `Nat.Prime.pow_dvd_iff_le_factorization`,
     `Finset.lcm_eq_prod`, `Finset.lcm_dvd`, `Nat.factorization_div`,
     `Nat.factorization_prod_apply`, `Nat.Prime.factorization_pow`,
     `Nat.coprime_prod_right_iff`, and
     `Nat.Prime.dvd_iff_one_le_factorization` provide the canonical quotient
     reconstruction and coprimality proof.
   * Repository searches for finite observed-prime factors, complementary
     quotients, and factorization cylinders found no equivalent public
     definitions. The related `PrimeExponentLanguageComplete` module exposes
     the canonical full factorization readout but no finite observed factor or
     quotient. Thus the definitions below construct the source objects from
     `Nat.factorization`; none defines an object by the theorem's conclusions.
   * The concrete zeta law and `1 < s` are essential. The cylinder equality is
     false for general correlated integer laws, as the source boundary notes. -/

namespace D5.S3.Analytic.ZetaObservation.FinitePrimeObservationPosterior

open scoped ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaPrimeIndependence

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Integers realizing specified exponent readings on a finite prime set. -/
def primeExponentCylinder
    (observed : Finset Nat.Primes) (reading : Nat.Primes -> Nat) : Set Nat :=
  {n | forall p : observed, n.factorization p.1 = reading p}

/-- The factor completely determined by the observed prime exponents. -/
def observedPrimeFactor
    (observed : Finset Nat.Primes) (reading : Nat.Primes -> Nat) : Nat :=
  ∏ p ∈ observed, p.1 ^ reading p

/-- The square-free product of the observed primes. -/
def observedPrimeProduct (observed : Finset Nat.Primes) : Nat :=
  ∏ p ∈ observed, p.1

/-- The canonical quotient remaining after removal of the observed factor. -/
def unobservedCofactor
    (observed : Finset Nat.Primes) (reading : Nat.Primes -> Nat) (n : Nat) : Nat :=
  n / observedPrimeFactor observed reading

private lemma factorization_observed_factor_apply
    (observed : Finset Nat.Primes) (reading : Nat.Primes -> Nat)
    (q : Nat.Primes) :
    (observedPrimeFactor observed reading).factorization q.1 =
      if q ∈ observed then reading q else 0 := by
  rw [observedPrimeFactor, Nat.factorization_prod_apply]
  · by_cases hq : q ∈ observed
    · rw [if_pos hq, Finset.sum_eq_single q]
      · exact Nat.factorization_pow_self q.2
      · intro p hp hpq
        rw [p.2.factorization_pow]
        have hval : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
        simp [hval]
      · exact fun hnmem => (hnmem hq).elim
    · rw [if_neg hq]
      apply Finset.sum_eq_zero
      intro p hp
      rw [p.2.factorization_pow]
      have hval : p.1 ≠ q.1 := fun h => hq (Subtype.ext h ▸ hp)
      simp [hval]
  · intro p hp
    exact pow_ne_zero _ p.2.ne_zero

/-- Conditioning on finitely many prime exponents leaves every disjoint finite
unobserved exponent cylinder unchanged. Every integer realizing the observation
is the product of its known factor and the canonical quotient; that quotient is
coprime to all observed primes and preserves every unobserved exponent. -/
theorem finite_prime_observation_posterior
    (s : Real) (hs : 1 < s)
    (observed : Finset Nat.Primes) (reading : Nat.Primes -> Nat) :
    (forall (unobserved : Finset Nat.Primes), Disjoint observed unobserved ->
      forall unobservedReading : Nat.Primes -> Nat,
        (zetaDist s hs).toMeasure
            (primeExponentCylinder observed reading ∩
              primeExponentCylinder unobserved unobservedReading) =
          (zetaDist s hs).toMeasure (primeExponentCylinder observed reading) *
            (zetaDist s hs).toMeasure
              (primeExponentCylinder unobserved unobservedReading)) ∧
    (forall n : Nat, n ≠ 0 -> n ∈ primeExponentCylinder observed reading ->
      n = observedPrimeFactor observed reading *
          unobservedCofactor observed reading n ∧
        Nat.Coprime (unobservedCofactor observed reading n)
          (observedPrimeProduct observed) ∧
        forall q : Nat.Primes, q ∉ observed ->
          (unobservedCofactor observed reading n).factorization q.1 =
            n.factorization q.1) := by
  constructor
  · intro unobserved hdisjoint unobservedReading
    have independentTuples :=
      (iIndepFun_factorization s hs).indepFun_finset
        observed unobserved hdisjoint (fun _ => measurable_of_countable _)
    have cylinderProduct := independentTuples.measure_inter_preimage_eq_mul
      ({fun p : observed => reading p} : Set (observed -> Nat))
      ({fun p : unobserved => unobservedReading p} : Set (unobserved -> Nat))
      (MeasurableSet.singleton _) (MeasurableSet.singleton _)
    have observedPreimage :
        (fun n : Nat => fun p : observed => n.factorization p.1) ⁻¹'
            ({fun p : observed => reading p} : Set (observed -> Nat)) =
          primeExponentCylinder observed reading := by
      ext n
      constructor
      · intro hn p
        exact congrFun hn p
      · intro hn
        funext p
        exact hn p
    have unobservedPreimage :
        (fun n : Nat => fun p : unobserved => n.factorization p.1) ⁻¹'
            ({fun p : unobserved => unobservedReading p} :
              Set (unobserved -> Nat)) =
          primeExponentCylinder unobserved unobservedReading := by
      ext n
      constructor
      · intro hn p
        exact congrFun hn p
      · intro hn
        funext p
        exact hn p
    rw [observedPreimage, unobservedPreimage] at cylinderProduct
    exact cylinderProduct
  · intro n hn realizesObservation
    have pairwiseCoprime : (observed : Set Nat.Primes).Pairwise
        (Nat.Coprime.onFun fun p => p.1 ^ reading p) := by
      intro p hp q hq hpq
      exact Nat.coprime_pow_primes _ _ p.2 q.2
        (fun h => hpq (Subtype.ext h))
    have observedFactorDvd : observedPrimeFactor observed reading ∣ n := by
      rw [observedPrimeFactor, ← Finset.lcm_eq_prod pairwiseCoprime]
      exact Finset.lcm_dvd fun p hp =>
        p.2.pow_dvd_iff_le_factorization hn |>.2
          (realizesObservation ⟨p, hp⟩).ge
    have observedFactorPos : 0 < observedPrimeFactor observed reading := by
      rw [observedPrimeFactor]
      apply Finset.prod_pos
      intro p hp
      exact pow_pos p.2.pos _
    have cofactorNe : unobservedCofactor observed reading n ≠ 0 := by
      apply (Nat.div_pos
        (Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hn) observedFactorDvd)
        observedFactorPos).ne'
    have unobservedFactorization (q : Nat.Primes) (hq : q ∉ observed) :
        (unobservedCofactor observed reading n).factorization q.1 =
          n.factorization q.1 := by
      rw [unobservedCofactor, Nat.factorization_div observedFactorDvd,
        Finsupp.tsub_apply, factorization_observed_factor_apply, if_neg hq,
        Nat.sub_zero]
    have observedFactorizationZero (p : Nat.Primes) (hp : p ∈ observed) :
        (unobservedCofactor observed reading n).factorization p.1 = 0 := by
      rw [unobservedCofactor, Nat.factorization_div observedFactorDvd,
        Finsupp.tsub_apply, factorization_observed_factor_apply, if_pos hp,
        realizesObservation ⟨p, hp⟩, Nat.sub_self]
    refine ⟨?_, ?_, unobservedFactorization⟩
    · rw [unobservedCofactor, mul_comm, Nat.div_mul_cancel observedFactorDvd]
    · rw [observedPrimeProduct, Nat.coprime_prod_right_iff]
      intro p hp
      apply (p.2.coprime_iff_not_dvd.mpr ?_).symm
      intro pDvdCofactor
      have positiveFactorization :=
        p.2.dvd_iff_one_le_factorization cofactorNe |>.mp pDvdCofactor
      rw [observedFactorizationZero p hp] at positiveFactorization
      omega

#print axioms primeExponentCylinder
#print axioms observedPrimeFactor
#print axioms observedPrimeProduct
#print axioms unobservedCofactor
#print axioms finite_prime_observation_posterior

end

end D5.S3.Analytic.ZetaObservation.FinitePrimeObservationPosterior
