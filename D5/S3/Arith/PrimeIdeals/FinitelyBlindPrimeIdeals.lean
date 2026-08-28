/- GID: D5/S3/Arith/PrimeIdeals/FinitelyBlindPrimeIdeals
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeIdeals/FinitelyBlindPrimeIdeals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dedekind reductions coincide on divisors; blind sets finite; unit and Z cases audited. -/

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib searches hit `IsDedekindDomain`, `Ideal.IsPrime`,
     `NumberField.RingOfIntegers`, `Ideal.Quotient.mk`, and `Nat.Prime`.
   * The exact APIs used below are `Ideal.Quotient.mk_eq_mk_iff_sub_mem`,
     `Ideal.dvd_span_singleton`, and `Ideal.finite_factors`.
   * Searches also checked `UniqueFactorizationMonoid.factors`, `Ideal.factors`,
     and `UniqueFactorizationMonoid.finite_factors`; they were not needed because
     `Ideal.finite_factors` directly supplies the required finite exceptional set.
   * No existing repository declaration packages this reduction/divisor theorem or
     the all-prime coarse-property counterexample.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.PrimeIdeals.FinitelyBlindPrimeIdeals

open IsDedekindDomain

/-- Reduction of an element at a nonzero prime ideal of a Dedekind domain. -/
def primeIdealReduction {R : Type*} [CommRing R]
    (v : HeightOneSpectrum R) : R →+* (R ⧸ v.asIdeal) :=
  Ideal.Quotient.mk v.asIdeal

/-- The set of prime ideals whose reductions identify two elements. -/
def blindPrimeIdeals {R : Type*} [CommRing R]
    (a b : R) : Set (HeightOneSpectrum R) :=
  {v | primeIdealReduction v a = primeIdealReduction v b}

/-- Vanishing of the reduction is the coarse property used in the integer counterexample. -/
def zeroReductionObservation {R : Type*} [CommRing R]
    (v : HeightOneSpectrum R) (a : R) : Prop :=
  primeIdealReduction v a = 0

/-- Reduction equality is equivalent to divisibility of the principal difference ideal. -/
theorem reduction_eq_iff_dvd_difference {R : Type*} [CommRing R]
    [IsDedekindDomain R] (v : HeightOneSpectrum R) (a b : R) :
    primeIdealReduction v a = primeIdealReduction v b ↔
      v.asIdeal ∣ Ideal.span {a - b} := by
  rw [primeIdealReduction, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    Ideal.dvd_span_singleton]

#print axioms reduction_eq_iff_dvd_difference

/-- The prime ideals identifying distinct elements form a finite set. -/
theorem finite_blind_prime_ideals {R : Type*} [CommRing R]
    [IsDedekindDomain R] {a b : R} (hab : a ≠ b) :
    (blindPrimeIdeals a b).Finite := by
  have hdiff : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hspan : Ideal.span {a - b} ≠ (0 : Ideal R) := by
    intro h
    apply hdiff
    apply Ideal.span_singleton_eq_bot.mp
    simpa using h
  rw [blindPrimeIdeals]
  refine (Ideal.finite_factors hspan).subset ?_
  intro v hv
  exact (reduction_eq_iff_dvd_difference v a b).mp hv

#print axioms finite_blind_prime_ideals

/-- A unit difference has no blind prime ideal. -/
theorem unit_difference_has_no_blind_prime_ideals {R : Type*} [CommRing R]
    [IsDedekindDomain R] {a b : R} (hu : IsUnit (a - b)) :
    blindPrimeIdeals a b = ∅ := by
  ext v
  constructor
  · intro hv
    have hdiv := (reduction_eq_iff_dvd_difference v a b).mp hv
    have hmem : a - b ∈ v.asIdeal := Ideal.dvd_span_singleton.mp hdiv
    exact (v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)).elim
  · intro hv
    have hfalse : False := (Set.mem_empty_iff_false v).mp hv
    exact hfalse.elim

#print axioms unit_difference_has_no_blind_prime_ideals

/-- In `Z`, distinct global elements can share the zero/nonzero reduction property everywhere. -/
theorem coarse_zero_observation_counterexample :
    (1 : ℤ) ≠ -1 ∧
      ∀ v : HeightOneSpectrum ℤ,
        zeroReductionObservation v (1 : ℤ) ↔
          zeroReductionObservation v (-1 : ℤ) := by
  constructor
  · norm_num
  · intro v
    have h_one : ¬ zeroReductionObservation v (1 : ℤ) := by
      intro h
      have hmem : (1 : ℤ) ∈ v.asIdeal :=
        (Ideal.Quotient.eq_zero_iff_mem).mp h
      exact v.isPrime.one_notMem hmem
    have h_neg_one : ¬ zeroReductionObservation v (-1 : ℤ) := by
      intro h
      have hmem : (-1 : ℤ) ∈ v.asIdeal :=
        (Ideal.Quotient.eq_zero_iff_mem).mp h
      exact v.isPrime.one_notMem (neg_mem_iff.mp hmem)
    exact iff_of_false h_one h_neg_one

#print axioms coarse_zero_observation_counterexample

/-- Without distinct global elements, no prime ideal can distinguish the two inputs. -/
theorem distinctness_is_necessary_for_separation :
    ¬ ∃ v : HeightOneSpectrum ℤ,
      primeIdealReduction v (0 : ℤ) ≠ primeIdealReduction v 0 := by
  simp

#print axioms distinctness_is_necessary_for_separation

section DegenerateAudit

-- Equal elements are excluded exactly because their difference is zero.
example {R : Type*} [CommRing R] [IsDedekindDomain R] (a : R) :
    blindPrimeIdeals a a = Set.univ := by
  ext v
  simp [blindPrimeIdeals]

-- A unit difference gives the empty exceptional set, including the `1 - 0` case in `Z`.
example : blindPrimeIdeals (1 : ℤ) 0 = ∅ := by
  apply unit_difference_has_no_blind_prime_ideals
  norm_num

-- The concrete `Z` specialization is the `𝓞_K = Z` audit; no number-field parameters are used.
example (a b : ℤ) (hab : a ≠ b) :
    (blindPrimeIdeals a b).Finite := by
  exact finite_blind_prime_ideals hab

-- Empty and singleton index types, constant maps, and zero maps are inapplicable:
-- the declarations quantify over elements and prime ideals of a fixed commutative ring.

end DegenerateAudit

end D5.S3.Arith.PrimeIdeals.FinitelyBlindPrimeIdeals

/- Conclusion and audits:
   * This is level (a): the statements are generalized to arbitrary commutative Dedekind domains.
     Number-field notation `𝓞_K` is a specialization, so no stronger field or fraction-ring
     hypotheses are claimed; those unused hypotheses were removed from every declaration.
   * Prime-ideal support uses primality/properness through `HeightOneSpectrum.isPrime` and
     finiteness through the library theorem `Ideal.finite_factors`; unique factorization is not
     used directly. The quotient equality uses `Ideal.Quotient.mk_eq_mk_iff_sub_mem`, and the
     Dedekind bridge from membership to ideal divisibility uses `Ideal.dvd_span_singleton`.
   * The unit difference audit is `unit_difference_has_no_blind_prime_ideals`; the `𝓞_K = ℤ`
     audit and the all-prime coarse-property counterexample are concrete named theorems above.
     Empty or singleton index types and constant/zero maps are inapplicable to this fixed-ring
     formulation; equal inputs are separately audited and cannot be separated.
-/
