/- GID: D5/S3/Factorization/Embeddings/FiniteValuationPortraitObjectLayer
   generality: I
   mirror-B: D5/B/S3/Factorization/Embeddings/FiniteValuationPortraitObjectLayer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime portraits recover principal ideals; zero and composite cases are audited. -/
/- Library-search audit trail (2026-08-25):
   * The FPOD source was checked at `FORMAL_PRIME_OBSERVER_DYNAMICS.md`, Sections 178 and 180.
   * D5 hits were `RationalValuationRecovery`, `DirichletUnitCompletion`,
     `FractionalIdealPrimeValuationFaithfulness`, `IdealIdentityPrincipalityGeneratorLayers`,
     and `ThreeCompletionOrthogonality`; their relevant declarations are reused below.
   * Pinned Mathlib's exact reconstruction hit
     `FractionalIdeal.finprod_heightOneSpectrum_factorization'` is applied directly.
   * `FractionalIdeal.spanSingleton_eq_spanSingleton`, `spanSingleton_ne_zero_iff`,
     `FractionalIdeal.count`, and `HeightOneSpectrum` were exact hits and are used.
     `HeightOneSpectrum.valuation` and `Rat.RingOfIntegers.isUnit_iff` were inspected but are
     not needed: `count` is the factorization exponent, while the rational bridge must directly
     reuse the stronger signed result from `RationalValuationRecovery`.
   * No declaration named `FractionalIdeal.factorization` exists in the pinned source; the
     canonical finite-product factorization theorem above is the applicable library API.
   * Repository and local-Mathlib searches found no existing theorem combining a named element
     portrait with the universal unit-ratio iff. -/

import D5.S3.Factorization.Embeddings.DirichletUnitCompletion
import D5.S3.Factorization.Embeddings.RationalValuationRecovery
import D5.S3.Observer.Completion.ThreeCompletionOrthogonality
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped nonZeroDivisors

namespace D5.S3.Factorization.Embeddings.FiniteValuationPortraitObjectLayer

open D5.S3.Factorization.Embeddings.DirichletUnitCompletion
open D5.S3.Factorization.Embeddings.FractionalIdealPrimeValuationFaithfulness
open D5.S3.Factorization.Embeddings.RationalValuationRecovery
open D5.S3.Factorization.IdealClassGroups.IdealIdentityPrincipalityGeneratorLayers
open D5.S3.Observer.Completion.ThreeCompletionOrthogonality

/-- The integer exponents of the principal fractional ideal at all height-one prime ideals. -/
noncomputable def finiteValuationPortrait
    (R K : Type*) [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsDedekindDomain R] (x : K) :
    IsDedekindDomain.HeightOneSpectrum R → ℤ :=
  fun prime => FractionalIdeal.count K prime (FractionalIdeal.spanSingleton R⁰ x)

/-- The quotient `x / y` is the image of a unit of the chosen base ring. -/
def IsBaseUnitRatio
    (R K : Type*) [CommSemiring R] [DivisionSemiring K] [Algebra R K]
    (x y : K) : Prop :=
  ∃ unit : Rˣ, x / y = algebraMap R K (unit : R)

/-- A nonzero principal fractional ideal is the finite product of its prime-ideal powers. -/
theorem principal_fractional_ideal_reconstruction
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsDedekindDomain R] {x : K} (hx : x ≠ 0) :
    FractionalIdeal.spanSingleton R⁰ x =
      ∏ᶠ prime : IsDedekindDomain.HeightOneSpectrum R,
        (prime.asIdeal : FractionalIdeal R⁰ K) ^ finiteValuationPortrait R K x prime := by
  exact (FractionalIdeal.finprod_heightOneSpectrum_factorization' K
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)).symm
#print axioms principal_fractional_ideal_reconstruction

/-- The reconstruction formula fails at zero because `count` is totalized there. -/
theorem reconstruction_nonzero_hypothesis_is_necessary :
    FractionalIdeal.spanSingleton ℤ⁰ (0 : ℚ) ≠
      ∏ᶠ prime : IsDedekindDomain.HeightOneSpectrum ℤ,
        (prime.asIdeal : FractionalIdeal ℤ⁰ ℚ) ^
          finiteValuationPortrait ℤ ℚ 0 prime := by
  simp [finiteValuationPortrait, FractionalIdeal.count_zero]
#print axioms reconstruction_nonzero_hypothesis_is_necessary

/-- Equal finite-prime portraits are exactly quotients by units of the base Dedekind domain.

Primality is load-bearing in `prime_valuation_observers_faithful`: the height-one points are
nonzero prime ideals, and Dedekind unique factorization reconstructs each fractional ideal from
their exponents. The composite-modulus theorem below shows that an arbitrary nonprime readout
does not have this faithfulness property.
-/
theorem finite_valuation_portrait_eq_iff_base_unit_ratio
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsDedekindDomain R]
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    finiteValuationPortrait R K x = finiteValuationPortrait R K y ↔
      IsBaseUnitRatio R K x y := by
  constructor
  · intro samePortrait
    have sameIdeal :
        FractionalIdeal.spanSingleton R⁰ x = FractionalIdeal.spanSingleton R⁰ y := by
      have sameSubtype := prime_valuation_observers_faithful
        ⟨FractionalIdeal.spanSingleton R⁰ x,
          FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx⟩
        ⟨FractionalIdeal.spanSingleton R⁰ y,
          FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy⟩
        (fun prime => congrFun samePortrait prime)
      exact congrArg Subtype.val sameSubtype
    obtain ⟨unit, unitMultiple⟩ :=
      FractionalIdeal.spanSingleton_eq_spanSingleton.mp sameIdeal.symm
    refine ⟨unit, ?_⟩
    rw [← unitMultiple, Units.smul_def, Algebra.smul_def,
      mul_div_cancel_right₀ _ hy]
  · rintro ⟨unit, ratioIsUnit⟩
    have unitMultiple : (unit : R) • y = x := by
      rw [Algebra.smul_def, ← ratioIsUnit]
      exact div_mul_cancel₀ x hy
    have sameIdeal :
        FractionalIdeal.spanSingleton R⁰ x = FractionalIdeal.spanSingleton R⁰ y := by
      symm
      exact FractionalIdeal.spanSingleton_eq_spanSingleton.mpr ⟨unit, unitMultiple⟩
    funext prime
    simp only [finiteValuationPortrait]
    rw [sameIdeal]
#print axioms finite_valuation_portrait_eq_iff_base_unit_ratio

/-- Every nonzero ideal satisfies the identity-completion predicate imported from Section 108. -/
theorem nonzero_ideal_has_prime_valuation_identity_completion
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ≠ ⊥) : PrimeValuationIdentityCompletion I := by
  refine ⟨hI, ?_⟩
  intro J hJ sameValuation
  have sameFractional :
      (J : FractionalIdeal R⁰ (FractionRing R)) =
        (I : FractionalIdeal R⁰ (FractionRing R)) :=
    congrArg Subtype.val
      (ideal_valuation_layer_recovers_fractional_ideal
        ⟨(J : FractionalIdeal R⁰ (FractionRing R)),
          FractionalIdeal.coeIdeal_ne_zero.mpr hJ⟩
        ⟨(I : FractionalIdeal R⁰ (FractionRing R)),
          FractionalIdeal.coeIdeal_ne_zero.mpr hI⟩
        sameValuation)
  exact FractionalIdeal.coeIdeal_injective sameFractional
#print axioms nonzero_ideal_has_prime_valuation_identity_completion

/-- The nonzero premise in identity completion excludes the zero ideal. -/
theorem nonzero_ideal_hypothesis_is_necessary :
    ¬ PrimeValuationIdentityCompletion (⊥ : Ideal ℤ) := by
  exact fun completion => completion.1 rfl
#print axioms nonzero_ideal_hypothesis_is_necessary

/-- Over `ℚ`, the finite portrait leaves rank zero and exactly the two signs. -/
theorem rational_finite_profile_eq_iff_rank_zero_sign
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    rationalFiniteValuationProfile x = rationalFiniteValuationProfile y ↔
      NumberField.Units.rank ℚ = 0 ∧ (x = y ∨ x = -y) := by
  constructor
  · intro samePortrait
    exact ⟨rational_unit_rank_zero,
      abs_eq_abs.mp
        ((rational_finite_valuation_profile_eq_iff_abs_eq hx hy).mp samePortrait)⟩
  · rintro ⟨_, sameSign⟩
    apply (rational_finite_valuation_profile_eq_iff_abs_eq hx hy).mpr
    rcases sameSign with same | opposite
    · rw [same]
    · rw [opposite, abs_neg]
#print axioms rational_finite_profile_eq_iff_rank_zero_sign

/-- Both nonzero hypotheses are necessary because the valuation of zero is totalized to zero. -/
theorem nonzero_hypotheses_are_necessary :
    (finiteValuationPortrait ℤ ℚ 0 = finiteValuationPortrait ℤ ℚ 1 ∧
      ¬ IsBaseUnitRatio ℤ ℚ 0 1) ∧
    (finiteValuationPortrait ℤ ℚ 1 = finiteValuationPortrait ℤ ℚ 0 ∧
      ¬ IsBaseUnitRatio ℤ ℚ 1 0) := by
  constructor
  · constructor
    · ext prime
      simp [finiteValuationPortrait, FractionalIdeal.count_zero,
        FractionalIdeal.count_one]
    · rintro ⟨unit, ratioIsUnit⟩
      norm_num only [zero_div] at ratioIsUnit
      change (0 : ℚ) = ((unit : ℤ) : ℚ) at ratioIsUnit
      rcases Int.isUnit_eq_one_or unit.isUnit with unitIsOne | unitIsNegOne
      · norm_num [unitIsOne] at ratioIsUnit
      · norm_num [unitIsNegOne] at ratioIsUnit
  · constructor
    · ext prime
      simp [finiteValuationPortrait, FractionalIdeal.count_zero,
        FractionalIdeal.count_one]
    · rintro ⟨unit, ratioIsUnit⟩
      norm_num only [div_zero] at ratioIsUnit
      change (0 : ℚ) = ((unit : ℤ) : ℚ) at ratioIsUnit
      rcases Int.isUnit_eq_one_or unit.isUnit with unitIsOne | unitIsNegOne
      · norm_num [unitIsOne] at ratioIsUnit
      · norm_num [unitIsNegOne] at ratioIsUnit
#print axioms nonzero_hypotheses_are_necessary

/-- Replacing a prime coordinate by the composite modulus four destroys faithfulness. -/
theorem composite_readout_is_not_faithful :
    padicValRat 4 (1 : ℚ) = padicValRat 4 2 ∧
      ¬ IsBaseUnitRatio ℤ ℚ 1 2 := by
  constructor
  · have fourDoesNotDivideTwo : ¬ 4 ∣ 2 := by norm_num
    have valueAtTwo : padicValNat 4 2 = 0 :=
      padicValNat.eq_zero_of_not_dvd fourDoesNotDivideTwo
    norm_num [padicValRat, padicValInt, valueAtTwo]
  · rintro ⟨unit, ratioIsUnit⟩
    change (1 : ℚ) / 2 = ((unit : ℤ) : ℚ) at ratioIsUnit
    rcases Int.isUnit_eq_one_or unit.isUnit with unitIsOne | unitIsNegOne
    · norm_num [unitIsOne] at ratioIsUnit
    · norm_num [unitIsNegOne] at ratioIsUnit
#print axioms composite_readout_is_not_faithful

/- Degenerate audit:
   * `x = y` is the identity case of the iff; a unit multiple is exercised below over the PID `ℤ`.
   * Class number one is not assumed: the theorem remains valid over `ℤ` and all number fields.
   * A field used as its own base ring has empty height-one spectrum; its constant portrait is
     correct because every nonzero quotient is a base-ring unit.
   * Empty and singleton field carriers are impossible (`Field` supplies `Nonempty` and
     `Nontrivial`). The zero portrait is the named counterexample above. There is no `n` input,
     so an `n = 0` case is inapplicable. -/
example {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsDedekindDomain R] {x : K} (hx : x ≠ 0) :
    finiteValuationPortrait R K x = finiteValuationPortrait R K x ∧
      IsBaseUnitRatio R K x x := by
  exact ⟨rfl, (finite_valuation_portrait_eq_iff_base_unit_ratio hx hx).mp rfl⟩

example :
    finiteValuationPortrait ℤ ℚ 1 = finiteValuationPortrait ℤ ℚ (-1) ∧
      IsBaseUnitRatio ℤ ℚ 1 (-1) := by
  have unitRatio : IsBaseUnitRatio ℤ ℚ 1 (-1) := by
    exact ⟨(-1 : ℤˣ), by norm_num⟩
  exact ⟨(finite_valuation_portrait_eq_iff_base_unit_ratio
    (R := ℤ) (K := ℚ) (by norm_num) (by norm_num)).mpr unitRatio, unitRatio⟩

example : IsEmpty (IsDedekindDomain.HeightOneSpectrum ℚ) :=
  ⟨fun prime => by
    rcases Ideal.eq_bot_or_top prime.asIdeal with h | h
    · exact prime.ne_bot h
    · exact prime.isPrime.ne_top h⟩

example (K : Type*) [Field K] : Nonempty K ∧ Nontrivial K :=
  ⟨inferInstance, inferInstance⟩

end D5.S3.Factorization.Embeddings.FiniteValuationPortraitObjectLayer
