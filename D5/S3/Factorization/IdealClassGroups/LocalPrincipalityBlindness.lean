/- GID: D5/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness
   generality: I
   mirror-B: D5/B/S3/Factorization/IdealClassGroups/LocalPrincipalityBlindness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dedekind local readouts are true; PIDs and zero primes expose degeneracies. -/
/- Library-search audit trail (2026-08-25):
   * Current-tree searches for `IsLocalization.AtPrime`, local principality, and the named
     quadratic witness found `NormTwoIdealLocalGlobalGap`. It proves the concrete gap by a direct
     calculation because the tree has no Dedekind instance for `QuadraticOrder`; that theorem is
     imported for the witness rather than reconstructed.
   * `IdealRecoveryNotPrincipality` and `IdealIdentityPrincipalityGeneratorLayers` reuse the same
     witness, but neither states the general Dedekind/DVR result or names the local readout.
   * Pinned Mathlib provides the exact DVR step as
     `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`. A DVR extends
     `IsPrincipalIdealRing`, and `FractionalIdeal.isPrincipal` then handles every fractional ideal.
   * `FractionalIdeal.extendedHom` is the canonical localization operation used below.
     `Submodule.IsPrincipal` and `Ideal.IsPrincipal` are used according to the object represented.
   * `ClassGroup.mk0_surjective` and `ClassGroup.mk0_eq_one_iff` extract a nonprincipal ideal from
     a nontrivial class group. `card_classGroup_eq_one` gives the exact PID degeneration.
     Searches for `HeightOneSpectrum` found adjacent valuation observers, but no theorem equivalent
     to the general local-readout blindness statement below.
   * Strength: the general all-true result is proved, and the existing concrete quadratic witness
     gives a principal/nonprincipal pair with identical readouts. No new class-group witness is
     constructed. -/

import D5.S3.Factorization.QuadraticIdeals.NormTwoIdealLocalGlobalGap
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.FractionalIdeal.Extended

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped nonZeroDivisors

namespace D5.S3.Factorization.IdealClassGroups.LocalPrincipalityBlindness

open D5.S3.Factorization.QuadraticIdeals.NormTwoIdeal
open D5.S3.Factorization.QuadraticIdeals.NormTwoIdealLocalGlobalGap

universe u

/-- The extension of a fractional ideal to the fraction field of a prime localization. -/
noncomputable def localizedFractionalIdealAtPrime
    {R : Type u} [CommRing R] [IsDomain R]
    (prime : PrimeSpectrum R)
    (I : FractionalIdeal R⁰ (FractionRing R)) :
    FractionalIdeal (Localization.AtPrime prime.asIdeal)⁰
      (FractionRing (Localization.AtPrime prime.asIdeal)) :=
  FractionalIdeal.extendedHom
    (FractionRing (Localization.AtPrime prime.asIdeal))
    (Localization.AtPrime prime.asIdeal) I

/-- The Boolean-valued proposition that an ideal becomes principal at one prime localization. -/
def localPrincipalityReadout
    {R : Type u} [CommRing R]
    (prime : PrimeSpectrum R)
    (I : Ideal R) : Prop :=
  (I.map (algebraMap R (Localization.AtPrime prime.asIdeal))).IsPrincipal

/-- A Dedekind domain localized at a nonzero prime ideal is a DVR. -/
theorem localization_at_nonzero_prime_is_dvr
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (prime : {p : PrimeSpectrum R // p.asIdeal ≠ ⊥}) :
    IsDiscreteValuationRing (Localization.AtPrime prime.1.asIdeal) := by
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    R prime.2 _
#print axioms localization_at_nonzero_prime_is_dvr

/-- Every localized fractional ideal is principal; the ideal need not be nonzero. -/
theorem localized_fractional_ideal_is_principal
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (prime : {p : PrimeSpectrum R // p.asIdeal ≠ ⊥})
    (I : FractionalIdeal R⁰ (FractionRing R)) :
    (localizedFractionalIdealAtPrime prime.1 I :
      Submodule (Localization.AtPrime prime.1.asIdeal)
        (FractionRing (Localization.AtPrime prime.1.asIdeal))).IsPrincipal := by
  letI : IsDiscreteValuationRing (Localization.AtPrime prime.1.asIdeal) :=
    localization_at_nonzero_prime_is_dvr prime
  exact FractionalIdeal.isPrincipal _
#print axioms localized_fractional_ideal_is_principal

/-- The named local-principality readout is true for every ideal. -/
theorem local_principality_readout_is_true
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (prime : {p : PrimeSpectrum R // p.asIdeal ≠ ⊥})
    (I : Ideal R) : localPrincipalityReadout prime.1 I ↔ True := by
  rw [iff_true]
  letI : IsDiscreteValuationRing (Localization.AtPrime prime.1.asIdeal) :=
    localization_at_nonzero_prime_is_dvr prime
  exact IsPrincipalIdealRing.principal _
#print axioms local_principality_readout_is_true

/-- A nontrivial class group supplies a principal/nonprincipal pair with identical readouts. -/
theorem local_principality_observers_are_blind_of_nontrivial_class_group
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    [Nontrivial (ClassGroup R)] :
    ∃ nonprincipal principal : Ideal R,
      ¬ nonprincipal.IsPrincipal ∧ principal.IsPrincipal ∧
      ∀ prime : {p : PrimeSpectrum R // p.asIdeal ≠ ⊥},
        localPrincipalityReadout prime.1 nonprincipal ↔
          localPrincipalityReadout prime.1 principal := by
  obtain ⟨idealClass, idealClass_ne_one⟩ := exists_ne (1 : ClassGroup R)
  obtain ⟨nonprincipal, class_spec⟩ := ClassGroup.mk0_surjective idealClass
  have not_principal : ¬ nonprincipal.1.IsPrincipal := by
    intro principal
    have class_eq_one : ClassGroup.mk0 nonprincipal = 1 :=
      (ClassGroup.mk0_eq_one_iff nonprincipal.2).2 principal
    exact idealClass_ne_one (class_spec.symm.trans class_eq_one)
  refine ⟨nonprincipal.1, ⊤, not_principal, top_isPrincipal, ?_⟩
  intro prime
  rw [local_principality_readout_is_true prime nonprincipal.1,
    local_principality_readout_is_true prime ⊤]
#print axioms local_principality_observers_are_blind_of_nontrivial_class_group

/-- All nonzero-prime local readouts identify a nonprincipal ideal with a principal ideal. -/
theorem local_principality_observers_are_blind :
    ∃ nonprincipal principal : Ideal QuadraticOrder,
      ¬ nonprincipal.IsPrincipal ∧ principal.IsPrincipal ∧
      ∀ prime : {p : PrimeSpectrum QuadraticOrder // p.asIdeal ≠ ⊥},
        localPrincipalityReadout prime.1 nonprincipal ↔
          localPrincipalityReadout prime.1 principal := by
  refine ⟨normTwoIdeal, ⊤, norm_two_ideal_local_global_gap.2.1,
    top_isPrincipal, ?_⟩
  intro prime
  constructor
  · intro _
    rw [localPrincipalityReadout, Ideal.map_top]
    exact top_isPrincipal
  · intro _
    exact norm_two_ideal_local_global_gap.1 prime
#print axioms local_principality_observers_are_blind

/-- The PID degeneration has class number one and cannot contain the required mixed pair. -/
theorem pid_blindness_witness_is_impossible :
    Fintype.card (ClassGroup ℤ) = 1 ∧
      ¬ ∃ nonprincipal principal : Ideal ℤ,
        ¬ nonprincipal.IsPrincipal ∧ principal.IsPrincipal ∧
        ∀ prime : {p : PrimeSpectrum ℤ // p.asIdeal ≠ ⊥},
          localPrincipalityReadout prime.1 nonprincipal ↔
            localPrincipalityReadout prime.1 principal := by
  refine ⟨card_classGroup_eq_one, ?_⟩
  rintro ⟨nonprincipal, _, not_principal, _, _⟩
  exact not_principal (IsPrincipalIdealRing.principal nonprincipal)
#print axioms pid_blindness_witness_is_impossible

/-- The nonzero-prime hypothesis is necessary for the DVR conclusion. -/
theorem zero_prime_is_not_a_dvr
    {R : Type u} [CommRing R] [IsDomain R] :
    ¬ IsDiscreteValuationRing (Localization.AtPrime (⊥ : Ideal R)) := by
  intro dvr
  letI : IsDiscreteValuationRing (Localization.AtPrime (⊥ : Ideal R)) := dvr
  apply IsDiscreteValuationRing.not_a_field
    (Localization.AtPrime (⊥ : Ideal R))
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  simp
#print axioms zero_prime_is_not_a_dvr

/-- Zero and unit ideals are globally principal and also receive true local readouts. -/
theorem zero_and_unit_ideal_readouts_are_true
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (prime : {p : PrimeSpectrum R // p.asIdeal ≠ ⊥}) :
    ((⊥ : Ideal R).IsPrincipal ∧ (⊤ : Ideal R).IsPrincipal) ∧
      (localPrincipalityReadout prime.1 ⊥ ∧
        localPrincipalityReadout prime.1 ⊤) := by
  constructor
  · exact ⟨bot_isPrincipal, top_isPrincipal⟩
  · constructor
    · exact (local_principality_readout_is_true prime ⊥).2 trivial
    · exact (local_principality_readout_is_true prime ⊤).2 trivial
#print axioms zero_and_unit_ideal_readouts_are_true

/- Degenerate-input audit: a carrier with zero is nonempty; a Dedekind domain is also nontrivial.
The singleton semiring has only principal ideals. There is no function or natural-number parameter
in the public statements; the identity and constant-map probes below make those absent cases
explicit, while the zero-ideal input is covered by `zero_and_unit_ideal_readouts_are_true`. -/
example {R : Type u} [Zero R] : Nonempty R := ⟨0⟩

example {R : Type u} [CommRing R] [IsDedekindDomain R] : Nontrivial R := inferInstance

example : Subsingleton (ZMod 1) := inferInstance

example (I : Ideal (ZMod 1)) : I.IsPrincipal :=
  IsPrincipalIdealRing.principal I

example : Function.Injective (id : Ideal ℤ → Ideal ℤ) :=
  Function.injective_id

example : ¬ Function.Injective (Function.const (Ideal ℤ) (⊥ : Ideal ℤ)) := by
  intro injective
  exact bot_ne_top (injective rfl)

/- Assumption and primality audit:
   * `IsDedekindDomain R` supplies `IsDomain R` and is consumed only by Mathlib's exact DVR
     theorem. The DVR instance supplies the PID instance used by both principality theorems.
   * The source's `I ≠ 0` premise was unused: `FractionalIdeal.isPrincipal` covers zero too, so it
     was deleted. No field, chosen fraction-field, maximality, or height hypothesis was added.
   * A `PrimeSpectrum` value supplies primality to form `Localization.AtPrime`. Nonzeroness is used
     exactly at the DVR step; `zero_prime_is_not_a_dvr` is its named counterexample. Mathlib derives
     maximality of a nonzero prime internally in the Dedekind-domain theorem.
   * `[Nontrivial (ClassGroup R)]` is consumed by `exists_ne`; surjectivity of `ClassGroup.mk0`
     produces the nonprincipal ideal. This condition is independent of the observer primes. The
     concrete norm-two witness is known to be prime in an adjacent module, but its primality is not
     used here: the imported gap supplies local truth and global nonprincipality separately.
   * The PID hypothesis is used by `card_classGroup_eq_one` and `principal`; the named integer
     theorem shows that removing a nontrivial global class makes the mixed witness impossible. -/

end D5.S3.Factorization.IdealClassGroups.LocalPrincipalityBlindness
