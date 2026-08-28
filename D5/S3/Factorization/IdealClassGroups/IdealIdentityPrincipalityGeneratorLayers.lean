/- GID: D5/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers
   generality: I
   mirror-B: D5/B/S3/Factorization/IdealClassGroups/IdealIdentityPrincipalityGeneratorLayers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ideal, principal, and unit layers separate, including all audited degeneracies. -/
/- Library-search audit trail (2026-08-25):
   * The requested Lean LSP search commands are unavailable in this host session;
     `smart_search.sh` and repository `rg` were used as the local fallbacks.
   * D5 already proves ideal recovery in `prime_valuation_observers_faithful`,
     principality detection in `principal_ideal_criterion`, and the identified
     nonprincipal example in `norm_two_ideal_local_global_gap`; all are imported.
   * Pinned Mathlib's `Ideal.span_singleton_eq_span_singleton` identifies equal
     singleton spans with `Associated`, whose definition supplies the unit coordinate.
     `Ideal.span_singleton_mul_right_unit` proves that the coordinate preserves the ideal.
   * No separate packaged theorem for unique recovery of the unit coordinate was found.
     The proof below only cancels the nonzero base after applying the two exact APIs above. -/

import D5.S3.Factorization.Embeddings.FractionalIdealPrimeValuationFaithfulness
import D5.S3.Factorization.IdealClassGroups.PrincipalIdealCriterion
import D5.S3.Factorization.QuadraticIdeals.NormTwoIdealLocalGlobalGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped nonZeroDivisors

namespace D5.S3.Factorization.IdealClassGroups.IdealIdentityPrincipalityGeneratorLayers

open D5.S3.Factorization.Embeddings.FractionalIdealPrimeValuationFaithfulness
open D5.S3.Factorization.IdealClassGroups.PrincipalIdealCriterion
open D5.S3.Factorization.QuadraticIdeals.NormTwoIdeal
open D5.S3.Factorization.QuadraticIdeals.NormTwoIdealLocalGlobalGap

universe u v

/-- The first layer is the imported faithfulness of all prime-ideal valuations. -/
theorem ideal_valuation_layer_recovers_fractional_ideal
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsDedekindDomain R]
    (I J : {L : FractionalIdeal R⁰ K // L ≠ 0})
    (sameValuation : ∀ prime : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K prime I.1 = FractionalIdeal.count K prime J.1) :
    I = J := by
  exact prime_valuation_observers_faithful I J sameValuation

#print axioms ideal_valuation_layer_recovers_fractional_ideal

/-- The second layer is the imported criterion that the ideal class detects principality. -/
theorem class_group_layer_detects_principality
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {I : (FractionalIdeal R⁰ K)ˣ} :
    (I : Submodule R K).IsPrincipal ↔ ClassGroup.mk K I = 1 := by
  exact principal_ideal_criterion

#print axioms class_group_layer_detects_principality

/-- Identifying an ideal does not imply that the identified ideal is principal. -/
theorem identified_ideal_need_not_be_principal :
    ∃ I : Ideal QuadraticOrder,
      I = normTwoIdeal ∧
      (∀ prime : {p : PrimeSpectrum QuadraticOrder // p.asIdeal ≠ ⊥},
        (I.map
          (algebraMap QuadraticOrder
            (Localization.AtPrime prime.1.asIdeal))).IsPrincipal) ∧
      ¬ I.IsPrincipal := by
  refine ⟨normTwoIdeal, rfl, norm_two_ideal_local_global_gap.1, ?_⟩
  exact norm_two_ideal_local_global_gap.2.1

#print axioms identified_ideal_need_not_be_principal

/-- A nontrivial class group is necessary for the preceding strictness witness. -/
theorem nontrivial_class_group_is_necessary :
    ¬ ∃ I : Ideal ℤ, ¬ I.IsPrincipal := by
  rintro ⟨I, not_principal⟩
  exact not_principal (IsPrincipalIdealRing.principal I)

#print axioms nontrivial_class_group_is_necessary

/-- A principal ideal can have two different generators. -/
theorem principality_does_not_determine_generator :
    ∃ x y : ℤ, x ≠ y ∧ Ideal.span {x} = Ideal.span {y} := by
  refine ⟨1, -1, by norm_num, ?_⟩
  apply Ideal.span_singleton_eq_span_singleton.mpr
  exact ⟨(-1 : ℤˣ), by norm_num⟩

#print axioms principality_does_not_determine_generator

/-- Without a nontrivial unit, the unit-coordinate strictness witness cannot exist. -/
theorem nontrivial_unit_is_necessary :
    ¬ ∃ coordinate : (ZMod 2)ˣ, coordinate ≠ 1 := by
  rintro ⟨coordinate, coordinate_ne_one⟩
  exact coordinate_ne_one (Subsingleton.elim coordinate 1)

#print axioms nontrivial_unit_is_necessary

/-- Multiplying a generator by a unit coordinate preserves its principal ideal. -/
theorem unit_coordinate_preserves_principal_ideal
    {R : Type u} [CommSemiring R] (base : R) (coordinate : Rˣ) :
    Ideal.span {base * (coordinate : R)} = Ideal.span {base} := by
  exact Ideal.span_singleton_mul_right_unit coordinate.isUnit base

#print axioms unit_coordinate_preserves_principal_ideal

/-- A nonzero base generator and its ideal uniquely recover every generator's unit coordinate. -/
theorem ideal_and_unit_coordinate_recover_generator
    {R : Type u} [CommSemiring R] [IsDomain R] {base target : R}
    (base_ne_zero : base ≠ 0)
    (sameIdeal : Ideal.span {target} = Ideal.span {base}) :
    ∃! coordinate : Rˣ, base * (coordinate : R) = target := by
  have associated : Associated base target :=
    (Ideal.span_singleton_eq_span_singleton.mp sameIdeal).symm
  obtain ⟨coordinate, coordinate_spec⟩ := associated
  refine ⟨coordinate, coordinate_spec, ?_⟩
  intro other other_spec
  apply Units.ext
  exact mul_left_cancel₀ base_ne_zero (other_spec.trans coordinate_spec.symm)

#print axioms ideal_and_unit_coordinate_recover_generator

/-- The nonzero-generator hypothesis is necessary even over the integers. -/
theorem nonzero_generator_is_necessary :
    ¬ ∃! coordinate : ℤˣ, (0 : ℤ) * (coordinate : ℤ) = 0 := by
  rintro ⟨coordinate, _, unique⟩
  have one_eq : (1 : ℤˣ) = coordinate := unique 1 (by norm_num)
  have neg_one_eq : (-1 : ℤˣ) = coordinate := unique (-1) (by norm_num)
  have units_eq : (1 : ℤˣ) = -1 := one_eq.trans neg_one_eq.symm
  have values_eq := congrArg (fun unit : ℤˣ ↦ (unit : ℤ)) units_eq
  norm_num at values_eq

#print axioms nonzero_generator_is_necessary

/-- Excluding zero divisors is necessary even when the chosen generator is nonzero. -/
theorem no_zero_divisors_is_necessary :
    ∃ base target : ZMod 8,
      base ≠ 0 ∧
      Ideal.span {target} = Ideal.span {base} ∧
      ¬ ∃! coordinate : (ZMod 8)ˣ, base * (coordinate : ZMod 8) = target := by
  refine ⟨4, 4, by decide, rfl, ?_⟩
  rintro ⟨coordinate, _, unique⟩
  have one_eq : (1 : (ZMod 8)ˣ) = coordinate := unique 1 (by norm_num)
  have neg_one_eq : (-1 : (ZMod 8)ˣ) = coordinate := unique (-1) (by decide)
  have units_eq : (1 : (ZMod 8)ˣ) = -1 := one_eq.trans neg_one_eq.symm
  have values_eq := congrArg (fun unit : (ZMod 8)ˣ ↦ (unit : ZMod 8)) units_eq
  exact (by decide : (1 : ZMod 8) ≠ -1) values_eq

#print axioms no_zero_divisors_is_necessary

/-- A carrier with a zero element cannot be empty. -/
theorem zero_carrier_is_not_empty {R : Type u} [Zero R] : Nonempty R := by
  exact ⟨0⟩

#print axioms zero_carrier_is_not_empty

end D5.S3.Factorization.IdealClassGroups.IdealIdentityPrincipalityGeneratorLayers
