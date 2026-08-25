/- GID: D5/S3/Factorization/QuadraticIdeals/NormTwoIdealLocalGlobalGap
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/NormTwoIdealLocalGlobalGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The norm-two ideal is principal at every nonzero prime localization but not globally. -/

import D5.S3.Factorization.QuadraticIdeals.NormTwoIdeal
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Repository searches for the local/global principal-ideal conjunction, a
     positive Hasse defect, and the minus-five quadratic ideal found no exact
     D5 theorem. The frozen `NormTwoIdeal` module is the unique same-carrier
     construction and is imported rather than repeated.
   * Pinned Mathlib has the general Dedekind-localization PID theorem
     `IsDedekindDomain.isPrincipalIdealRing_localization_over_prime`, but no
     Dedekind instance or corresponding local-principality theorem for
     `Zsqrtd (-5)`.
   * `Ideal.span_pair_eq_span_right_iff_dvd`,
     `IsLocalization.map_units`, and
     `IsLocalization.mk'_mul_cancel_left` are the exact library steps used for
     the direct local computation. `Zsqrtd.norm_mul` and
     `Zsqrtd.norm_eq_one_iff` supply the global norm obstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.NormTwoIdealLocalGlobalGap

open D5.S3.Factorization.QuadraticIdeals.NormTwoIdeal

universe u v

/-- The positive local-to-global defect from Section 44, constructed from a
global predicate and its family of local predicates. -/
def positiveHasseDefect {X : Type u} {Index : Type v}
    (global : X → Prop) (localPredicate : Index → X → Prop) :=
  {object : X // (∀ index, localPredicate index object) ∧ ¬ global object}

private theorem norm_two_ideal_locally_principal
    (prime : PrimeSpectrum QuadraticOrder) :
    (normTwoIdeal.map
      (algebraMap QuadraticOrder (Localization.AtPrime prime.asIdeal))).IsPrincipal := by
  let localized := Localization.AtPrime prime.asIdeal
  let mapToLocal : QuadraticOrder →+* localized := algebraMap _ _
  by_cases two_mem : (2 : QuadraticOrder) ∈ prime.asIdeal
  · have three_not_mem : (3 : QuadraticOrder) ∉ prime.asIdeal := by
      intro three_mem
      have one_mem : (1 : QuadraticOrder) ∈ prime.asIdeal := by
        have one_eq : (1 : QuadraticOrder) = 3 - 2 := by norm_num
        rw [one_eq]
        exact prime.asIdeal.sub_mem three_mem two_mem
      exact prime.isPrime.ne_top ((Ideal.eq_top_iff_one prime.asIdeal).mpr one_mem)
    let threeInComplement : prime.asIdeal.primeCompl := ⟨3, three_not_mem⟩
    let coefficient : localized :=
      IsLocalization.mk' localized (1 - Zsqrtd.sqrtd) threeInComplement
    have product_identity :
        ((1 + Zsqrtd.sqrtd) * (1 - Zsqrtd.sqrtd) : QuadraticOrder) =
          (threeInComplement : QuadraticOrder) * 2 := by
      ext <;> norm_num [threeInComplement]
    have local_divisibility :
        mapToLocal (1 + Zsqrtd.sqrtd) ∣ mapToLocal 2 := by
      refine ⟨coefficient, ?_⟩
      symm
      calc
        mapToLocal (1 + Zsqrtd.sqrtd) * coefficient =
            IsLocalization.mk' localized
              ((1 + Zsqrtd.sqrtd) * (1 - Zsqrtd.sqrtd)) threeInComplement := by
                exact IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _
        _ = IsLocalization.mk' localized
              ((threeInComplement : QuadraticOrder) * 2) threeInComplement := by
                rw [product_identity]
        _ = mapToLocal 2 := by
              exact IsLocalization.mk'_mul_cancel_left 2 threeInComplement
    refine ⟨mapToLocal (1 + Zsqrtd.sqrtd), ?_⟩
    change normTwoIdeal.map mapToLocal =
      Ideal.span {mapToLocal (1 + Zsqrtd.sqrtd)}
    rw [normTwoIdeal, Ideal.map_span]
    have image_pair :
        mapToLocal '' ({(2 : QuadraticOrder), 1 + Zsqrtd.sqrtd} : Set QuadraticOrder) =
          {mapToLocal 2, mapToLocal (1 + Zsqrtd.sqrtd)} := by
      ext value
      simp [eq_comm]
    rw [image_pair]
    exact Ideal.span_pair_eq_span_right_iff_dvd.mpr local_divisibility
  · have mapped_two_unit : IsUnit (mapToLocal 2) :=
      IsLocalization.map_units localized
        (⟨2, two_mem⟩ : prime.asIdeal.primeCompl)
    have mapped_two_mem : mapToLocal 2 ∈ normTwoIdeal.map mapToLocal := by
      apply Ideal.mem_map_of_mem
      rw [normTwoIdeal]
      exact Ideal.subset_span (by simp)
    have mapped_ideal_top : normTwoIdeal.map mapToLocal = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ mapped_two_mem mapped_two_unit
    refine ⟨1, ?_⟩
    change normTwoIdeal.map mapToLocal = Submodule.span localized {1}
    rw [mapped_ideal_top]
    apply le_antisymm
    · intro value _
      exact Submodule.mem_span_singleton.mpr ⟨value, by simp⟩
    · exact le_top

private theorem norm_two_ideal_not_principal : ¬ normTwoIdeal.IsPrincipal := by
  intro principal
  obtain ⟨generator, generator_spec⟩ := principal.principal
  have ideal_proper : normTwoIdeal ≠ ⊤ := by
    have ideal_le_kernel : normTwoIdeal ≤ RingHom.ker residueHom := by
      rw [normTwoIdeal, Ideal.span_le]
      intro value value_mem
      rcases value_mem with (rfl | value_mem)
      · norm_num [RingHom.mem_ker, residueHom, Zsqrtd.lift_apply_apply]
        exact CharP.cast_eq_zero (ZMod 2) 2
      · have : value = 1 + Zsqrtd.sqrtd := by simpa using value_mem
        subst value
        norm_num [RingHom.mem_ker, residueHom, Zsqrtd.lift_apply_apply]
        exact CharP.cast_eq_zero (ZMod 2) 2
    intro ideal_top
    have one_mem : (1 : QuadraticOrder) ∈ normTwoIdeal := by
      rw [ideal_top]
      trivial
    have one_in_kernel : residueHom (1 : QuadraticOrder) = 0 :=
      RingHom.mem_ker.mp (ideal_le_kernel one_mem)
    rw [map_one] at one_in_kernel
    exact (one_ne_zero : (1 : ZMod 2) ≠ 0) one_in_kernel
  have generator_not_unit : ¬ IsUnit generator := by
    intro generator_unit
    apply ideal_proper
    calc
      normTwoIdeal = Submodule.span QuadraticOrder {generator} := generator_spec
      _ = Ideal.span {generator} := rfl
      _ = ⊤ := Ideal.span_singleton_eq_top.mpr generator_unit
  have two_mem : (2 : QuadraticOrder) ∈ normTwoIdeal := by
    rw [normTwoIdeal]
    exact Ideal.subset_span (by simp)
  have root_mem : (1 + Zsqrtd.sqrtd : QuadraticOrder) ∈ normTwoIdeal := by
    rw [normTwoIdeal]
    exact Ideal.subset_span (by simp)
  rw [generator_spec, Ideal.mem_span_singleton] at two_mem root_mem
  obtain ⟨twoFactor, two_factor_spec⟩ := two_mem
  obtain ⟨rootFactor, root_factor_spec⟩ := root_mem
  have generator_norm_dvd_four : Zsqrtd.norm generator ∣ (4 : ℤ) := by
    refine ⟨Zsqrtd.norm twoFactor, ?_⟩
    calc
      (4 : ℤ) = Zsqrtd.norm (2 : QuadraticOrder) := by
        norm_num [Zsqrtd.norm_def]
      _ = Zsqrtd.norm (generator * twoFactor) :=
        congrArg Zsqrtd.norm two_factor_spec
      _ = Zsqrtd.norm generator * Zsqrtd.norm twoFactor :=
        Zsqrtd.norm_mul _ _
  have root_norm :
      Zsqrtd.norm (1 + Zsqrtd.sqrtd : QuadraticOrder) = 6 := by
    norm_num [Zsqrtd.norm_def]
  have generator_norm_dvd_six : Zsqrtd.norm generator ∣ (6 : ℤ) := by
    refine ⟨Zsqrtd.norm rootFactor, ?_⟩
    calc
      (6 : ℤ) = Zsqrtd.norm (1 + Zsqrtd.sqrtd : QuadraticOrder) := root_norm.symm
      _ = Zsqrtd.norm (generator * rootFactor) :=
        congrArg Zsqrtd.norm root_factor_spec
      _ = Zsqrtd.norm generator * Zsqrtd.norm rootFactor :=
        Zsqrtd.norm_mul _ _
  have generator_norm_dvd_two : Zsqrtd.norm generator ∣ (2 : ℤ) := by
    simpa using dvd_sub generator_norm_dvd_six generator_norm_dvd_four
  have norm_abs_dvd_two : (Zsqrtd.norm generator).natAbs ∣ 2 :=
    Int.dvd_natCast.mp generator_norm_dvd_two
  have norm_abs_ne_zero : (Zsqrtd.norm generator).natAbs ≠ 0 := by
    intro norm_zero
    have : 0 ∣ (2 : ℕ) := norm_zero ▸ norm_abs_dvd_two
    norm_num at this
  have norm_abs_ne_one : (Zsqrtd.norm generator).natAbs ≠ 1 := by
    intro norm_one
    exact generator_not_unit (Zsqrtd.norm_eq_one_iff.mp norm_one)
  have norm_abs_le_two : (Zsqrtd.norm generator).natAbs ≤ 2 :=
    Nat.le_of_dvd (by norm_num) norm_abs_dvd_two
  have norm_abs_eq_two : (Zsqrtd.norm generator).natAbs = 2 := by
    omega
  have generator_norm_nonnegative : 0 ≤ Zsqrtd.norm generator :=
    Zsqrtd.norm_nonneg (by norm_num) generator
  have generator_norm_eq_two : Zsqrtd.norm generator = 2 := by
    have cast_norm_abs : ((Zsqrtd.norm generator).natAbs : ℤ) = 2 := by
      exact_mod_cast norm_abs_eq_two
    simpa [Int.natCast_natAbs, abs_of_nonneg generator_norm_nonnegative] using
      cast_norm_abs
  have coordinate_equation :
      generator.re * generator.re + 5 * generator.im * generator.im = 2 := by
    simpa [Zsqrtd.norm_def] using generator_norm_eq_two
  have imaginary_zero : generator.im = 0 := by
    by_contra imaginary_nonzero
    have imaginary_cases : generator.im ≤ -1 ∨ 1 ≤ generator.im := by omega
    rcases imaginary_cases with imaginary_negative | imaginary_positive
    · have imaginary_square : 1 ≤ generator.im * generator.im := by nlinarith
      nlinarith [sq_nonneg generator.re]
    · have imaginary_square : 1 ≤ generator.im * generator.im := by nlinarith
      nlinarith [sq_nonneg generator.re]
  rw [imaginary_zero] at coordinate_equation
  have real_lower : -1 ≤ generator.re := by nlinarith
  have real_upper : generator.re ≤ 1 := by nlinarith
  have real_cases : generator.re = -1 ∨ generator.re = 0 ∨ generator.re = 1 := by
    omega
  rcases real_cases with real_negative | real_zero | real_positive
  · rw [real_negative] at coordinate_equation
    norm_num at coordinate_equation
  · rw [real_zero] at coordinate_equation
    norm_num at coordinate_equation
  · rw [real_positive] at coordinate_equation
    norm_num at coordinate_equation

/-- The standard norm-two ideal is principal at every nonzero prime
localization, is not principal in the quadratic order, and is the named object
of an explicit positive local-to-global defect witness. -/
theorem norm_two_ideal_local_global_gap :
    (∀ prime : {p : PrimeSpectrum QuadraticOrder // p.asIdeal ≠ ⊥},
      (normTwoIdeal.map
        (algebraMap QuadraticOrder
          (Localization.AtPrime prime.1.asIdeal))).IsPrincipal) ∧
    ¬ normTwoIdeal.IsPrincipal ∧
    ∃ witness : positiveHasseDefect
        (fun ideal : Ideal QuadraticOrder => ideal.IsPrincipal)
        (fun prime : {p : PrimeSpectrum QuadraticOrder // p.asIdeal ≠ ⊥} =>
          fun ideal =>
            (ideal.map
              (algebraMap QuadraticOrder
                (Localization.AtPrime prime.1.asIdeal))).IsPrincipal),
      witness.1 = normTwoIdeal := by
  have local_principality :
      ∀ prime : {p : PrimeSpectrum QuadraticOrder // p.asIdeal ≠ ⊥},
        (normTwoIdeal.map
          (algebraMap QuadraticOrder
            (Localization.AtPrime prime.1.asIdeal))).IsPrincipal :=
    fun prime => norm_two_ideal_locally_principal prime.1
  have global_nonprincipality : ¬ normTwoIdeal.IsPrincipal :=
    norm_two_ideal_not_principal
  refine ⟨local_principality, global_nonprincipality, ?_⟩
  exact ⟨⟨normTwoIdeal, local_principality, global_nonprincipality⟩, rfl⟩

/-- The positive defect type is inhabited here by the source ideal itself, not
by an unrelated ideal. -/
example :
    ∃ witness : positiveHasseDefect
        (fun ideal : Ideal QuadraticOrder => ideal.IsPrincipal)
        (fun prime : {p : PrimeSpectrum QuadraticOrder // p.asIdeal ≠ ⊥} =>
          fun ideal =>
            (ideal.map
              (algebraMap QuadraticOrder
                (Localization.AtPrime prime.1.asIdeal))).IsPrincipal),
      witness.1 = normTwoIdeal :=
  norm_two_ideal_local_global_gap.2.2

#print axioms norm_two_ideal_local_global_gap

end D5.S3.Factorization.QuadraticIdeals.NormTwoIdealLocalGlobalGap
