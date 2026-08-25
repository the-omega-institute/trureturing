/- GID: D5/S3/Factorization/IdealClassGroups/ClassGroupQuotientUniversality
   generality: I
   mirror-B: D5/B/S3/Factorization/IdealClassGroups/ClassGroupQuotientUniversality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Principal-trivial homomorphisms descend uniquely to the class group. -/

import Mathlib.RingTheory.ClassGroup.Basic

/- Library-search audit trail (2026-08-25):
   * Repository searches found no D5 class-group construction or theorem with
     this universal property.
   * Pinned Mathlib's `ClassGroup`, `ClassGroup.mk`, and
     `toPrincipalIdeal` are the exact canonical source objects.
   * `QuotientGroup.lift`, `QuotientGroup.lift_comp_mk'`, and
     `QuotientGroup.mk'_surjective` provide existence, the computation law,
     and uniqueness for the quotient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.IdealClassGroups.ClassGroupQuotientUniversality

open scoped nonZeroDivisors

open IsLocalization IsFractionRing FractionalIdeal Units

universe u v

/--
The class group has the quotient universal property on its canonical
fractional-ideal carrier: a group homomorphism that sends every principal
fractional ideal to one factors through the canonical ideal-class map, and
the factor is unique.
-/
theorem class_group_quotient_universality
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (H : Type v) [Group H]
    (f : (FractionalIdeal R⁰ (FractionRing R))ˣ →* H)
    (principal_eq_one : ∀ x : (FractionRing R)ˣ,
      f (toPrincipalIdeal R (FractionRing R) x) = 1) :
    ∃! descended : ClassGroup R →* H,
      f = descended.comp (ClassGroup.mk (FractionRing R)) := by
  let principalSubgroup := (toPrincipalIdeal R (FractionRing R)).range
  have principal_le_kernel : principalSubgroup ≤ f.ker := by
    intro ideal hideal
    obtain ⟨x, rfl⟩ := hideal
    exact MonoidHom.mem_ker.mpr (principal_eq_one x)
  let descended : ClassGroup R →* H :=
    QuotientGroup.lift principalSubgroup f principal_le_kernel
  refine ⟨descended, ?_, ?_⟩
  · apply MonoidHom.ext
    intro ideal
    change f ideal = descended (ClassGroup.mk (FractionRing R) ideal)
    rw [← ClassGroup.Quot_mk_eq_mk]
    rfl
  · intro candidate hcandidate
    apply MonoidHom.ext
    intro idealClass
    refine ClassGroup.induction (K := FractionRing R) ?_ idealClass
    intro ideal
    have candidate_agrees := DFunLike.congr_fun hcandidate ideal
    have candidate_agrees' :
        f ideal = candidate (ClassGroup.mk (FractionRing R) ideal) := by
      simpa using candidate_agrees
    change candidate (ClassGroup.mk (FractionRing R) ideal) =
      descended (ClassGroup.mk (FractionRing R) ideal)
    rw [← candidate_agrees', ← ClassGroup.Quot_mk_eq_mk]
    rfl

end D5.S3.Factorization.IdealClassGroups.ClassGroupQuotientUniversality
