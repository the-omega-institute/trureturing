/- GID: D5/S3/ConceptDynamics/Fibers/IdealRecoveryNotPrincipality
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Fibers/IdealRecoveryNotPrincipality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A named prime ideal is nonprincipal; PID, zero, and unit cases stay principal. -/
/- Library-search audit trail (2026-08-25):
   * Current-tree search found the exact concrete source theorem
     `identified_ideal_need_not_be_principal`, together with its named
     `Zsqrtd (-5)` ideal. It is imported and applied; its norm obstruction is
     not reconstructed here.
   * Pinned Mathlib supplies
     `Ideal.Quotient.maximal_ideal_iff_isField_quotient`,
     `Ideal.IsMaximal.isPrime`, `IsPrincipalIdealRing.principal`, and the
     `bot_isPrincipal` and `top_isPrincipal` instances. All are used directly.
   * FPOD 191.1's `two_generators_unit_gauge` starts after principality is
     known and compares two generators up to a unit. The theorem below instead
     exhibits an ideal with no global single generator. None of 191.1's
     kernel, image, or gauge theorems is recreated or imported.
   * Downgrade choice: none. The repository already has the concrete
     minus-five quadratic-order witness, so fallback paths A, B, and C are
     unnecessary; no new class-group witness or abstract existence premise is
     substituted for it. -/

import D5.S3.Factorization.IdealClassGroups.IdealIdentityPrincipalityGeneratorLayers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Fibers.IdealRecoveryNotPrincipality

open D5.S3.Factorization.IdealClassGroups.IdealIdentityPrincipalityGeneratorLayers
open D5.S3.Factorization.QuadraticIdeals.NormTwoIdeal

universe u

/-- The named two-generator data uniquely identifies the norm-two ideal, yet
that ideal is prime and has no global single generator. -/
theorem uniquely_recovered_prime_ideal_need_not_be_principal :
    (∃! I : Ideal QuadraticOrder, I = normTwoIdeal) ∧
      normTwoIdeal.IsPrime ∧ ¬ normTwoIdeal.IsPrincipal := by
  have uniquely_recovered : ∃! I : Ideal QuadraticOrder, I = normTwoIdeal :=
    ⟨normTwoIdeal, rfl, fun _ hI => hI⟩
  have not_principal : ¬ normTwoIdeal.IsPrincipal := by
    obtain ⟨I, hI, _, hI_not_principal⟩ := identified_ideal_need_not_be_principal
    simpa [hI] using hI_not_principal
  have quotient_is_field : IsField (QuadraticOrder ⧸ normTwoIdeal) :=
    quotientEquivZModTwo.toMulEquiv.isField (Field.toIsField (ZMod 2))
  have maximal : normTwoIdeal.IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient normTwoIdeal).2
      quotient_is_field
  exact ⟨uniquely_recovered, maximal.isPrime, not_principal⟩

#print axioms uniquely_recovered_prime_ideal_need_not_be_principal

/-- Every ideal is principal when the ambient semiring carries Mathlib's
principal-ideal-ring structure. -/
theorem every_ideal_is_principal_in_principal_ideal_ring
    {R : Type u} [Semiring R] [IsPrincipalIdealRing R] (I : Ideal R) :
    I.IsPrincipal := by
  exact IsPrincipalIdealRing.principal I

#print axioms every_ideal_is_principal_in_principal_ideal_ring

/-- The principal-ideal-ring hypothesis is essential: the concrete quadratic
order above does not carry it. -/
theorem principal_ideal_ring_hypothesis_is_necessary :
    ¬ IsPrincipalIdealRing QuadraticOrder := by
  intro principal_ring
  letI : IsPrincipalIdealRing QuadraticOrder := principal_ring
  exact uniquely_recovered_prime_ideal_need_not_be_principal.2.2
    (every_ideal_is_principal_in_principal_ideal_ring normTwoIdeal)

#print axioms principal_ideal_ring_hypothesis_is_necessary

/-- The zero and unit ideals are always principal, independently of any PID
hypothesis. -/
theorem zero_and_unit_ideals_are_principal
    {R : Type u} [Semiring R] :
    (⊥ : Ideal R).IsPrincipal ∧ (⊤ : Ideal R).IsPrincipal := by
  exact ⟨bot_isPrincipal, top_isPrincipal⟩

#print axioms zero_and_unit_ideals_are_principal

example : normTwoIdeal ≠ ⊥ ∧ normTwoIdeal ≠ ⊤ := by
  have not_principal :=
    uniquely_recovered_prime_ideal_need_not_be_principal.2.2
  constructor
  · intro bottom
    rw [bottom] at not_principal
    exact not_principal bot_isPrincipal
  · intro top
    rw [top] at not_principal
    exact not_principal top_isPrincipal

/- Degenerate audit: a semiring carrier cannot be empty because it contains
zero. The singleton semiring `ZMod 1` has only principal ideals, so it cannot
host the strictness witness. The `n = 0` ideal input is the first component of
`zero_and_unit_ideals_are_principal`; it remains principal. -/
example {R : Type u} [Semiring R] : Nonempty R := ⟨0⟩

example : Subsingleton (ZMod 1) := inferInstance

example (I : Ideal (ZMod 1)) : I.IsPrincipal := by
  exact every_ideal_is_principal_in_principal_ideal_ring I

/- There is no map parameter in the public statements. If recovery were
replaced by an arbitrary map, the identity map is injective while the constant
zero map is not; neither specialization changes the concrete theorem above. -/
example : Function.Injective (id : Ideal QuadraticOrder → Ideal QuadraticOrder) :=
  Function.injective_id

example :
    ¬ Function.Injective
      (Function.const (Ideal QuadraticOrder) (⊥ : Ideal QuadraticOrder)) := by
  intro injective
  have bottom_eq_top : (⊥ : Ideal QuadraticOrder) = ⊤ := injective rfl
  exact bot_ne_top bottom_eq_top

/- Primality audit: primality is not used to identify the ideal or to import
its nonprincipality. It is used only in the stronger prime-ideal refinement:
the prime modulus `2` makes `ZMod 2` a field, hence the quotient ideal maximal
and therefore prime.

Assumption audit: the core and necessity theorems are concrete and have no
hypotheses. In the PID contrast, `[Semiring R]` is definitional for `Ideal R`
and `[IsPrincipalIdealRing R]` is used by `principal`; the named necessity
result gives its concrete counterexample. In the zero/unit theorem,
`[Semiring R]` is again definitional. There are no unused field, domain,
Dedekind, nonzero, or prime hypotheses. -/

end D5.S3.ConceptDynamics.Fibers.IdealRecoveryNotPrincipality
