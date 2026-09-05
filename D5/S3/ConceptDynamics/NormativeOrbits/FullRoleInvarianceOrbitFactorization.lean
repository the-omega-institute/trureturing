/- GID: D5/S3/ConceptDynamics/NormativeOrbits/FullRoleInvarianceOrbitFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeOrbits/FullRoleInvarianceOrbitFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full role invariance is orbit factorization without a finite-role restriction. -/

import D5.S3.ConceptDynamics.NormativeOrbits.RoleSwapOrbitFactorization

/- Library-search audit trail (2026-09-05):
   * The frozen `RoleSwapOrbitFactorization` and
     `NormativeStructure.TranspositionOrbitFactorization` owners both place
     `[Finite I]` over their complete conjunctions.
   * Broader D5 searches for unrestricted `FactorsThrough`/role-orbit and
     `Equiv.Perm`/role-invariance statements found no exact owner.
   * The canonical `RoleInvariant`, `RoleOrbit`, and `roleOrbitProjection`
     primitives are imported from `RoleSwapOrbitFactorization`; the proof below
     uses only orbit equivalence and quotient soundness, not finite generation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeOrbits.FullRoleInvarianceOrbitFactorization

open D5.S3.ConceptDynamics.NormativeOrbits.RoleSwapOrbitFactorization

universe u v w

/-- For an arbitrary role carrier, invariance under every role permutation is
equivalent to factorization through the canonical role-orbit projection. -/
theorem full_role_invariance_iff_orbit_factorization
    {X : Type u} {U : Type v} {I : Type w}
    (admission : X -> U -> I -> I -> Prop) :
    (forall sigma : Equiv.Perm I, RoleInvariant admission sigma) ↔
      Function.FactorsThrough
        (fun input : X × U × (I × I) =>
          admission input.1 input.2.1 input.2.2.1 input.2.2.2)
        (roleOrbitProjection (X := X) (U := U) (I := I)) := by
  constructor
  · intro fullInvariant
    rintro ⟨state, action, actor, recipient⟩
      ⟨state', action', actor', recipient'⟩ projectionEq
    have sameOrbit :
        MulAction.orbitRel (Equiv.Perm I) (X × U × (I × I))
          (state, action, actor, recipient)
          (state', action', actor', recipient') :=
      Quotient.exact projectionEq
    rcases MulAction.mem_orbit_iff.mp sameOrbit with ⟨sigma, rolesEq⟩
    change
      (state', action', sigma actor', sigma recipient') =
        (state, action, actor, recipient) at rolesEq
    have stateEq : state' = state := congrArg Prod.fst rolesEq
    have actionEq : action' = action :=
      congrArg (fun output => output.2.1) rolesEq
    have actorEq : sigma actor' = actor :=
      congrArg (fun output => output.2.2.1) rolesEq
    have recipientEq : sigma recipient' = recipient :=
      congrArg (fun output => output.2.2.2) rolesEq
    subst state'
    subst action'
    subst actor
    subst recipient
    exact propext (fullInvariant sigma state action actor' recipient')
  · intro factors sigma state action actor recipient
    have sameOrbit :
        MulAction.orbitRel (Equiv.Perm I) (X × U × (I × I))
          (state, action, sigma actor, sigma recipient)
          (state, action, actor, recipient) := by
      exact ⟨sigma, rfl⟩
    have orbitEq :
        (Quotient.mk'' (state, action, sigma actor, sigma recipient) :
            RoleOrbit X U I) =
          Quotient.mk'' (state, action, actor, recipient) :=
      Quotient.sound sameOrbit
    exact Iff.of_eq (factors orbitEq)

#print axioms full_role_invariance_iff_orbit_factorization

end D5.S3.ConceptDynamics.NormativeOrbits.FullRoleInvarianceOrbitFactorization
