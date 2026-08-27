/- GID: D5/S3/ConceptDynamics/NormativeStructure/RoleSwapOrbitFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/RoleSwapOrbitFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pairwise role-swap invariance is full invariance and orbit factorization. -/

import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.GroupAction.Defs

/- Library-search audit trail (2026-08-28):
   * Statement-shape searches across D5 found no theorem equating pairwise role-swap
     invariance, invariance under every role permutation, and orbit factorization.
   * The adjacent frozen `UniversalValueRoleInvariance` module transports a different
     structural schema across role equivalences; it does not state swap generation or
     factorization of an admission predicate.
   * Pinned Mathlib supplies `Equiv.Perm.closure_isSwap`,
     `MulAction.orbitRel.Quotient`, and `Function.FactorsThrough`; all three canonical
     primitives are used directly below. Body-shape searches found no D5 copy of the
     orbit projection defined here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.RoleSwapOrbitFactorization

universe u v w

/-- An admission predicate is invariant under a simultaneous relabeling of its
actor and recipient roles. -/
def RoleInvariant {X : Type u} {U : Type v} {I : Type w}
    (admission : X -> U -> I -> I -> Prop) (sigma : Equiv.Perm I) : Prop :=
  forall state action actor recipient,
    admission state action (sigma actor) (sigma recipient) ↔
      admission state action actor recipient

/-- The transposition of two roles, with the finite carrier's decidable equality
kept out of the public theorem hypotheses. -/
noncomputable def roleSwap {I : Type w} (actor recipient : I) : Equiv.Perm I :=
  @Equiv.swap I (Classical.decEq I) actor recipient

/-- A role permutation fixes state and action while acting diagonally on the
ordered actor-recipient pair. -/
instance roleTupleMulAction (X : Type u) (U : Type v) (I : Type w) :
    MulAction (Equiv.Perm I) (X × U × (I × I)) where
  smul sigma input :=
    (input.1, input.2.1, sigma input.2.2.1, sigma input.2.2.2)
  one_smul input := by
    rfl
  mul_smul sigma tau input := by
    rfl

/-- The canonical quotient of state-action-role tuples by simultaneous role
permutation. -/
abbrev RoleOrbit (X : Type u) (U : Type v) (I : Type w) :=
  MulAction.orbitRel.Quotient (Equiv.Perm I) (X × U × (I × I))

/-- Forget role names while retaining the state and action coordinates. -/
def roleOrbitProjection {X : Type u} {U : Type v} {I : Type w} :
    X × U × (I × I) -> RoleOrbit X U I :=
  fun input => Quotient.mk'' input

/-- For a finite role carrier, invariance under every pairwise swap, invariance
under every role permutation, and factorization through the role-orbit quotient
are equivalent. -/
theorem role_swap_full_invariance_orbit_factorization
    {X : Type u} {U : Type v} {I : Type w} [Finite I]
    (admission : X -> U -> I -> I -> Prop) :
    ((forall actor recipient,
        RoleInvariant admission (roleSwap actor recipient)) ↔
      (forall sigma : Equiv.Perm I, RoleInvariant admission sigma)) ∧
    ((forall sigma : Equiv.Perm I, RoleInvariant admission sigma) ↔
      Function.FactorsThrough
        (fun input : X × U × (I × I) =>
          admission input.1 input.2.1 input.2.2.1 input.2.2.2)
        (roleOrbitProjection (X := X) (U := U) (I := I))) := by
  constructor
  · constructor
    · intro swapInvariant
      letI : DecidableEq I := Classical.decEq I
      let stabilizer : Subgroup (Equiv.Perm I) :=
        { carrier := {sigma | RoleInvariant admission sigma}
          one_mem' := by
            intro state action actor recipient
            simp
          mul_mem' := by
            intro sigma tau sigmaInvariant tauInvariant
            change RoleInvariant admission sigma at sigmaInvariant
            change RoleInvariant admission tau at tauInvariant
            intro state action actor recipient
            change
              admission state action (sigma (tau actor)) (sigma (tau recipient)) ↔
                admission state action actor recipient
            exact
              (sigmaInvariant state action (tau actor) (tau recipient)).trans
                (tauInvariant state action actor recipient)
          inv_mem' := by
            intro sigma sigmaInvariant
            change RoleInvariant admission sigma at sigmaInvariant
            intro state action actor recipient
            simpa using
              (sigmaInvariant state action (sigma.symm actor) (sigma.symm recipient)).symm }
      have swaps_le :
          {sigma : Equiv.Perm I | sigma.IsSwap} ⊆ stabilizer := by
        intro sigma isSwap
        rcases isSwap with ⟨actor, recipient, _, rfl⟩
        change RoleInvariant admission (Equiv.swap actor recipient)
        simpa [roleSwap] using swapInvariant actor recipient
      have closure_le :
          Subgroup.closure {sigma : Equiv.Perm I | sigma.IsSwap} ≤ stabilizer :=
        (Subgroup.closure_le stabilizer).2 swaps_le
      rw [Equiv.Perm.closure_isSwap] at closure_le
      intro sigma
      exact closure_le (Subgroup.mem_top sigma)
    · intro fullInvariant actor recipient
      exact fullInvariant (roleSwap actor recipient)
  · constructor
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

#print axioms role_swap_full_invariance_orbit_factorization

end D5.S3.ConceptDynamics.NormativeStructure.RoleSwapOrbitFactorization
