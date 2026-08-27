/- GID: D5/S3/ConceptDynamics/NormativeStructure/TranspositionOrbitFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/TranspositionOrbitFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Swap invariance is full role invariance and canonical orbit factorization. -/

import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-28):
   * D5 searches for role-pair permutation actions, transposition generation,
     and orbit factorization found no exact theorem. `UniversalValueRoleInvariance`
     proves a broader schema-naturality result but has neither the transposition
     premise nor the orbit-quotient factorization clause.
   * Pinned Mathlib's exact finite-generation hit is
     `Equiv.Perm.swap_induction_on`; it is applied directly below.
   * Pinned Mathlib also supplies the canonical `MulAction.orbitRel`,
     `Quotient.lift`, and `Quotient.sound`. No theorem packages the source action
     on the carrier `X × U × I × I`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.TranspositionOrbitFactorization

universe u v w

/-- Relabel the actor and recipient coordinates while retaining the state and
action coordinates. -/
def relabelRoles {X : Type u} {U : Type v} {I : Type w}
    (sigma : Equiv.Perm I) : X × U × I × I -> X × U × I × I :=
  fun input => (input.1, input.2.1, sigma input.2.2.1, sigma input.2.2.2)

/-- Simultaneous relabeling is the canonical permutation action on the two role
coordinates of an action record. -/
@[implicit_reducible]
def roleAction (X : Type u) (U : Type v) (I : Type w) :
    MulAction (Equiv.Perm I) (X × U × I × I) where
  smul := relabelRoles
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] roleAction

/-- For finitely many roles, invariance under every transposition is equivalent
to invariance under every role permutation, and full invariance is equivalent
to factorization through the canonical orbit quotient of action records. -/
theorem transposition_orbit_factorization
    {X : Type u} {U : Type v} {I : Type w} [Finite I]
    (admissible : X × U × I × I -> Prop) :
    ((forall actor recipient input,
      admissible
          (relabelRoles (@Equiv.swap I (Classical.decEq I) actor recipient) input) ↔
        admissible input) ↔
      forall (sigma : Equiv.Perm I) input,
        admissible (relabelRoles sigma input) ↔ admissible input) ∧
    ((forall (sigma : Equiv.Perm I) input,
      admissible (relabelRoles sigma input) ↔ admissible input) ↔
      exists descended :
          Quotient (MulAction.orbitRel (Equiv.Perm I)
            (X × U × I × I)) -> Prop,
        admissible = descended ∘
          Quotient.mk
            (MulAction.orbitRel (Equiv.Perm I) (X × U × I × I))) := by
  letI := Classical.decEq I
  constructor
  · constructor
    · intro swapInvariant sigma
      induction sigma using Equiv.Perm.swap_induction_on with
      | one =>
          intro input
          simp [relabelRoles]
      | swap_mul sigma actor recipient _ ih =>
          intro input
          calc
            admissible
                (relabelRoles (Equiv.swap actor recipient * sigma) input) ↔
              admissible (relabelRoles sigma input) := by
                simpa [relabelRoles] using
                  swapInvariant actor recipient (relabelRoles sigma input)
            _ ↔ admissible input := ih input
    · intro permutationInvariant actor recipient input
      exact permutationInvariant (Equiv.swap actor recipient) input
  · constructor
    · intro permutationInvariant
      let descended :
          Quotient (MulAction.orbitRel (Equiv.Perm I)
            (X × U × I × I)) -> Prop :=
        Quotient.lift admissible (by
          intro first second sameOrbit
          rcases MulAction.mem_orbit_iff.mp sameOrbit with ⟨sigma, rfl⟩
          exact propext (permutationInvariant sigma second))
      refine ⟨descended, ?_⟩
      funext input
      rfl
    · rintro ⟨descended, factorization⟩ sigma input
      have sameOrbit :
          Quotient.mk
              (MulAction.orbitRel (Equiv.Perm I) (X × U × I × I))
              (relabelRoles sigma input) =
            Quotient.mk
              (MulAction.orbitRel (Equiv.Perm I) (X × U × I × I))
              input := by
        apply Quotient.sound
        exact MulAction.mem_orbit input sigma
      rw [congrFun factorization (relabelRoles sigma input),
        congrFun factorization input]
      change descended ⟦relabelRoles sigma input⟧ ↔ descended ⟦input⟧
      exact iff_of_eq (congrArg descended sameOrbit)

/-- The public finite-role hypothesis and predicate carrier are inhabited. -/
example :
    let admissible : Unit × Unit × Bool × Bool -> Prop := fun input => input.2.2.1 = input.2.2.2
    forall (sigma : Equiv.Perm Bool) input,
      admissible (relabelRoles sigma input) ↔ admissible input := by
  dsimp
  intro sigma input
  exact sigma.injective.eq_iff

#print axioms relabelRoles
#print axioms roleAction
#print axioms transposition_orbit_factorization

end D5.S3.ConceptDynamics.NormativeStructure.TranspositionOrbitFactorization
