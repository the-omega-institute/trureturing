/- GID: D5/S3/ConceptDynamics/Control/EffectiveProtocolActionMonoid
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/EffectiveProtocolActionMonoid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The protocol action-kernel quotient acts faithfully. -/

import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.Congruence.Basic

/- Library-search audit trail (2026-08-28):
   * Current-tree name and body-shape searches found no declaration constructing
     the quotient of protocol words by equality of their actions on every state.
     `ControlQuotientUniversalMinimality` instead quotients states by equality of
     their full control profiles, so it is not an exact hit.
   * Exact pinned-Mathlib hits `MulAction.toEndHom`, `Con.ker`, `Con.Quotient`,
     and `Con.kerLift_injective` provide the canonical action representation,
     its two-sided monoid congruence, the effective quotient carrier, and the
     faithfulness proof. They are applied directly rather than redeclared.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.EffectiveProtocolActionMonoid

/-- Equality of protocol-word actions is an equivalence stable under composition
on both sides. The quotient by this action kernel carries the canonical induced
action, and that action is faithful. -/
theorem effective_protocol_action_monoid
    {Action State : Type*} [MulAction (FreeMonoid Action) State] :
    Equivalence
        (fun first second : FreeMonoid Action =>
          forall state : State, first • state = second • state) ∧
      (forall actionHead first second : FreeMonoid Action,
        (forall state : State, first • state = second • state) ->
        forall state : State,
          (actionHead * first) • state = (actionHead * second) • state) ∧
      (forall suffix first second : FreeMonoid Action,
        (forall state : State, first • state = second • state) ->
        forall state : State,
          (first * suffix) • state = (second * suffix) • state) ∧
      @FaithfulSMul
        ((Con.ker
          (MulAction.toEndHom (M := FreeMonoid Action) (α := State))).Quotient)
        State
        (MulAction.ofEndHom
          (Con.kerLift
            (MulAction.toEndHom
              (M := FreeMonoid Action) (α := State)))).toSMul := by
  constructor
  · constructor
    · intro word state
      rfl
    · intro first second sameAction state
      exact (sameAction state).symm
    · intro first second third firstSecond secondThird state
      exact (firstSecond state).trans (secondThird state)
  constructor
  · intro actionHead first second sameAction state
    simpa only [mul_smul] using
      congrArg (fun value => actionHead • value) (sameAction state)
  constructor
  · intro suffix first second sameAction state
    simpa only [mul_smul] using sameAction (suffix • state)
  · letI : MulAction
        ((Con.ker
          (MulAction.toEndHom
            (M := FreeMonoid Action) (α := State))).Quotient)
        State :=
      MulAction.ofEndHom
        (Con.kerLift
          (MulAction.toEndHom (M := FreeMonoid Action) (α := State)))
    change FaithfulSMul
      ((Con.ker
        (MulAction.toEndHom
          (M := FreeMonoid Action) (α := State))).Quotient)
      State
    refine ⟨?_⟩
    intro first second sameAction
    apply Con.kerLift_injective
      (MulAction.toEndHom (M := FreeMonoid Action) (α := State))
    funext state
    exact sameAction state

#print axioms effective_protocol_action_monoid

end D5.S3.ConceptDynamics.Control.EffectiveProtocolActionMonoid
