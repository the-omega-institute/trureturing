/- GID: D5/S3/ConceptDynamics/NormativeStructure/ObserverActionRuleDecidability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/ObserverActionRuleDecidability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Actor readouts decide mirrored rules exactly under transition compatibility. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-28):
   * Searches for transition compatibility, actor-relative decidability, wishes,
     capability, and readout factorization found no exact D5 theorem.
   * `AnswerabilityCriterion` and `InterventionTargetFactorization` are adjacent
     factorization results, but neither proves the universal converse or the three
     action-rule clauses below.
   * Pinned Mathlib's `Function.FactorsThrough` is the source's fiber-constancy
     notion. `Function.factorsThrough_iff` is an adjacent existence theorem; the
     proof below works directly at the source's kernel-constancy strength. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.ObserverActionRuleDecidability

universe u v w z

/-- A mirrored transition is compatible with an actor's readout exactly when
every wish readable by that actor still yields a readable negative rule. Under
the same compatibility, the positive rule is readable from the actor's wish
and capability. An actual-action rule using another actor's wish is readable
exactly when that pulled-back wish is readable. -/
theorem observer_action_rule_decidability
    {X : Type u} {U : Type v} {I : Type w} {B : I -> Type z}
    (readout : forall actor, X -> B actor)
    (transition : X -> U -> I -> I -> X) (actor : I) :
    let actorInputReadout : X × U × I -> B actor × U × I :=
      fun input => (readout actor input.1, input.2)
    let mirroredTransition : X × U × I -> X :=
      fun input => transition input.1 input.2.1 input.2.2 actor
    let actualTransition : X × U × I -> X :=
      fun input => transition input.1 input.2.1 actor input.2.2
    ((readout actor ∘ mirroredTransition).FactorsThrough actorInputReadout ↔
      forall wish : X -> Prop,
        wish.FactorsThrough (readout actor) ->
          (fun input => Not (wish (mirroredTransition input))).FactorsThrough
            actorInputReadout) ∧
    (forall (wish : X -> Prop) (capable : X × U × I -> Prop),
      wish.FactorsThrough (readout actor) ->
      capable.FactorsThrough actorInputReadout ->
      (readout actor ∘ mirroredTransition).FactorsThrough actorInputReadout ->
        (fun input => wish (mirroredTransition input) ∧ capable input).FactorsThrough
          actorInputReadout) ∧
    (forall otherWish : forall _recipient, X -> Prop,
      (fun input => Not (otherWish input.2.2 (actualTransition input))).FactorsThrough
          actorInputReadout ↔
        (fun input => otherWish input.2.2 (actualTransition input)).FactorsThrough
          actorInputReadout) := by
  dsimp only
  constructor
  · constructor
    · intro compatible wish wishReadable input input' sameInput
      exact congrArg Not (wishReadable (compatible sameInput))
    · intro everyWish input input' sameInput
      by_contra differentOutput
      let separatingWish : X -> Prop := fun state =>
        readout actor state =
          readout actor (transition input.1 input.2.1 input.2.2 actor)
      have separatingReadable : separatingWish.FactorsThrough (readout actor) := by
        intro state state' sameReadout
        apply propext
        constructor
        · intro hmatch
          exact sameReadout.symm.trans hmatch
        · intro hmatch
          exact sameReadout.trans hmatch
      have negativeReadable := everyWish separatingWish separatingReadable
      have equalNegations := negativeReadable sameInput
      have notSecond : Not
          (separatingWish
            (transition input'.1 input'.2.1 input'.2.2 actor)) := by
        intro hmatch
        exact differentOutput hmatch.symm
      have notFirst : Not
          (separatingWish
            (transition input.1 input.2.1 input.2.2 actor)) := by
        exact Eq.mpr equalNegations notSecond
      exact notFirst rfl
  · constructor
    · intro wish capable wishReadable capableReadable compatible input input' sameInput
      exact congrArg₂ And
        (wishReadable (compatible sameInput)) (capableReadable sameInput)
    · intro otherWish
      constructor
      · intro negativeReadable input input' sameInput
        have equalNegations := negativeReadable sameInput
        apply propext
        constructor
        · intro firstWish
          by_contra notSecondWish
          have notFirstWish : Not
              (otherWish input.2.2
                (transition input.1 input.2.1 actor input.2.2)) := by
            exact Eq.mpr equalNegations notSecondWish
          exact notFirstWish firstWish
        · intro secondWish
          by_contra notFirstWish
          have notSecondWish : Not
              (otherWish input'.2.2
                (transition input'.1 input'.2.1 actor input'.2.2)) := by
            exact Eq.mp equalNegations notFirstWish
          exact notSecondWish secondWish
      · intro positiveReadable input input' sameInput
        exact congrArg Not (positiveReadable sameInput)

/-- The theorem's premises are jointly inhabited by identity readouts and an
identity transition. -/
example :
    let readout : forall _ : Unit, Bool -> Bool := fun _ state => state
    let transition : Bool -> Unit -> Unit -> Unit -> Bool := fun state _ _ _ => state
    (readout () ∘ fun input : Bool × Unit × Unit =>
      transition input.1 input.2.1 input.2.2 ()).FactorsThrough
        (fun input => (readout () input.1, input.2)) := by
  dsimp
  intro input input' sameInput
  exact congrArg Prod.fst sameInput

#print axioms observer_action_rule_decidability

end D5.S3.ConceptDynamics.NormativeStructure.ObserverActionRuleDecidability
