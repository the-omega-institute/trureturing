/- GID: D5/S3/Observer/VisibleDescent/ThreeRuleActorDecidability
   generality: G
   mirror-B: D5/B/S3/Observer/VisibleDescent/ThreeRuleActorDecidability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Expose all actor-readout descent clauses on the full action-input carrier. -/

import D5.S3.ConceptDynamics.NormativeStructure.ObserverActionRuleDecidability
import Mathlib.Tactic.Push

/- Library-search audit trail (2026-09-04):
   * Exact repository owner `observer_action_rule_decidability` supplies the
     full `X × U × I` carrier, compatibility criterion, positive rule, and
     recipient-pullback polarity equivalence. It is applied below.
   * That owner does not expose the source's separating desire or descended
     predicate as public conjuncts, so this theorem adds exactly those clauses.
   * Exact pinned-Mathlib hit `Function.factorsThrough_iff` supplies the
     descended predicate; no whole-statement Mathlib theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.VisibleDescent.ThreeRuleActorDecidability

open D5.S3.ConceptDynamics.NormativeStructure.ObserverActionRuleDecidability

universe u v w z

/-- On the full state-action-recipient carrier, transition compatibility
preserves the negative and positive actor-relative rules. Its negation has an
explicit separating actor-visible desire, and the recipient-relative rule is
actor-visible exactly when its positive pullback has a descended predicate. -/
theorem three_rule_actor_decidability
    {X : Type u} {U : Type v} {I : Type w} {B : I -> Type z}
    (readout : forall agent, X -> B agent)
    (transition : X -> U -> I -> I -> X) (actor : I) :
    let actorInputReadout : X × U × I -> B actor × U × I :=
      fun input => (readout actor input.1, input.2)
    let mirroredTransition : X × U × I -> X :=
      fun input => transition input.1 input.2.1 input.2.2 actor
    let actualTransition : X × U × I -> X :=
      fun input => transition input.1 input.2.1 actor input.2.2
    let compatible : Prop :=
      (readout actor ∘ mirroredTransition).FactorsThrough actorInputReadout
    (forall wish : X -> Prop,
      wish.FactorsThrough (readout actor) ->
      compatible ->
        (fun input => Not (wish (mirroredTransition input))).FactorsThrough
          actorInputReadout) ∧
    ((Not compatible) ->
      exists wish : X -> Prop,
        wish.FactorsThrough (readout actor) ∧
          Not ((fun input => Not (wish (mirroredTransition input))).FactorsThrough
            actorInputReadout)) ∧
    (compatible ↔
      forall wish : X -> Prop,
        wish.FactorsThrough (readout actor) ->
          (fun input => Not (wish (mirroredTransition input))).FactorsThrough
            actorInputReadout) ∧
    (forall (wish : X -> Prop) (capable : X × U × I -> Prop),
      wish.FactorsThrough (readout actor) ->
      capable.FactorsThrough actorInputReadout ->
      compatible ->
        (fun input => wish (mirroredTransition input) ∧ capable input).FactorsThrough
          actorInputReadout) ∧
    (forall otherWish : forall _recipient, X -> Prop,
      (fun input : X × U × I =>
        Not (otherWish input.2.2 (actualTransition input))).FactorsThrough
          actorInputReadout ↔
        exists descended : B actor × U × I -> Prop,
          (fun input : X × U × I =>
            otherWish input.2.2 (actualTransition input)) =
            descended ∘ actorInputReadout) := by
  dsimp only
  obtain ⟨criterion, positiveRule, polarityCriterion⟩ :=
    observer_action_rule_decidability readout transition actor
  have forwardRule :
      forall wish : X -> Prop,
        wish.FactorsThrough (readout actor) ->
        (readout actor ∘ fun input : X × U × I =>
          transition input.1 input.2.1 input.2.2 actor).FactorsThrough
            (fun input : X × U × I => (readout actor input.1, input.2)) ->
          (fun input : X × U × I => Not (wish
            (transition input.1 input.2.1 input.2.2 actor))).FactorsThrough
              (fun input : X × U × I => (readout actor input.1, input.2)) := by
    intro wish wishReadable compatible
    exact (criterion.mp compatible) wish wishReadable
  have separatingRule :
      (Not ((readout actor ∘ fun input : X × U × I =>
        transition input.1 input.2.1 input.2.2 actor).FactorsThrough
          (fun input : X × U × I => (readout actor input.1, input.2)))) ->
        exists wish : X -> Prop,
          wish.FactorsThrough (readout actor) ∧
            Not ((fun input : X × U × I => Not (wish
              (transition input.1 input.2.1 input.2.2 actor))).FactorsThrough
                (fun input : X × U × I => (readout actor input.1, input.2))) := by
    intro notCompatible
    have notEveryWish : Not (forall wish : X -> Prop,
        wish.FactorsThrough (readout actor) ->
          (fun input : X × U × I => Not (wish
            (transition input.1 input.2.1 input.2.2 actor))).FactorsThrough
              (fun input : X × U × I => (readout actor input.1, input.2))) := by
      intro everyWish
      exact notCompatible (criterion.mpr everyWish)
    push Not at notEveryWish
    exact notEveryWish
  have structuralRule :
      forall otherWish : forall _recipient, X -> Prop,
        (fun input : X × U × I => Not (otherWish input.2.2
          (transition input.1 input.2.1 actor input.2.2))).FactorsThrough
            (fun input : X × U × I => (readout actor input.1, input.2)) ↔
          exists descended : B actor × U × I -> Prop,
            (fun input : X × U × I => otherWish input.2.2
              (transition input.1 input.2.1 actor input.2.2)) =
                descended ∘ fun input : X × U × I =>
                  (readout actor input.1, input.2) := by
    intro otherWish
    exact (polarityCriterion otherWish).trans
      (Function.factorsThrough_iff
        (f := fun input : X × U × I => (readout actor input.1, input.2))
        (fun input => otherWish input.2.2
          (transition input.1 input.2.1 actor input.2.2)))
  exact ⟨forwardRule, separatingRule, criterion, positiveRule, structuralRule⟩

/-- The source input carrier is inhabited in a concrete model. -/
example : Bool × Unit × Unit := (false, (), ())

/-- Identity readout and transition satisfy the compatibility premise. -/
example :
    let readout : forall _ : Unit, Bool -> Bool := fun _ state => state
    let transition : Bool -> Unit -> Unit -> Unit -> Bool := fun state _ _ _ => state
    (readout () ∘ fun input : Bool × Unit × Unit =>
      transition input.1 input.2.1 input.2.2 ()).FactorsThrough
        (fun input => (readout () input.1, input.2)) := by
  dsimp
  intro input input' sameInput
  exact congrArg Prod.fst sameInput

#print axioms three_rule_actor_decidability

end D5.S3.Observer.VisibleDescent.ThreeRuleActorDecidability
