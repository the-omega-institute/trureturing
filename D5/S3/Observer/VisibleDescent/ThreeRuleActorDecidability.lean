/- GID: D5/S3/Observer/VisibleDescent/ThreeRuleActorDecidability
   generality: G
   mirror-B: D5/B/S3/Observer/VisibleDescent/ThreeRuleActorDecidability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize which actor-relative rule predicates descend through the actor readout. -/

import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Push

/- Library-search audit trail (2026-09-04):
   * Repository shape searches found `AnswerabilityCriterion`, whose theorem
     relates one question to a concept fiber and an empty defect relation, but
     no declaration carrying the transition converse or all three rule forms.
   * Exact pinned-Mathlib hit `Function.FactorsThrough` supplies fiber
     constancy, and `Function.factorsThrough_iff` supplies the descended
     predicate in the structural-rule clause. Both are applied below.
   * Pinned-Mathlib searches for the universal separating-predicate converse
     and the combined desire-and-ability clause found no packaged theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.VisibleDescent.ThreeRuleActorDecidability

/-- Actor-readout compatibility preserves the negative mirrored rule and the
positive mirrored desire-and-ability rule. It is also exactly the condition
that preserves every actor-visible desire: an incompatible transition is
separated by a desire predicate on the actor's readout. For the actual action,
the recipient's negative desire is actor-visible exactly when the underlying
recipient desire has a descended predicate on the actor's observation type. -/
theorem three_rule_actor_decidability
    {State Action Agent : Type*}
    (Observation : Agent -> Type*)
    (readout : (agent : Agent) -> State -> Observation agent)
    (transition : State -> Action -> Agent -> Agent -> State)
    (desire : Agent -> State -> Prop)
    (ability : Agent -> State -> Action -> Agent -> Prop)
    (action : Action) (actor recipient : Agent) :
    let q : State -> Observation actor := readout actor
    let mirrored : State -> State :=
      fun state => transition state action recipient actor
    let actual : State -> State :=
      fun state => transition state action actor recipient
    let compatible : Prop := Function.FactorsThrough (q ∘ mirrored) q
    (Function.FactorsThrough (desire actor) q ->
      compatible ->
      Function.FactorsThrough (fun state => Not (desire actor (mirrored state))) q) /\
    ((Not compatible) ->
      exists selfDesire : State -> Prop,
        Function.FactorsThrough selfDesire q /\
          Not (Function.FactorsThrough
            (fun state => Not (selfDesire (mirrored state))) q)) /\
    (compatible <->
      forall selfDesire : State -> Prop,
        Function.FactorsThrough selfDesire q ->
          Function.FactorsThrough
            (fun state => Not (selfDesire (mirrored state))) q) /\
    (Function.FactorsThrough (desire actor) q ->
      Function.FactorsThrough
        (fun state => ability actor state action recipient) q ->
      compatible ->
      Function.FactorsThrough
        (fun state =>
          desire actor (mirrored state) /\ ability actor state action recipient) q) /\
    (Function.FactorsThrough
        (fun state => Not (desire recipient (actual state))) q <->
      exists descended : Observation actor -> Prop,
        (fun state => desire recipient (actual state)) = descended ∘ q) := by
  dsimp only
  have forward :
      forall selfDesire : State -> Prop,
        Function.FactorsThrough selfDesire (readout actor) ->
        Function.FactorsThrough
          ((readout actor) ∘ fun state => transition state action recipient actor)
          (readout actor) ->
        Function.FactorsThrough
          (fun state => Not (selfDesire (transition state action recipient actor)))
          (readout actor) := by
    intro selfDesire selfDesireVisible transitionCompatible first second sameReadout
    exact congrArg Not (selfDesireVisible (transitionCompatible sameReadout))
  have counterexample :
      (Not (Function.FactorsThrough
        ((readout actor) ∘ fun state => transition state action recipient actor)
        (readout actor))) ->
      exists selfDesire : State -> Prop,
        Function.FactorsThrough selfDesire (readout actor) /\
          Not (Function.FactorsThrough
            (fun state => Not (selfDesire (transition state action recipient actor)))
            (readout actor)) := by
    intro notCompatible
    rw [Function.FactorsThrough] at notCompatible
    push Not at notCompatible
    obtain ⟨first, second, sameReadout, differentAfter⟩ := notCompatible
    let separatingDesire : State -> Prop :=
      fun state =>
        readout actor state =
          readout actor (transition first action recipient actor)
    refine ⟨separatingDesire, ?_, ?_⟩
    · intro left right same
      exact congrArg
        (fun value =>
          value = readout actor (transition first action recipient actor)) same
    · intro allegedlyVisible
      have sameNegation := allegedlyVisible sameReadout
      have holdsAtFirst :
          separatingDesire (transition first action recipient actor) := rfl
      have notAtSecond :
          Not (separatingDesire (transition second action recipient actor)) := by
        intro reversed
        exact differentAfter reversed.symm
      have notAtFirst :
          Not (separatingDesire (transition first action recipient actor)) := by
        exact (Iff.of_eq sameNegation).mpr notAtSecond
      exact notAtFirst holdsAtFirst
  have universalCriterion :
      Function.FactorsThrough
          ((readout actor) ∘ fun state => transition state action recipient actor)
          (readout actor) <->
        forall selfDesire : State -> Prop,
          Function.FactorsThrough selfDesire (readout actor) ->
            Function.FactorsThrough
              (fun state => Not (selfDesire (transition state action recipient actor)))
              (readout actor) := by
    constructor
    · intro compatible selfDesire selfDesireVisible
      exact forward selfDesire selfDesireVisible compatible
    · intro everyDesire
      by_contra notCompatible
      obtain ⟨selfDesire, selfDesireVisible, pullbackNotVisible⟩ :=
        counterexample notCompatible
      exact pullbackNotVisible (everyDesire selfDesire selfDesireVisible)
  have positiveRule :
      Function.FactorsThrough (desire actor) (readout actor) ->
      Function.FactorsThrough
        (fun state => ability actor state action recipient) (readout actor) ->
      Function.FactorsThrough
          ((readout actor) ∘ fun state => transition state action recipient actor)
          (readout actor) ->
      Function.FactorsThrough
        (fun state =>
          desire actor (transition state action recipient actor) /\
            ability actor state action recipient)
        (readout actor) := by
    intro desireVisible abilityVisible transitionCompatible first second sameReadout
    have sameDesire := desireVisible (transitionCompatible sameReadout)
    have sameAbility := abilityVisible sameReadout
    apply propext
    constructor
    · rintro ⟨holdsDesire, holdsAbility⟩
      exact ⟨
        (Iff.of_eq sameDesire).mp holdsDesire,
        (Iff.of_eq sameAbility).mp holdsAbility⟩
    · rintro ⟨holdsDesire, holdsAbility⟩
      exact ⟨
        (Iff.of_eq sameDesire).mpr holdsDesire,
        (Iff.of_eq sameAbility).mpr holdsAbility⟩
  have structuralRule :
      Function.FactorsThrough
          (fun state => Not (desire recipient (transition state action actor recipient)))
          (readout actor) <->
        exists descended : Observation actor -> Prop,
          (fun state => desire recipient (transition state action actor recipient)) =
            descended ∘ readout actor := by
    have negationCriterion :
        Function.FactorsThrough
            (fun state => Not (desire recipient (transition state action actor recipient)))
            (readout actor) <->
          Function.FactorsThrough
            (fun state => desire recipient (transition state action actor recipient))
            (readout actor) := by
      constructor
      · intro negationVisible first second sameReadout
        have sameNegation := negationVisible sameReadout
        apply propext
        have equivalentNegations :
            (Not (desire recipient (transition first action actor recipient))) <->
              Not (desire recipient (transition second action actor recipient)) :=
          Iff.of_eq sameNegation
        constructor
        · intro holdsAtFirst
          by_contra notAtSecond
          exact (equivalentNegations.mpr notAtSecond) holdsAtFirst
        · intro holdsAtSecond
          by_contra notAtFirst
          exact (equivalentNegations.mp notAtFirst) holdsAtSecond
      · intro desireVisible first second sameReadout
        exact congrArg Not (desireVisible sameReadout)
    exact negationCriterion.trans
      (Function.factorsThrough_iff
        (f := readout actor)
        (fun state => desire recipient (transition state action actor recipient)))
  exact ⟨
    forward (desire actor),
    counterexample,
    universalCriterion,
    positiveRule,
    structuralRule⟩

/-- The source carrier is inhabited in a concrete model. -/
example : PUnit := PUnit.unit

/-- A constant desire visibly satisfies the factorization premise. -/
example : Function.FactorsThrough
    (fun _ : PUnit => True) (fun _ : PUnit => PUnit.unit) := by
  intro first second same
  rfl

#print axioms three_rule_actor_decidability

end D5.S3.Observer.VisibleDescent.ThreeRuleActorDecidability
