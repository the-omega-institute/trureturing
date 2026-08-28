/- GID: D5/S3/Observer/Refinement/StateProtocolQuotientOrderCommutation
   generality: G
   mirror-B: D5/B/S3/Observer/Refinement/StateProtocolQuotientOrderCommutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evaluation-derived state and protocol quotients commute canonically. -/

import D5.S3.Observer.Refinement.DoubleExtensionalEvaluationDescent

/- Library-search audit trail (2026-08-28):
   * D5 name and body-shape searches found canonical simultaneous evaluation
     descent, row-column separation, and one-axis quotient maps, but no theorem
     comparing the two iterated quotient orders.
   * `Setoid.ker`, `Quotient.map`, `Quotient.liftOn₂`, and
     `Equiv.ofBijective` are the pinned-Mathlib primitives applied below.
   * No existing D5 definition has the bodies of the second-stage setoids,
     order-comparison maps, or induced evaluations introduced here. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Refinement.StateProtocolQuotientOrderCommutation

universe u v w

/-- Protocols are equivalent after the state quotient when they agree on
every state class. -/
def protocolAfterStateSetoid
    {State : Type u} {Protocol : Type v} {Value : Type w}
    (evaluation : State -> Protocol -> Value) : Setoid Protocol :=
  Setoid.ker fun protocol => fun stateClass : Quotient (Setoid.ker evaluation) =>
    Quotient.liftOn stateClass (fun state => evaluation state protocol)
      (fun _ _ sameRow => congrFun sameRow protocol)

/-- States are equivalent after the protocol quotient when they agree on
every protocol class. -/
def stateAfterProtocolSetoid
    {State : Type u} {Protocol : Type v} {Value : Type w}
    (evaluation : State -> Protocol -> Value) : Setoid State :=
  Setoid.ker fun state => fun protocolClass :
      Quotient (Setoid.ker fun protocol => fun state => evaluation state protocol) =>
    Quotient.liftOn protocolClass (fun protocol => evaluation state protocol)
      (fun _ _ sameColumn => congrFun sameColumn state)

/-- The evaluation obtained by quotienting states first and protocols second. -/
def stateFirstEvaluation
    {State : Type u} {Protocol : Type v} {Value : Type w}
    (evaluation : State -> Protocol -> Value) :
    Quotient (Setoid.ker evaluation) ->
      Quotient (protocolAfterStateSetoid evaluation) -> Value :=
  fun stateClass protocolClass =>
    Quotient.liftOn₂ stateClass protocolClass evaluation
      (fun _ firstProtocol secondState _ sameRow sameColumn =>
        (congrFun sameRow firstProtocol).trans
          (congrFun sameColumn
            (Quotient.mk (Setoid.ker evaluation) secondState)))

/-- The evaluation obtained by quotienting protocols first and states second. -/
def protocolFirstEvaluation
    {State : Type u} {Protocol : Type v} {Value : Type w}
    (evaluation : State -> Protocol -> Value) :
    Quotient (stateAfterProtocolSetoid evaluation) ->
      Quotient (Setoid.ker fun protocol => fun state => evaluation state protocol) ->
        Value :=
  fun stateClass protocolClass =>
    Quotient.liftOn₂ stateClass protocolClass evaluation
      (fun firstState _ _ secondProtocol sameRow sameColumn =>
        (congrFun sameColumn firstState).trans
          (congrFun sameRow
            (Quotient.mk
              (Setoid.ker fun protocol => fun state => evaluation state protocol)
              secondProtocol)))

/-- The identity on representatives maps the state-first carrier to the
protocol-first state carrier. -/
def stateOrderMap
    {State : Type u} {Protocol : Type v} {Value : Type w}
    (evaluation : State -> Protocol -> Value) :
    Quotient (Setoid.ker evaluation) ->
      Quotient (stateAfterProtocolSetoid evaluation) :=
  Quotient.map id (by
    intro first second sameRow
    apply funext
    intro protocolClass
    refine Quotient.inductionOn protocolClass ?_
    intro protocol
    exact congrFun sameRow protocol)

/-- The identity on representatives maps the state-first protocol carrier to
the protocol-first carrier. -/
def protocolOrderMap
    {State : Type u} {Protocol : Type v} {Value : Type w}
    (evaluation : State -> Protocol -> Value) :
    Quotient (protocolAfterStateSetoid evaluation) ->
      Quotient (Setoid.ker fun protocol => fun state => evaluation state protocol) :=
  Quotient.map id (by
    intro first second sameAfterState
    apply funext
    intro state
    exact congrFun sameAfterState (Quotient.mk (Setoid.ker evaluation) state))

/-- The canonical equivalence between the final state carriers in the two
quotient orders. -/
noncomputable def stateOrderEquiv
    {State : Type u} {Protocol : Type v} {Value : Type w}
    (evaluation : State -> Protocol -> Value) :
    Quotient (Setoid.ker evaluation) ≃
      Quotient (stateAfterProtocolSetoid evaluation) :=
  Equiv.ofBijective (stateOrderMap evaluation) (by
    constructor
    · intro first second equalImages
      refine Quotient.inductionOn₂ first second ?_ equalImages
      intro firstState secondState equalClasses
      apply Quotient.sound
      apply funext
      intro protocol
      exact congrFun (Quotient.exact equalClasses)
        (Quotient.mk
          (Setoid.ker fun protocol => fun state => evaluation state protocol)
          protocol)
    · intro target
      obtain ⟨state, rfl⟩ := Quotient.exists_rep target
      exact ⟨Quotient.mk (Setoid.ker evaluation) state, rfl⟩)

/-- The canonical equivalence between the final protocol carriers in the two
quotient orders. -/
noncomputable def protocolOrderEquiv
    {State : Type u} {Protocol : Type v} {Value : Type w}
    (evaluation : State -> Protocol -> Value) :
    Quotient (protocolAfterStateSetoid evaluation) ≃
      Quotient (Setoid.ker fun protocol => fun state => evaluation state protocol) :=
  Equiv.ofBijective (protocolOrderMap evaluation) (by
    constructor
    · intro first second equalImages
      refine Quotient.inductionOn₂ first second ?_ equalImages
      intro firstProtocol secondProtocol equalClasses
      apply Quotient.sound
      apply funext
      intro stateClass
      refine Quotient.inductionOn stateClass ?_
      intro state
      exact congrFun (Quotient.exact equalClasses) state
    · intro target
      obtain ⟨protocol, rfl⟩ := Quotient.exists_rep target
      exact ⟨Quotient.mk (protocolAfterStateSetoid evaluation) protocol, rfl⟩)

/-- The state-first and protocol-first paths have canonical equivalent state
and protocol carriers. Both equivalences preserve representatives, and the
two descended evaluations agree under those equivalences. -/
theorem state_protocol_quotient_order_commutes
    {State : Type u} {Protocol : Type v} {Value : Type w}
    (evaluation : State -> Protocol -> Value) :
    (∀ state : State,
      stateOrderEquiv evaluation
          (Quotient.mk (Setoid.ker evaluation) state) =
        Quotient.mk (stateAfterProtocolSetoid evaluation) state) ∧
    (∀ protocol : Protocol,
      protocolOrderEquiv evaluation
          (Quotient.mk (protocolAfterStateSetoid evaluation) protocol) =
        Quotient.mk
          (Setoid.ker fun protocol => fun state => evaluation state protocol)
          protocol) ∧
    (∀ state protocol,
      stateFirstEvaluation evaluation state protocol =
        protocolFirstEvaluation evaluation
          (stateOrderEquiv evaluation state)
          (protocolOrderEquiv evaluation protocol)) := by
  constructor
  · intro state
    rfl
  constructor
  · intro protocol
    rfl
  · intro state protocol
    refine Quotient.inductionOn state ?_
    intro stateRepresentative
    refine Quotient.inductionOn protocol ?_
    intro protocolRepresentative
    rfl

#print axioms state_protocol_quotient_order_commutes

end D5.S3.Observer.Refinement.StateProtocolQuotientOrderCommutation
