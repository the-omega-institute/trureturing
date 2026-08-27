/- GID: D5/S3/Observer/VisibleDescent/RowColumnObserverCore
   generality: G
   mirror-B: D5/B/S3/Observer/VisibleDescent/RowColumnObserverCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quotienting equal evaluation rows and columns yields a separating observer core. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-28):
   * Current-tree name and body-shape searches found no theorem simultaneously
     quotienting both state rows and protocol columns of an arbitrary evaluation.
     Existing observer and concept quotients descend only one carrier at a time.
   * `GraphPairingCriterion` characterizes injectivity of a specialized
     Boolean graph pairing but does not construct either quotient or its descent.
   * Exact pinned-Mathlib hits `Setoid.ker`, `Quotient.liftOn₂'`,
     `Quotient.liftOn₂'_mk''`, `Quotient.inductionOn₂'`, and `Quotient.sound`
     provide the two canonical kernel quotients, descended evaluation,
     representative computation, and quotient reasoning used below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.VisibleDescent.RowColumnObserverCore

/-- Quotient an arbitrary evaluation by equality of state rows and protocol
columns. The canonical two-variable quotient lift is representative-independent,
computes as the source evaluation, and separates distinct classes on both sides. -/
theorem row_column_observer_core
    {State Protocol Value : Type*}
    (evaluate : State -> Protocol -> Value) :
    let stateRelation : Setoid State := Setoid.ker evaluate
    let protocolRelation : Setoid Protocol :=
      Setoid.ker (fun protocol => fun state => evaluate state protocol)
    let descended :
        Quotient stateRelation -> Quotient protocolRelation -> Value :=
      fun stateClass protocolClass =>
        Quotient.liftOn₂' stateClass protocolClass evaluate
          (fun _ firstProtocol secondState _ sameRow sameColumn =>
            (congrFun sameRow firstProtocol).trans
              (congrFun sameColumn secondState))
    (forall firstState secondState firstProtocol secondProtocol,
      stateRelation firstState secondState ->
      protocolRelation firstProtocol secondProtocol ->
      evaluate firstState firstProtocol =
        evaluate secondState secondProtocol) /\
    (forall first second : Quotient stateRelation,
      first ≠ second ->
      exists protocolClass : Quotient protocolRelation,
        descended first protocolClass ≠ descended second protocolClass) /\
    (forall first second : Quotient protocolRelation,
      first ≠ second ->
      exists stateClass : Quotient stateRelation,
        descended stateClass first ≠ descended stateClass second) := by
  dsimp only
  constructor
  · intro firstState secondState firstProtocol secondProtocol sameRow sameColumn
    exact (congrFun sameRow firstProtocol).trans
      (congrFun sameColumn secondState)
  constructor
  · intro first second
    refine Quotient.inductionOn₂' first second ?_
    intro firstState secondState distinct
    classical
    by_contra noWitness
    simp only [not_exists, not_ne_iff] at noWitness
    apply distinct
    apply Quotient.sound
    change evaluate firstState = evaluate secondState
    funext protocol
    simpa only [Quotient.liftOn₂'_mk''] using
      noWitness (Quotient.mk'' protocol)
  · intro first second
    refine Quotient.inductionOn₂' first second ?_
    intro firstProtocol secondProtocol distinct
    classical
    by_contra noWitness
    simp only [not_exists, not_ne_iff] at noWitness
    apply distinct
    apply Quotient.sound
    change (fun state => evaluate state firstProtocol) =
      (fun state => evaluate state secondProtocol)
    funext state
    simpa only [Quotient.liftOn₂'_mk''] using
      noWitness (Quotient.mk'' state)

#print axioms row_column_observer_core

end D5.S3.Observer.VisibleDescent.RowColumnObserverCore
