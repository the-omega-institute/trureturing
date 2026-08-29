/- GID: D5/S3/ConceptDynamics/Faithfulness/InjectiveConstantReadoutSubsingleton
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Faithfulness/InjectiveConstantReadoutSubsingleton
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An injective constant readout has a subsingleton source. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-29):
   * D5 searches for an injective constant readout forcing a subsingleton source
     found adjacent constant-readout countermodels, but no theorem with this
     conclusion and generality.
   * Pinned Mathlib supplies `Function.Injective` and `Subsingleton`; the proof
     uses their defining elimination principles directly rather than creating a
     second abstraction layer.
   * A repository-wide search for `Injective` together with `IsConstant` or
     `Subsingleton` found no exact owner for the source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Faithfulness.InjectiveConstantReadoutSubsingleton

universe u v

/-- A readout that is simultaneously injective and constant can have at most
one source state. -/
theorem injective_constant_readout_subsingleton
    {X : Type u} {Y : Type v} (q : X -> Y)
    (injective : Function.Injective q)
    (constant : forall x y : X, q x = q y) :
    Subsingleton X := by
  constructor
  intro x y
  exact injective (constant x y)

/-- Satisfiability probe: the identity readout on the one-point type is both
injective and constant. -/
example :
    Function.Injective (fun x : PUnit => x) /\
      (forall x y : PUnit, (fun z : PUnit => z) x = (fun z : PUnit => z) y) := by
  constructor
  · intro x y equality
    exact equality
  · intro x y
    exact Subsingleton.elim x y

/-- Consequence probe: on a source with two distinct states, no readout can be
both injective and constant. -/
example {X : Type u} {Y : Type v} (q : X -> Y) (x y : X) (different : x ≠ y) :
    Not (Function.Injective q /\ (forall first second : X, q first = q second)) := by
  rintro ⟨injective, constant⟩
  exact different (injective (constant x y))

#print axioms injective_constant_readout_subsingleton

end D5.S3.ConceptDynamics.Faithfulness.InjectiveConstantReadoutSubsingleton
