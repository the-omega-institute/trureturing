/- GID: D5/S3/Observer/Refinement/CanonicalRowColumnSeparation
   generality: G
   mirror-B: D5/B/S3/Observer/Refinement/CanonicalRowColumnSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Behavioral row-column quotients separate both evaluation axes. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-28):
   * Repository searches for a two-sided evaluation quotient, its descended evaluation, and
     separation on both axes found no exact D5 theorem or canonical family definition.
   * The pinned Mathlib search found `Setoid.ker`, `Quotient.lift₂`,
     `Quotient.lift₂_mk`, and `Quotient.sound`, all applied below. The one-axis theorem
     `Setoid.kerLift_injective` does not construct the source's two-sided evaluation map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Refinement.CanonicalRowColumnSeparation

universe u v w

/- The canonical evaluation descended to the row and column behavioral quotients separates
each quotient coordinate. -/
theorem canonical_row_column_separation
    {X : Type u} {P : Type v} {Lambda : Type w} (e : X → P → Lambda) :
    let stateRow : X → P → Lambda := fun x p => e x p
    let protocolColumn : P → X → Lambda := fun p x => e x p
    let collapsedEvaluation :
        Quotient (Setoid.ker stateRow) →
          Quotient (Setoid.ker protocolColumn) → Lambda :=
      Quotient.lift₂ e (by
        intro x p y q hxy hpq
        exact (congrFun hxy p).trans (congrFun hpq y))
    (∀ first second : Quotient (Setoid.ker stateRow),
        (∀ protocol : Quotient (Setoid.ker protocolColumn),
          collapsedEvaluation first protocol = collapsedEvaluation second protocol) →
        first = second) ∧
      (∀ first second : Quotient (Setoid.ker protocolColumn),
        (∀ state : Quotient (Setoid.ker stateRow),
          collapsedEvaluation state first = collapsedEvaluation state second) →
        first = second) := by
  dsimp only
  constructor
  · intro first second hrows
    induction first using Quotient.inductionOn with
    | _ x =>
      induction second using Quotient.inductionOn with
      | _ y =>
        apply Quotient.sound
        apply funext
        intro p
        simpa only [Quotient.lift₂_mk] using
          hrows (Quotient.mk (Setoid.ker fun p : P => fun x : X => e x p) p)
  · intro first second hcolumns
    induction first using Quotient.inductionOn with
    | _ p =>
      induction second using Quotient.inductionOn with
      | _ q =>
        apply Quotient.sound
        apply funext
        intro x
        simpa only [Quotient.lift₂_mk] using
          hcolumns (Quotient.mk (Setoid.ker fun x : X => fun p : P => e x p) x)

/- The Boolean equality table instantiates the canonical two-sided collapse. -/
example :
    let e : Bool → Bool → Bool := fun x p => decide (x = p)
    let stateRow : Bool → Bool → Bool := fun x p => e x p
    let protocolColumn : Bool → Bool → Bool := fun p x => e x p
    let collapsedEvaluation :
        Quotient (Setoid.ker stateRow) →
          Quotient (Setoid.ker protocolColumn) → Bool :=
      Quotient.lift₂ e (by
        intro x p y q hxy hpq
        exact (congrFun hxy p).trans (congrFun hpq y))
    (∀ first second : Quotient (Setoid.ker stateRow),
        (∀ protocol : Quotient (Setoid.ker protocolColumn),
          collapsedEvaluation first protocol = collapsedEvaluation second protocol) →
        first = second) ∧
      (∀ first second : Quotient (Setoid.ker protocolColumn),
        (∀ state : Quotient (Setoid.ker stateRow),
          collapsedEvaluation state first = collapsedEvaluation state second) →
        first = second) := by
  exact canonical_row_column_separation (fun x p : Bool => decide (x = p))

#print axioms canonical_row_column_separation

end D5.S3.Observer.Refinement.CanonicalRowColumnSeparation
