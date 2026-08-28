/- GID: D5/S3/Observer/Refinement/DoubleExtensionalEvaluationDescent
   generality: G
   mirror-B: D5/B/S3/Observer/Refinement/DoubleExtensionalEvaluationDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evaluation descends canonically through its row and column kernels. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-28):
   * D5 searches found application-specific quotient metrics, predictive
     descents, and one-sided kernel factorizations, but no joint row-and-column
     evaluation descent through both evaluation-derived kernels.
   * Pinned Mathlib exact components `Quotient.liftOn₂`,
     `Quotient.liftOn₂_mk`, and `Quotient.mk_surjective` are applied directly.
   * Body-shape searches found no existing D5 primitive with this construction.
     This module introduces no `def` or `abbrev`; both setoids and the canonical
     lift are constructed as public theorem-local objects. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Refinement.DoubleExtensionalEvaluationDescent

/-- Quotienting states by equal evaluation rows and protocols by equal
evaluation columns makes the canonical evaluation independent of both
representatives. Its computation rule uniquely determines the descended map. -/
theorem double_extensional_evaluation_descent
    {State Protocol Value : Type*} (evaluation : State -> Protocol -> Value) :
    let stateKernel : Setoid State := Setoid.ker fun state => evaluation state
    let protocolKernel : Setoid Protocol := Setoid.ker fun protocol state =>
      evaluation state protocol
    let descended : Quotient stateKernel -> Quotient protocolKernel -> Value :=
      fun stateClass protocolClass =>
        Quotient.liftOn₂ stateClass protocolClass evaluation
          (fun x p y q stateRelated protocolRelated =>
            (show evaluation x p = evaluation y p from congrFun stateRelated p).trans
              (show evaluation y p = evaluation y q from congrFun protocolRelated y))
    (∀ (x y : State) (p q : Protocol),
      stateKernel x y -> protocolKernel p q ->
        evaluation x p = evaluation y q) ∧
    (∀ (x : State) (p : Protocol),
      descended (Quotient.mk' x) (Quotient.mk' p) = evaluation x p) ∧
    (∀ other : Quotient stateKernel -> Quotient protocolKernel -> Value,
      (∀ (x : State) (p : Protocol),
        other (Quotient.mk' x) (Quotient.mk' p) = evaluation x p) ->
      other = descended) := by
  dsimp only
  constructor
  · intro x y p q stateRelated protocolRelated
    exact (congrFun stateRelated p).trans (congrFun protocolRelated y)
  constructor
  · intros
    rfl
  · intro other otherComputes
    funext stateClass protocolClass
    rcases Quotient.mk_surjective stateClass with ⟨state, rfl⟩
    rcases Quotient.mk_surjective protocolClass with ⟨protocol, rfl⟩
    exact otherComputes state protocol

#print axioms double_extensional_evaluation_descent

end D5.S3.Observer.Refinement.DoubleExtensionalEvaluationDescent
