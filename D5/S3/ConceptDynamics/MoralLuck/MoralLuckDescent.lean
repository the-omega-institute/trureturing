/- GID: D5/S3/ConceptDynamics/MoralLuck/MoralLuckDescent
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/MoralLuck/MoralLuckDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: In a finite inhabited model, control descent is equivalent to an empty fiber defect. -/

import D5.S0.Rewriting.Quotients.AnswerabilityCriterion
import Mathlib.Data.Fintype.Basic

/- Library-search audit trail (2026-08-21).
   * Exact repository hit: `D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion`
     packages factorization through a readout, fiber constancy, and an empty defect relation.
     Its factorization direction is applied directly below.
   * Exact pinned-Mathlib hit used by that repository theorem: `Function.factorsThrough_iff`.
   * Searches for `moral luck`, `control principle`, and the exact descent equivalence in
     `D5/` and `.lake/packages/mathlib/Mathlib/` found no existing declaration for this wrapper.
   * `lake env loogle` and `lake env leansearch` are unavailable in this environment; repository
     and pinned Mathlib `rg` searches were used instead.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.MoralLuck.MoralLuckDescent

/- A control principle is a factorization of the evaluation through the control readout. -/
def ControlPrinciple {X B L : Type*} (control : X → B) (evaluation : X → L) : Prop :=
  ∃ factor : B → L, evaluation = factor ∘ control

/- A moral-luck witness is a pair in one control fiber with distinct evaluations. -/
def MoralLuckWitness {X B L : Type*} (control : X → B) (evaluation : X → L) : Prop :=
  ∃ x y : X, control x = control y ∧ evaluation x ≠ evaluation y

/- In a finite inhabited model, descent holds exactly when no control fiber carries
   two different evaluation values. -/
theorem moral_luck_descent_iff
    {X B L : Type*} [Fintype X] [Fintype B] [Fintype L] [Nonempty X]
    (control : X → B) (evaluation : X → L) :
    ControlPrinciple control evaluation ↔ ¬ MoralLuckWitness control evaluation := by
  let anchor : X := Classical.choice (inferInstance : Nonempty X)
  have criterion :=
    D5.S0.Rewriting.Quotients.AnswerabilityCriterion.answerability_criterion
      anchor control evaluation
  constructor
  · intro hControl hLuck
    rcases hLuck with ⟨x, y, hxy, hne⟩
    exact hne (criterion.1.mp hControl hxy)
  · intro hNoLuck
    apply criterion.1.mpr
    intro x y hxy
    by_contra hne
    exact hNoLuck ⟨x, y, hxy, hne⟩

example :
    ControlPrinciple (fun x : Bool => x) (fun x : Bool => x) := by
  exact ⟨id, rfl⟩

example :
    ¬ MoralLuckWitness (fun x : Bool => x) (fun x : Bool => x) := by
  intro witness
  rcases witness with ⟨x, y, hxy, hne⟩
  exact hne hxy

#print axioms moral_luck_descent_iff

end D5.S3.ConceptDynamics.MoralLuck.MoralLuckDescent
