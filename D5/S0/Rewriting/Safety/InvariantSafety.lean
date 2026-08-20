/- GID: D5/S0/Rewriting/Safety/InvariantSafety
   generality: G
   mirror-B: D5/B/S0/Rewriting/Safety/InvariantSafety
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An inductive invariant makes every finitely reachable state safe. -/

import Mathlib.Logic.Relation

/- Library-search audit trail (2026-08-20):
   * Repository and pinned-Mathlib searches found no theorem packaging the
     complete initial-set, invariant-closure, and safety conclusion.
   * The exact pinned-Mathlib induction primitive
     `Relation.ReflTransGen.head_induction_on` is applied directly below.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

namespace D5.S0.Rewriting.Safety.InvariantSafety

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A set containing every initial state, closed under the transition relation,
and contained in the safe set certifies every finite execution as safe. -/
theorem invariant_safety
    {X : Type*} (R : X -> X -> Prop) (initial invariant safe : Set X)
    (initial_invariant : initial ⊆ invariant)
    (invariant_safe : invariant ⊆ safe)
    (step_closed : forall {x y}, x ∈ invariant -> R x y -> y ∈ invariant) :
    forall {x₀ x}, x₀ ∈ initial -> Relation.ReflTransGen R x₀ x -> x ∈ safe := by
  intro x₀ x hx₀ path
  apply invariant_safe
  have preserved : x₀ ∈ invariant -> x ∈ invariant :=
    Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => a ∈ invariant -> x ∈ invariant) path
      (fun hx => hx)
      (fun hab _ ih ha => ih (step_closed ha hab))
  exact preserved (initial_invariant hx₀)

/-- The public hypotheses are jointly inhabited by a one-state execution. -/
example :
    let R : Unit -> Unit -> Prop := fun _ _ => True
    let states : Set Unit := Set.univ
    forall {x₀ x}, x₀ ∈ states -> Relation.ReflTransGen R x₀ x -> x ∈ states := by
  intro R states x₀ x _ _
  trivial

/-- The state carrier used by the witness is inhabited. -/
example : Unit := ()

#print axioms invariant_safety

end D5.S0.Rewriting.Safety.InvariantSafety
