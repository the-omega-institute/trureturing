/- GID: D5/S3/ConceptDynamics/Interventions/PredictiveClosureInterventionSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/PredictiveClosureInterventionSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A naturally descending update need not make every intervention descend. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence

/- Library-search audit trail (2026-08-30):
   * Searches for predictive closure, intervention closure, natural updates,
     action families, and interface descent found no exact frozen theorem.
   * `ObservationInterventionSeparation` separates observational and
     interventional maps, but does not state descent through one interface.
   * `DynamicClosureMinimality` constructs the least refinement closed under an
     intervention family, rather than separating natural and controlled closure.
   * `InterventionFamilyTranscriptObstruction` concerns transcript readouts and
     is not an exact statement on a single interface kernel.
   * `EffectiveDescent`, `InterfaceCongruence`, and
     `deterministic_interface_sixfold_equivalence` are the canonical frozen
     primitives and are imported instead of redeclared by body shape. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.PredictiveClosureInterventionSeparation

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence

/-- A three-state interface can be closed under its natural update while an
action extending that update breaks the same interface fiber. -/
theorem predictive_closure_not_intervention_closure :
    ∃ (q : Fin 3 → Bool) (natural : Fin 3 → Fin 3)
      (action : Bool → Fin 3 → Fin 3),
      action false = natural ∧
      EffectiveDescent q natural ∧
      ¬(∀ a, EffectiveDescent q (action a)) ∧
      ∃ a x y,
        q x = q y ∧ q (action a x) ≠ q (action a y) := by
  let q : Fin 3 → Bool := fun x ↦ decide (x = 2)
  let natural : Fin 3 → Fin 3 := id
  let action : Bool → Fin 3 → Fin 3 := fun a x ↦
    match a with
    | false => x
    | true => if x = 1 then 2 else x
  refine ⟨q, natural, action, ?_, ?_, ?_, ?_⟩
  · funext x
    rfl
  · apply ((deterministic_interface_sixfold_equivalence q natural).out 1 0).mp
    intro x y hxy
    simpa [natural] using hxy
  · intro allActionsDescend
    have congruence :=
      ((deterministic_interface_sixfold_equivalence q (action true)).out 0 1).mp
        (allActionsDescend true)
    have broken := congruence (0 : Fin 3) (1 : Fin 3) (by decide)
    simp [q, action] at broken
  · refine ⟨true, 0, 1, by decide, ?_⟩
    decide

#print axioms predictive_closure_not_intervention_closure

end D5.S3.ConceptDynamics.Interventions.PredictiveClosureInterventionSeparation
