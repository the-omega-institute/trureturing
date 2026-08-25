/- GID: D5/S3/ConceptDynamics/Control/CounterfactualRepairSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/CounterfactualRepairSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A successful counterfactual state does not universally imply an admissible allowed repair. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-25):
   * `rg -n -i 'counterfactual|remed|not.*reach|allowed.*action' D5/S3/ConceptDynamics/Control D5/S3/ConceptDynamics/Interventions --glob '*.lean'`
     found `finite_horizon_reachability` and permission monotonicity, but no
     theorem refuting the universal counterfactual-to-repair implication.
   * The pinned Boolean/Set primitives and function application are sufficient
     for the explicit shared-transition countermodel below; no exact Mathlib
     theorem was found by the same body-shape search.
   * The positive and negative clauses use the same target, actual state,
     transition function, and desired value. The counterfactual branch is the
     excluded action of that transition family, so the witness is not separable.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.CounterfactualRepairSeparation

/- The universal source claim is false: a counterfactual target value need not be
   achieved by any action in the allowed set with an admissible result. -/
theorem counterfactual_success_not_imply_allowed_repair :
    ¬ ∀ (State Action Result : Type)
        (target : State → Result) (actual : State) (desired : Result)
        (allowed : Set Action) (step : Action → State → State)
        (admissible : State → Prop),
        (∃ counterfactual : State, target counterfactual = desired) →
          ∃ action, action ∈ allowed ∧
            target (step action actual) = desired ∧
            admissible (step action actual) := by
  intro universalClaim
  have instanceClaim := universalClaim
    Bool Bool Bool (id : Bool → Bool) false true ({false} : Set Bool)
    (fun action state => action || state) (fun _ => True)
  rcases instanceClaim ⟨true, rfl⟩ with ⟨action, actionAllowed, targetReached, _⟩
  have actionIsFalse : action = false := by simpa using actionAllowed
  subst action
  simpa using targetReached

#print axioms counterfactual_success_not_imply_allowed_repair

end D5.S3.ConceptDynamics.Control.CounterfactualRepairSeparation
