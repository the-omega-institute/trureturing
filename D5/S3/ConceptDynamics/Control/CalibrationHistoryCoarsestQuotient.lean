/- GID: D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.claim; result=D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.refutation; claim=D5/S3/ConceptDynamics/Control/CalibrationHistoryCoarsestQuotient.claim
   digest: Pairwise solvable destructive calibration histories have no coarsest feasible encoding. -/

import D5.S3.ConceptDynamics.Control.FiniteHorizonReachability
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.CalibrationHistoryCoarsestQuotient

open D5.S3.ConceptDynamics.Control.FiniteHorizonReachability

/-- A bad set closed against every control choice excludes every bounded strategy. -/
private theorem trap_general {X : Type*} (system : ControlSystem X)
    (goal bad : Set X)
    (apart : ∀ x ∈ bad, x ∉ goal)
    (trapped : ∀ x ∈ bad, ∀ action : system.Action x,
      ∃ next ∈ system.successor action, next ∈ bad)
    {n : ℕ} {x : X} (hx : x ∈ bad) :
    ¬ BoundedReachStrategy system goal n x := by
  intro strategy
  induction strategy with
  | now atGoal => exact apart _ hx atGoal
  | step action continuation ih =>
      obtain ⟨next, attained, stays⟩ := trapped _ hx action
      exact ih next attained stays

end D5.S3.ConceptDynamics.Control.CalibrationHistoryCoarsestQuotient
