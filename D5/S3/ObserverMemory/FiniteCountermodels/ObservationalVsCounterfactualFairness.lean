/- GID: D5/S3/ObserverMemory/FiniteCountermodels/ObservationalVsCounterfactualFairness
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/FiniteCountermodels/ObservationalVsCounterfactualFairness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Qualification factorization can survive while coupled intervention changes a decision. -/

import Mathlib.Data.Fintype.Prod

/- Library-search audit trail (2026-08-21):
   * The exact query `observational_fairness_counterfactual` has no hit in D5
     or the active frozen ledger.
   * Searches for counterfactual fairness, protected-attribute intervention,
     and group-rate predicates found no repository declaration to reuse.
   * This module therefore localizes the finite two-bit admission domain,
     qualification factorization, and intervention predicates named by §158.
 -/

namespace D5.S3.ObserverMemory.FiniteCountermodels.ObservationalVsCounterfactualFairness

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev State := Bool × Bool

instance : DecidableEq State := inferInstance

/-- The only admitted states are the two diagonal states. -/
def admissible (s : State) : Prop :=
  s = (false, false) ∨ s = (true, true)

/-- Qualification is the unprotected record coordinate. -/
def qualification (s : State) : Bool := s.2

/-- The decision uses the qualification coordinate. -/
def decision (s : State) : Bool := s.2

/-- Observational fairness is factorization through qualification on admission. -/
def observationallyFair : Prop :=
  ∃ factor : Bool → Bool, ∀ s, admissible s -> decision s = factor (qualification s)

/-- The coupled intervention changes the protected bit and sets the record to it. -/
def coupledIntervention (s : State) : State := (¬s.1, ¬s.1)

/-- Counterfactual fairness requires decision invariance under that intervention. -/
def counterfactuallyFair : Prop :=
  ∀ s, admissible s -> decision (coupledIntervention s) = decision s

/-- The admitted diagonal model is observationally fair but not counterfactually fair. -/
theorem observational_fairness_does_not_imply_counterfactual_fairness :
    observationallyFair ∧
      admissible (false, false) ∧
      admissible (true, true) ∧
      decision (false, false) = false ∧
      decision (true, true) = true ∧
      coupledIntervention (false, false) = (true, true) ∧
      decision (coupledIntervention (false, false)) = true ∧
      ¬ counterfactuallyFair := by
  refine ⟨?_, by simp [admissible], by simp [admissible], by decide, by decide, by decide,
    by decide, ?_⟩
  · refine ⟨id, ?_⟩
    intro s hs
    simp [decision, qualification]
  · intro hfair
    have hchange := hfair (false, false) (by simp [admissible])
    have hfalse : (true : Bool) = false := by
      simpa [counterfactuallyFair, coupledIntervention, decision] using hchange
    cases hfalse

/-- The two admitted states witness the finite source domain. -/
example : State := (false, false)

#print axioms observational_fairness_does_not_imply_counterfactual_fairness

end D5.S3.ObserverMemory.FiniteCountermodels.ObservationalVsCounterfactualFairness
