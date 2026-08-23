/- GID: D5/S3/ObserverMemory/FiniteCountermodels/CounterfactualFairnessDoesNotImplyGroupParity
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/FiniteCountermodels/CounterfactualFairnessDoesNotImplyGroupParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Protected intervention preserves decisions while diagonal support has unequal group rates. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/- Library-search audit trail (2026-08-21):
   * The exact query `counterfactual_fairness_group_parity` has no hit in D5
     or the active frozen ledger.
   * Searches for finite group-rate, parity, and counterfactual-invariance
     declarations found no theorem with these combined clauses.
   * The local finite population supplies the source's almost-everywhere
     diagonal support and makes both conditional group denominators explicit.
 -/

namespace D5.S3.ObserverMemory.FiniteCountermodels.CounterfactualFairnessDoesNotImplyGroupParity

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev State := Bool × Bool

instance : DecidableEq State := inferInstance

/-- The decision reads the qualification coordinate. -/
def decision (s : State) : Bool := s.2

/-- A protected-attribute intervention changes only the first coordinate. -/
def protectedIntervention (g : Bool) (s : State) : State := (g, s.2)

/-- Pointwise counterfactual fairness under every protected-attribute value. -/
def counterfactuallyFair : Prop :=
  ∀ g s, decision (protectedIntervention g s) = decision s

/-- The finite population is supported on the diagonal r=p. -/
def population : Finset State := {(false, false), (true, true)}

/-- Members of one protected group in the finite population. -/
def groupMembers (p : Bool) : Finset State :=
  population.filter (fun s => s.1 = p)

/-- Members whose decision is one. -/
def positiveMembers (p : Bool) : Finset State :=
  (groupMembers p).filter (fun s => decision s = true)

/-- The direct finite conditional decision rate, with its denominator visible. -/
def groupDecisionRate (p : Bool) : Rat :=
  ((positiveMembers p).card : Rat) / (groupMembers p).card

/-- On diagonal support, individual counterfactual fairness does not force group parity. -/
theorem counterfactual_fairness_does_not_imply_group_parity :
    counterfactuallyFair ∧
      (∀ s ∈ population, s.2 = s.1) ∧
      (groupMembers false).Nonempty ∧
      (groupMembers true).Nonempty ∧
      groupDecisionRate false = 0 ∧
      groupDecisionRate true = 1 ∧
      groupDecisionRate false ≠ groupDecisionRate true := by
  have hGroupFalse : groupMembers false = {(false, false)} := by
    ext s
    rcases s with ⟨p, r⟩
    cases p <;> cases r <;> simp [groupMembers, population]
  have hGroupTrue : groupMembers true = {(true, true)} := by
    ext s
    rcases s with ⟨p, r⟩
    cases p <;> cases r <;> simp [groupMembers, population]
  have hPositiveFalse : positiveMembers false = ∅ := by
    simp [positiveMembers, hGroupFalse, decision]
  have hPositiveTrue : positiveMembers true = {(true, true)} := by
    simp [positiveMembers, hGroupTrue, decision]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g s
    rfl
  · intro s hs
    simp only [population, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rfl
    · rfl
  · refine ⟨(false, false), by simp [groupMembers, population]⟩
  · refine ⟨(true, true), by simp [groupMembers, population]⟩
  · simp [groupDecisionRate, hPositiveFalse, hGroupFalse]
  · simp [groupDecisionRate, hPositiveTrue, hGroupTrue]
  · rw [show groupDecisionRate false = 0 by simp [groupDecisionRate, hPositiveFalse, hGroupFalse],
      show groupDecisionRate true = 1 by simp [groupDecisionRate, hPositiveTrue, hGroupTrue]]
    decide

/-- A concrete population member witnesses the finite probability support. -/
example : State := (false, false)

#print axioms counterfactual_fairness_does_not_imply_group_parity

end D5.S3.ObserverMemory.FiniteCountermodels.CounterfactualFairnessDoesNotImplyGroupParity
