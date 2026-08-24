/- GID: D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Trigger order changes cause, not outcome; provenance restores factorization. -/

import D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'end_state_omits_preempting_cause' D5 Golden/Frozen/accepted`
     returned no matches.
   * The brief's `CounterfactualIdentifiabilityCriterion` module is absent from this
     worktree. The public repository theorem
     `history_sensitive_evaluation_not_outcome_reducible` is the same general fiber
     obstruction and is reused below; this module adds the concrete preemption model.
   * Searches for `ActiveCause|preempt|culprit|provenance` found no public preemption
     result. The private-declaration search found no cause, culprit, provenance, or
     preemption theorem; unrelated private fiber lemmas do not cover this statement.
   * Pinned Mathlib's `Function.FactorsThrough` and `Function.factorsThrough_iff`
     underlie the reused general theorem. No Mathlib result supplies this causal model.
   * The sole sibling digest, `SymmetricEventNoUniqueCulprit`, concerns permutation
     equivariance rather than ordered preemption and does not cover this result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause

open D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/-- The two mechanisms in the minimal preemption model. -/
inductive Mechanism where
  | shooterA
  | shooterB
  deriving DecidableEq

/-- A two-step trace records which mechanism, if any, triggers at each time. -/
abbrev PreemptionTrace := Fin 2 -> Option Mechanism

/-- The trace in which A triggers first and B triggers only after the outcome. -/
def aThenB : PreemptionTrace := fun time =>
  if time = 0 then some .shooterA else some .shooterB

/-- The trace in which B triggers first and A triggers only after the outcome. -/
def bThenA : PreemptionTrace := fun time =>
  if time = 0 then some .shooterB else some .shooterA

/-- Whether the outcome has occurred by the given time. Either mechanism suffices. -/
def outcomeBy (trace : PreemptionTrace) (time : Fin 2) : Bool :=
  if time = 0 then (trace 0).isSome else (trace 0).isSome || (trace 1).isSome

/-- The endpoint concept reads only whether the outcome eventually occurred. -/
def endState (trace : PreemptionTrace) : Bool := outcomeBy trace 1

/-- The first mechanism appearing in event order, if any. -/
def firstTrigger (trace : PreemptionTrace) : Option Mechanism :=
  match trace 0 with
  | some mechanism => some mechanism
  | none => trace 1

/-- In this sufficient-trigger model, the first trigger is the mechanism reaching the outcome. -/
def activeCause (trace : PreemptionTrace) : Option Mechanism := firstTrigger trace

/-- The first mechanism reaches the outcome before a distinct delayed trigger. -/
def IsOrderedPreemption
    (trace : PreemptionTrace) (first delayed : Mechanism) : Prop :=
  trace 0 = some first ∧
    trace 1 = some delayed ∧
    first ≠ delayed ∧
    outcomeBy trace 0 = true

/-- Reversing the two triggers gives genuine preemption traces with one endpoint but
different active causes, so active cause cannot factor through the endpoint concept. -/
theorem end_state_omits_preempting_cause :
    IsOrderedPreemption aThenB .shooterA .shooterB ∧
      IsOrderedPreemption bThenA .shooterB .shooterA ∧
      endState aThenB = endState bThenA ∧
      activeCause aThenB ≠ activeCause bThenA ∧
      ¬(∃ recover : Bool → Option Mechanism,
        activeCause = recover ∘ endState) := by
  refine ⟨by simp [IsOrderedPreemption, aThenB, outcomeBy], ?_⟩
  refine ⟨by simp [IsOrderedPreemption, bThenA, outcomeBy], by decide, by decide, ?_⟩
  exact history_sensitive_evaluation_not_outcome_reducible endState activeCause
    ⟨aThenB, bThenA, by decide, by decide⟩

/-- Refining the endpoint with first-trigger provenance makes active cause recoverable. -/
def provenanceReadout (trace : PreemptionTrace) : Bool × Option Mechanism :=
  (endState trace, firstTrigger trace)

/-- Active cause factors through the endpoint refined by first-trigger provenance. -/
theorem active_cause_factors_through_provenance :
    ∃ recover : Bool × Option Mechanism → Option Mechanism,
      activeCause = recover ∘ provenanceReadout := by
  exact ⟨Prod.snd, rfl⟩

example : activeCause aThenB = some .shooterA := by
  decide

#print axioms end_state_omits_preempting_cause

end D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
