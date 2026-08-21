/- GID: D5/S1/FixedPoints/FiniteMonotoneTermination
   generality: G
   mirror-B: D5/B/S1/FixedPoints/FiniteMonotoneTermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite monotone refinement terminates, but its fixed point need not be unique. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Order.OrderIsoNat

/- Library-search audit trail (2026-08-21):
   * Repository searches for finite monotone termination, antitone stabilization,
     and multiple fixed points found the set-specialized theorem
     `finite_contracting_updates_stabilize`, but no generic finite-poset wrapper.
   * Pinned Mathlib search for `WellFoundedLT`, finite well-founded orders, and
     antitone chains found the exact ingredients `Finite.to_wellFoundedLT` and
     `WellFoundedLT.antitone_chain_condition`; the proof applies the latter
     directly after exposing the iterate orbit as an antitone chain.
   * Pinned Mathlib also provides `antitone_nat_of_succ_le`, used to derive the
     chain order from the one-step refinement hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.FixedPoints.FiniteMonotoneTermination

/-- Iterating a monotone endomorphism which only refines states eventually
reaches a fixed point, and remains there. -/
theorem finite_monotone_iteration_reaches_fixed_point
    {α : Type*} [Finite α] [PartialOrder α]
    (update : α →o α) (initial : α)
    (refines : ∀ state : α, update state ≤ state) :
    ∃ step : ℕ,
      Function.IsFixedPt (update : α → α)
        (((update : α → α)^[step]) initial) ∧
      ∀ later : ℕ, step ≤ later →
        (((update : α → α)^[later]) initial) =
          (((update : α → α)^[step]) initial) := by
  let orbit : ℕ → α := fun n => ((update : α → α)^[n]) initial
  have orbit_step (n : ℕ) : orbit (n + 1) ≤ orbit n := by
    simpa only [orbit, Function.iterate_succ_apply'] using refines (orbit n)
  have orbit_antitone : Antitone orbit := antitone_nat_of_succ_le orbit_step
  obtain ⟨step, stable⟩ :=
    WellFoundedLT.antitone_chain_condition orbit_antitone
  refine ⟨step, ?_, ?_⟩
  · change update (orbit step) = orbit step
    have hstable := (stable step.succ step.le_succ).symm
    simpa only [orbit, Function.iterate_succ_apply'] using hstable
  · intro later hlater
    exact (stable later hlater).symm

/-- The identity update on two ordered states is monotone and has two distinct
initial states whose iteration limits are distinct fixed points. -/
theorem bool_identity_has_distinct_fixed_point_limits :
    ∃ first second : Bool,
      first ≠ second ∧
      (∀ n : ℕ, (((id : Bool → Bool)^[n]) first) = first) ∧
      (∀ n : ℕ, (((id : Bool → Bool)^[n]) second) = second) ∧
      Function.IsFixedPt (id : Bool → Bool) first ∧
      Function.IsFixedPt (id : Bool → Bool) second := by
  refine ⟨false, true, by decide, ?_, ?_, ?_, ?_⟩ <;>
    simp [Function.IsFixedPt]

/-- A finite monotone refinement process terminates from every initial state,
while existence of such limits does not force their uniqueness. -/
theorem finite_monotone_termination_and_nonunique_example :
    (∀ (α : Type*) [Finite α] [PartialOrder α]
        (update : α →o α) (initial : α),
        (∀ state : α, update state ≤ state) →
        ∃ step : ℕ,
          Function.IsFixedPt (update : α → α)
            (((update : α → α)^[step]) initial) ∧
          ∀ later : ℕ, step ≤ later →
            (((update : α → α)^[later]) initial) =
              (((update : α → α)^[step]) initial)) ∧
      (∃ first second : Bool,
        first ≠ second ∧
        (∀ n : ℕ, (((id : Bool → Bool)^[n]) first) = first) ∧
        (∀ n : ℕ, (((id : Bool → Bool)^[n]) second) = second) ∧
        Function.IsFixedPt (id : Bool → Bool) first ∧
        Function.IsFixedPt (id : Bool → Bool) second) := by
  constructor
  · intro α _ _ update initial refines
    exact finite_monotone_iteration_reaches_fixed_point update initial refines
  · exact bool_identity_has_distinct_fixed_point_limits

#print axioms finite_monotone_termination_and_nonunique_example

end D5.S1.FixedPoints.FiniteMonotoneTermination
