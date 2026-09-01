/- GID: D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction
   generality: G
   mirror-B: D5/B/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Commuting spatial and temporal permutation actions combine into a product-monoid action. -/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic

/-!
# Commuting space-time action

A space-time dynamical system carries a spatial monoid action and a temporal
monoid action on the same state space.  When the two actions commute pointwise,
they combine into a product-monoid action

`(g,t) · x = g · (t · x)`.

The resulting law separates time translation symmetry from event-list
chronology and from Fourier time parameters.  It is a reusable foundation for
periodic, quasiperiodic, Floquet, lattice, and observer dynamics.

This module does not assume topology, continuity, differentiability,
Hamiltonian structure, or a physical arrow of time.
-/

/- Library-search audit trail (2026-09-01):
   * Existing time-ordered memory modules distinguish list chronology and
     Fourier time but do not define a time-translation group action.
   * Existing Floquet and monodromy modules are specialized instances.
   * Repository search found no owner of two commuting monoid actions combined
     into one space-time action.
   * Pinned Mathlib supplies permutation groups and monoid homomorphisms. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Dynamics.SpaceTime.CommutingSpaceTimeAction

universe u v w

/-- Spatial and temporal permutation representations with a pointwise
commutation law. -/
structure SpaceTimeAction
    (Space : Type u) (Time : Type v) (State : Type w)
    [Monoid Space] [Monoid Time] where
  spaceAction : Space →* Equiv.Perm State
  timeAction : Time →* Equiv.Perm State
  commute : ∀ space time state,
    spaceAction space (timeAction time state) =
      timeAction time (spaceAction space state)

variable {Space : Type u} {Time : Type v} {State : Type w}
variable [Monoid Space] [Monoid Time]

/-- Joint action of one spatial and one temporal parameter. -/
def jointAct
    (action : SpaceTimeAction Space Time State)
    (parameter : Space × Time) (state : State) : State :=
  action.spaceAction parameter.1
    (action.timeAction parameter.2 state)

/-- The identity space-time parameter fixes every state. -/
theorem jointAct_one
    (action : SpaceTimeAction Space Time State) (state : State) :
    jointAct action (1, 1) state = state := by
  simp [jointAct]

/-- Product multiplication of space-time parameters acts by composition. -/
theorem jointAct_mul
    (action : SpaceTimeAction Space Time State)
    (first second : Space × Time) (state : State) :
    jointAct action (first * second) state =
      jointAct action first (jointAct action second state) := by
  rcases first with ⟨space₁, time₁⟩
  rcases second with ⟨space₂, time₂⟩
  change
    action.spaceAction (space₁ * space₂)
        (action.timeAction (time₁ * time₂) state) =
      action.spaceAction space₁
        (action.timeAction time₁
          (action.spaceAction space₂
            (action.timeAction time₂ state)))
  simp only [map_mul, Equiv.Perm.mul_apply]
  rw [action.commute space₂ time₁ (action.timeAction time₂ state)]

/-- Pure spatial and pure temporal joint parameters commute. -/
theorem pure_space_time_commute
    (action : SpaceTimeAction Space Time State)
    (space : Space) (time : Time) (state : State) :
    jointAct action (space, 1) (jointAct action (1, time) state) =
      jointAct action (1, time) (jointAct action (space, 1) state) := by
  simpa [jointAct] using action.commute space time state

/-- A state fixed by each component is fixed by their joint action. -/
theorem joint_fixed_of_component_fixed
    (action : SpaceTimeAction Space Time State)
    (space : Space) (time : Time) (state : State)
    (hSpace : action.spaceAction space state = state)
    (hTime : action.timeAction time state = state) :
    jointAct action (space, time) state = state := by
  simp [jointAct, hTime, hSpace]

/-- The joint orbit of a state. -/
def jointOrbit
    (action : SpaceTimeAction Space Time State) (state : State) : Set State :=
  {target | ∃ parameter : Space × Time,
    jointAct action parameter state = target}

/-- Every state belongs to its own joint orbit. -/
theorem self_mem_jointOrbit
    (action : SpaceTimeAction Space Time State) (state : State) :
    state ∈ jointOrbit action state := by
  exact ⟨(1, 1), jointAct_one action state⟩

example : SpaceTimeAction Unit Unit Unit where
  spaceAction := 1
  timeAction := 1
  commute := by simp

#print axioms jointAct_one
#print axioms jointAct_mul
#print axioms pure_space_time_commute
#print axioms joint_fixed_of_component_fixed
#print axioms self_mem_jointOrbit

end D5.S3.Dynamics.SpaceTime.CommutingSpaceTimeAction
