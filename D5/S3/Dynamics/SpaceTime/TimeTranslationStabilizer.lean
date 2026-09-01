/- GID: D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer
   generality: G
   mirror-B: D5/B/S3/Dynamics/SpaceTime/TimeTranslationStabilizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Time-translation symmetries form a stabilizer subgroup, and symmetry breaking is strict loss of stabilizing parameters. -/

import D5.S3.Dynamics.SpaceTime.CommutingSpaceTimeAction
import Mathlib.Tactic

/-!
# Time-translation stabilizer

For a group-valued temporal action, the time translations fixing a state form
a subgroup.  This provides a precise finite definition of time-translation
symmetry.  A transition from `before` to `after` breaks time symmetry when
every symmetry of `after` was already a symmetry of `before`, while at least
one symmetry of `before` is lost.

This definition separates symmetry breaking from event-list orientation.  It
does not assert spontaneous symmetry breaking, degenerate vacua, a
thermodynamic limit, or an irreversible arrow of time.
-/

/- Library-search audit trail (2026-09-01):
   * `CommutingSpaceTimeAction` owns the temporal permutation representation.
   * Time-ordered memory modules own list chronology rather than a translation
     stabilizer.
   * Repository search found no time-stabilizer subgroup or exact lost-symmetry
     predicate attached to the shared space-time action.
   * Pinned Mathlib supplies subgroups and permutation inverses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Dynamics.SpaceTime.TimeTranslationStabilizer

open D5.S3.Dynamics.SpaceTime.CommutingSpaceTimeAction

universe u v w

variable {Space : Type u} {Time : Type v} {State : Type w}
variable [Monoid Space] [Group Time]

/-- Time translations fixing one state. -/
def timeStabilizer
    (action : SpaceTimeAction Space Time State)
    (state : State) : Subgroup Time where
  carrier := {time | action.timeAction time state = state}
  one_mem' := by simp
  mul_mem' := by
    intro first second hFirst hSecond
    change action.timeAction (first * second) state = state
    simp only [map_mul, Equiv.Perm.mul_apply, hSecond, hFirst]
  inv_mem' := by
    intro time hTime
    change action.timeAction time⁻¹ state = state
    have hTransport := congrArg
      (fun target => action.timeAction time⁻¹ target) hTime
    simpa using hTransport

/-- Membership in the stabilizer is the fixed-state equation. -/
theorem mem_timeStabilizer_iff
    (action : SpaceTimeAction Space Time State)
    (state : State) (time : Time) :
    time ∈ timeStabilizer action state ↔
      action.timeAction time state = state := by
  rfl

/-- Every state is fixed by identity time translation. -/
theorem one_mem_timeStabilizer
    (action : SpaceTimeAction Space Time State)
    (state : State) :
    (1 : Time) ∈ timeStabilizer action state := by
  exact (timeStabilizer action state).one_mem

/-- A time symmetry present before a transition and absent afterwards. -/
def LostTimeSymmetry
    (action : SpaceTimeAction Space Time State)
    (before after : State) (time : Time) : Prop :=
  time ∈ timeStabilizer action before ∧
    time ∉ timeStabilizer action after

/-- Strict loss of time-translation symmetry from one state to another. -/
def TimeSymmetryBreaksFrom
    (action : SpaceTimeAction Space Time State)
    (before after : State) : Prop :=
  (∀ time,
      time ∈ timeStabilizer action after →
        time ∈ timeStabilizer action before) ∧
    ∃ time, LostTimeSymmetry action before after time

/-- A time-symmetry break includes an explicit lost stabilizer. -/
theorem timeSymmetryBreaksFrom_has_witness
    (action : SpaceTimeAction Space Time State)
    {before after : State}
    (hBreak : TimeSymmetryBreaksFrom action before after) :
    ∃ time, LostTimeSymmetry action before after time :=
  hBreak.2

/-- A lost stabilizer is a concrete fixed-before and moved-after witness. -/
theorem lostTimeSymmetry_iff
    (action : SpaceTimeAction Space Time State)
    (before after : State) (time : Time) :
    LostTimeSymmetry action before after time ↔
      action.timeAction time before = before ∧
        action.timeAction time after ≠ after := by
  rfl

/-- No state breaks time symmetry relative to itself. -/
theorem no_timeSymmetryBreaksFrom_self
    (action : SpaceTimeAction Space Time State)
    (state : State) :
    ¬ TimeSymmetryBreaksFrom action state state := by
  intro hBreak
  obtain ⟨time, hFixed, hNotFixed⟩ := hBreak.2
  exact hNotFixed hFixed

/-- If every time translation fixes both states, there is no symmetry break. -/
theorem no_timeSymmetryBreaksFrom_of_all_fixed
    (action : SpaceTimeAction Space Time State)
    (before after : State)
    (hBefore : ∀ time, action.timeAction time before = before)
    (hAfter : ∀ time, action.timeAction time after = after) :
    ¬ TimeSymmetryBreaksFrom action before after := by
  intro hBreak
  obtain ⟨time, _, hLost⟩ := hBreak.2
  exact hLost (hAfter time)

/-- A proper lost-symmetry witness plus inclusion of the remaining
stabilizers proves time-symmetry breaking. -/
theorem timeSymmetryBreaksFrom_intro
    (action : SpaceTimeAction Space Time State)
    (before after : State)
    (hInclusion : ∀ time,
      action.timeAction time after = after →
        action.timeAction time before = before)
    (time : Time)
    (hBefore : action.timeAction time before = before)
    (hAfter : action.timeAction time after ≠ after) :
    TimeSymmetryBreaksFrom action before after := by
  refine ⟨?_, ⟨time, hBefore, hAfter⟩⟩
  intro parameter hParameter
  exact hInclusion parameter hParameter

example :
    let action : SpaceTimeAction Unit Unit Unit :=
      { spaceAction := 1
        timeAction := 1
        commute := by simp }
    ¬ TimeSymmetryBreaksFrom action () () := by
  intro action
  exact no_timeSymmetryBreaksFrom_self action ()

#print axioms timeStabilizer
#print axioms mem_timeStabilizer_iff
#print axioms timeSymmetryBreaksFrom_has_witness
#print axioms lostTimeSymmetry_iff
#print axioms no_timeSymmetryBreaksFrom_self
#print axioms no_timeSymmetryBreaksFrom_of_all_fixed
#print axioms timeSymmetryBreaksFrom_intro

end D5.S3.Dynamics.SpaceTime.TimeTranslationStabilizer
