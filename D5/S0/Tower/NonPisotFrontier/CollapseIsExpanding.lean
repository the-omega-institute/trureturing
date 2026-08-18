/- GID: D5/S0/Tower/NonPisotFrontier/CollapseIsExpanding
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotFrontier/CollapseIsExpanding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-block collapse is the general expanding-orbit lemma at one multiplier. -/

import D5.S0.Tower.NonPisotFrontier.BoundedForcesPeriodic
import D5.S0.Tower.NonPisotFrontier.PeriodicCollapse

/- Library-search audit trail (2026-08-18):
   * The general lemma lives one tier up and may not mention this base: a `G`
     artifact importing an `I` fact is rejected by SL-010, which is how this
     module came to exist.  The link was first written inside the general module
     and the gate refused it.
   * That refusal also corrects a rule written earlier the same day, in issue
     2419: it said a generalisation owes the specific form an in-place link,
     preferring that to a separate bridge.  Under the generality ordering the
     in-place link is not available, and the separate artifact is the only legal
     form.  The obligation stands; the location was wrong. -/

namespace D5.S0.Tower.NonPisotFrontier.CollapseIsExpanding

open D5.S0.Tower.NonPisotFrontier.BetaThirteen
open D5.S0.Tower.NonPisotFrontier.BoundedForcesPeriodic
open D5.S0.Tower.NonPisotFrontier.PeriodicCollapse

local notation "β'" => betaThirteenConjugate

/-- The frontier base is expanding, so its bounded orbits inherit the rigidity
proved for an arbitrary expanding multiplier. -/
theorem frontier_base_is_expanding : 1 < |betaThirteen| := by
  have h := two_lt_betaThirteen
  rw [abs_of_pos (by linarith)]
  linarith

/-- The signed step; the frozen module states it only under absolute value. -/
theorem collapse_signed_step {p : Nat} (hp : p ≠ 0) (c y : Real) (k : Nat) :
    collapseIterate p c (k + 1) y - collapseCentre p c
      = β' ^ p * (collapseIterate p c k y - collapseCentre p c) := by
  have hspec := collapseCentre_spec hp c
  rw [collapseIterate]
  linarith [hspec]

/-- Hence the distance identity there is an instance of the orbit identity here. -/
theorem collapse_distance_from_general {p : Nat} (hp : p ≠ 0) (c y : Real) (k : Nat) :
    |collapseIterate p c k y - collapseCentre p c|
      = |β' ^ p| ^ k * |y - collapseCentre p c| := by
  have h := abs_orbit_eq (c := β' ^ p)
    (w := fun j => collapseIterate p c j y - collapseCentre p c)
    (fun j => collapse_signed_step hp c y j) k
  simpa [collapseIterate] using h

/-- And that is exactly the statement proved there, reached by the other route. -/
theorem general_yields_collapse_distance {p : Nat} (hp : p ≠ 0) (c y : Real) (k : Nat) :
    |collapseIterate p c k y - collapseCentre p c|
      = (|β'| ^ p) ^ k * |y - collapseCentre p c| := by
  rw [collapse_distance_from_general hp, abs_pow]

/-- The two developments are one fact at one multiplier, and the base is expanding. -/
theorem the_collapse_is_the_general_lemma :
    1 < |betaThirteen| ∧
      ∀ (p : Nat), p ≠ 0 → ∀ c y : Real, ∀ k : Nat,
        |collapseIterate p c k y - collapseCentre p c|
          = (|β'| ^ p) ^ k * |y - collapseCentre p c| :=
  ⟨frontier_base_is_expanding, fun _ hp c y k => general_yields_collapse_distance hp c y k⟩

end D5.S0.Tower.NonPisotFrontier.CollapseIsExpanding
