/- GID: D5/S3/ConceptDynamics/Termination/GuardedRankingTermination
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Termination/GuardedRankingTermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A well-founded rank forbids infinite guard-preserving transition chains. -/

import Mathlib.Order.WellFounded
import Mathlib.Tactic

/- Library-search audit trail (2026-08-21):
   * Repository searches for guarded ranking termination, decreasing ranks,
     and `not_rel_apply_succ` found no accepted declaration of this theorem.
   * Pinned Mathlib exact hit `WellFounded.not_rel_apply_succ` states that
     every sequence into a well-founded relation has a nondecreasing adjacent
     pair. The proof below applies that theorem directly to the ranked states.
   * `loogle` and `leansearch` were unavailable on PATH; no third-party
     declaration was needed after the exact pinned-library hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Termination.GuardedRankingTermination

/-- A transition enabled by `guard` cannot execute forever when every step
strictly decreases a rank in a well-founded relation. -/
theorem guarded_ranking_terminates
    {X W : Type*}
    (guard : X -> Prop)
    (step : X -> X -> Prop)
    (rank : X -> W)
    (less : W -> W -> Prop)
    [IsWellFounded W less]
    (decreases : forall {x y},
      guard x -> step x y -> less (rank y) (rank x)) :
    forall trajectory : Nat -> X,
      exists n, Not (guard (trajectory n) ∧
        step (trajectory n) (trajectory (n + 1))) := by
  intro trajectory
  obtain ⟨n, notDecreasing⟩ :=
    WellFounded.not_rel_apply_succ (r := less) (rank ∘ trajectory)
  refine ⟨n, ?_⟩
  rintro ⟨guarded, stepped⟩
  exact notDecreasing (decreases guarded stepped)

/-- The ranking hypotheses admit a nonempty concrete transition relation. -/
example :
    let guard : Nat -> Prop := fun x => 0 < x
    let step : Nat -> Nat -> Prop := fun x y => y + 1 = x
    let rank : Nat -> Nat := id
    (forall {x y}, guard x -> step x y -> rank y < rank x) ∧
      exists x y, guard x ∧ step x y := by
  dsimp
  constructor
  · omega
  · exact ⟨1, 0, by omega, rfl⟩

/-- Natural-number countdown is a checked instance of ranking termination. -/
example :
    forall trajectory : Nat -> Nat,
      exists n, Not (0 < trajectory n ∧
        trajectory (n + 1) + 1 = trajectory n) := by
  apply guarded_ranking_terminates
    (guard := fun x : Nat => 0 < x)
    (step := fun x y => y + 1 = x)
    (rank := id)
    (less := (· < ·))
  intro x y _ stepped
  simp only [id_eq]
  omega

#print axioms guarded_ranking_terminates

end D5.S3.ConceptDynamics.Termination.GuardedRankingTermination
