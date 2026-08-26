/- GID: D5/S3/ConceptDynamics/Control/NoGuaranteedRemedyOutsideWinningRegion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/NoGuaranteedRemedyOutsideWinningRegion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Outside the finite winning region, no strategy guarantees a remedy. -/

import D5.S3.ConceptDynamics.Control.FiniteHorizonReachability
import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-27):
   * Current-tree and `origin/dev` searches for winning-region exclusion,
     guaranteed remedies, and counterfactual target witnesses found the
     canonical control primitives below but no theorem stating both source
     clauses.
   * Exact repository hit `finite_horizon_reachability` identifies membership
     in each finite winning stage with a bounded guaranteed-reach strategy and
     is applied directly.
   * Pinned Mathlib supplies `Set.mem_iUnion`; no whole-theorem Mathlib hit was
     found. External `loogle` and `leansearch` executables are unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.NoGuaranteedRemedyOutsideWinningRegion

open D5.S3.ConceptDynamics.Control.FiniteHorizonReachability

/-- A state outside every finite winning stage has no bounded strategy that
guarantees reaching the goal. Exhibiting a comparison state already in the goal
does not change that absence of an executable guarantee. -/
theorem no_guaranteed_remedy_outside_winning_region
    {State : Type*} (system : ControlSystem State) (goal : Set State)
    (state : State)
    (outside : state ∉ ⋃ n, winningRegion system goal n) :
    (¬ ∃ n, BoundedReachStrategy system goal n state) ∧
      ∀ counterfactual, counterfactual ∈ goal →
        ¬ ∃ n, BoundedReachStrategy system goal n state := by
  have noRemedy : ¬ ∃ n, BoundedReachStrategy system goal n state := by
    rintro ⟨n, strategy⟩
    apply outside
    exact Set.mem_iUnion.2
      ⟨n, (finite_horizon_reachability system goal n state).2 strategy⟩
  exact ⟨noRemedy, fun _ _ => noRemedy⟩

/-- The outside-winning-region premise is satisfiable. -/
example :
    let system : ControlSystem Unit :=
      { Action := fun _ => Unit
        successor := fun _ => Set.univ
        successor_nonempty := fun _ => ⟨(), Set.mem_univ ()⟩ }
    () ∉ ⋃ n, winningRegion system ∅ n := by
  dsimp only
  simp only [Set.mem_iUnion, not_exists]
  intro n
  induction n with
  | zero => simp [winningRegion]
  | succ n inductionHypothesis =>
      simp only [winningRegion, Set.mem_union, not_or]
      refine ⟨inductionHypothesis, ?_⟩
      rintro ⟨_action, confinesSuccessors⟩
      exact inductionHypothesis (confinesSuccessors (Set.mem_univ ()))

/-- Guaranteed remedies do exist inside a goal, so the public conclusion is
not unconditional. -/
example :
    let system : ControlSystem Unit :=
      { Action := fun _ => Unit
        successor := fun _ => Set.univ
        successor_nonempty := fun _ => ⟨(), Set.mem_univ ()⟩ }
    ∃ n, BoundedReachStrategy system Set.univ n () := by
  dsimp only
  exact ⟨0, .now (Set.mem_univ ())⟩

#print axioms no_guaranteed_remedy_outside_winning_region

end D5.S3.ConceptDynamics.Control.NoGuaranteedRemedyOutsideWinningRegion
