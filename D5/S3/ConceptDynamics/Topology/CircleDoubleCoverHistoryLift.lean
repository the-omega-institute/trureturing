/- GID: D5/S3/ConceptDynamics/Topology/CircleDoubleCoverHistoryLift
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/CircleDoubleCoverHistoryLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The circle double cover has canonical history-dependent path lifts. -/

import D5.S3.ConceptDynamics.Topology.CircleDoubleCoverNoSection
import Mathlib.Topology.Homotopy.Lifting

/- Library-search audit trail (2026-08-27):
   * No exact D5 theorem combines canonical path lifting, the absence of a
     continuous global section, and the endpoint exchange of the circle double
     cover. `CircleDoubleCoverNoSection.no_continuous_global_section` is the exact
     D5 owner of the global negative clause and is imported directly.
   * Body-shape searches for `liftPath`, `liftPath_lifts`, `eq_liftPath_iff'`, and
     circle squaring found no D5 path-lift construction to redeclare. This module
     introduces no `def` or `abbrev`.
   * Pinned Mathlib supplies the canonical objects and laws
     `Circle.isQuotientCoveringMap_npow`, `IsCoveringMap.liftPath`,
     `liftPath_lifts`, `liftPath_zero`, and `eq_liftPath_iff'`.
   * The explicit loop and half-angle lift are constructed on the exact `Circle`
     carrier from `Circle.exp`; no choice-dependent replacement is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Topology.CircleDoubleCoverHistoryLift

open Function
open scoped unitInterval

/-- Initial upper data and the base path determine the canonical lifted branch;
there is no continuous global section, while one full turn exchanges the two
points over the basepoint. -/
theorem circle_double_cover_history_lift :
    let square : Circle → Circle := fun point => point ^ 2
    let covering := (Circle.isQuotientCoveringMap_npow 2).isCoveringMap
    (∀ (basePath : C(I, Circle)) (initial : Circle)
        (initialOver : basePath 0 = square initial),
        let lifted := covering.liftPath basePath initial initialOver
        square ∘ lifted = basePath ∧
          lifted 0 = initial ∧
          ∀ alternative : C(I, Circle),
            square ∘ alternative = basePath ∧ alternative 0 = initial →
              alternative = lifted) ∧
      (¬ ∃ selector : Circle → Circle,
        Continuous selector ∧ ∀ point : Circle, square (selector point) = point) ∧
      let fullTurn : C(I, Circle) :=
        ⟨fun time => Circle.exp (2 * Real.pi * (time : ℝ)), by fun_prop⟩
      let lifted := covering.liftPath fullTurn 1 (by simp [fullTurn])
      square ∘ lifted = fullTurn ∧ lifted 0 = 1 ∧ lifted 1 = -1 := by
  dsimp only
  refine ⟨?_, CircleDoubleCoverNoSection.no_continuous_global_section, ?_⟩
  · intro basePath initial initialOver
    refine ⟨
      (Circle.isQuotientCoveringMap_npow 2).isCoveringMap.liftPath_lifts
        basePath initial initialOver,
      (Circle.isQuotientCoveringMap_npow 2).isCoveringMap.liftPath_zero
        basePath initial initialOver,
      ?_⟩
    intro alternative hAlternative
    exact
      ((Circle.isQuotientCoveringMap_npow 2).isCoveringMap.eq_liftPath_iff'
        initialOver).2 hAlternative
  · let fullTurn : C(I, Circle) :=
      ⟨fun time => Circle.exp (2 * Real.pi * (time : ℝ)), by fun_prop⟩
    let initialOver : fullTurn 0 = (1 : Circle) ^ 2 := by
      simp [fullTurn]
    let lifted :=
      (Circle.isQuotientCoveringMap_npow 2).isCoveringMap.liftPath
        fullTurn 1 initialOver
    let halfTurn : C(I, Circle) :=
      ⟨fun time => Circle.exp (Real.pi * (time : ℝ)), by fun_prop⟩
    have halfTurnLifts : (fun point : Circle => point ^ 2) ∘ halfTurn = fullTurn := by
      funext time
      change Circle.exp (Real.pi * (time : ℝ)) ^ 2 =
        Circle.exp (2 * Real.pi * (time : ℝ))
      rw [← Circle.exp_natCast_mul]
      congr 1
      norm_num
      ring
    have halfTurnStarts : halfTurn 0 = (1 : Circle) := by
      simp [halfTurn]
    have halfTurnIsCanonical : halfTurn = lifted := by
      exact
        ((Circle.isQuotientCoveringMap_npow 2).isCoveringMap.eq_liftPath_iff'
          initialOver).2 ⟨halfTurnLifts, halfTurnStarts⟩
    have expPi : Circle.exp Real.pi = -1 := by
      have squareExpPi : Circle.exp Real.pi ^ 2 = 1 := by
        rw [← Circle.exp_natCast_mul]
        convert Circle.exp_two_pi using 1
        norm_num
      have coerced : ((Circle.exp Real.pi : Circle) : ℂ) ^ 2 = 1 :=
        congrArg (fun point : Circle => (point : ℂ)) squareExpPi
      rcases (sq_eq_one_iff.mp coerced) with hOne | hNegOne
      · exact (Circle.exp_pi_ne_one (Circle.ext hOne)).elim
      · exact Circle.ext hNegOne
    refine ⟨
      (Circle.isQuotientCoveringMap_npow 2).isCoveringMap.liftPath_lifts
        fullTurn 1 initialOver,
      (Circle.isQuotientCoveringMap_npow 2).isCoveringMap.liftPath_zero
        fullTurn 1 initialOver,
      ?_⟩
    change lifted 1 = -1
    rw [← halfTurnIsCanonical]
    simpa [halfTurn] using expPi

#print axioms circle_double_cover_history_lift

end D5.S3.ConceptDynamics.Topology.CircleDoubleCoverHistoryLift
