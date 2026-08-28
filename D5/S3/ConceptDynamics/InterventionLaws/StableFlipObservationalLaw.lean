/- GID: D5/S3/ConceptDynamics/InterventionLaws/StableFlipObservationalLaw
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionLaws/StableFlipObservationalLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stable and flip Boolean models have the same uniform independent observational law. -/

import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-26):
   * Exact family primitives `DeterministicBoolSCM`, `noEffectModel`, and
     `flipEffectModel` construct the two source models and are imported rather
     than redeclared.
   * `SingleWorldPerfectInterventionLaw` constructs only post-intervention Nat
     count laws. Repository body-shape searches found no observational law for
     these models and no Real-mass construction from the uniform `(X,U)` pair.
   * Pinned Mathlib provides general independence characterizations but no
     theorem evaluating these two SCMs. Finite sums and `norm_num` evaluate the
     source construction directly. No `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.ConceptDynamics.InterventionLaws.StableFlipObservationalLaw

open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation

/-- Draw the natural treatment and exogenous unit independently and uniformly.
For either the stable or flip structural equation, both observed coordinates
are uniform, their point masses factor into their marginals, and every joint
Boolean outcome has probability one quarter. -/
theorem stable_and_flip_observational_laws_are_uniform_independent :
    let observationalLaw : DeterministicBoolSCM -> Bool -> Bool -> Real :=
      fun model x y =>
        ∑ naturalX : Bool, ∑ unit : Bool,
          if (naturalX, model.outcome unit naturalX) = (x, y) then 1 / 4 else 0
    ∀ model, model = noEffectModel ∨ model = flipEffectModel ->
      (∀ x, ∑ y : Bool, observationalLaw model x y = 1 / 2) ∧
      (∀ y, ∑ x : Bool, observationalLaw model x y = 1 / 2) ∧
      (∀ x y, observationalLaw model x y =
        (∑ y' : Bool, observationalLaw model x y') *
          ∑ x' : Bool, observationalLaw model x' y) ∧
      ∀ x y, observationalLaw model x y = 1 / 4 := by
  dsimp only
  intro model sourceModel
  rcases sourceModel with rfl | rfl
  · constructor
    · intro x
      cases x <;> norm_num [noEffectModel, Fintype.sum_bool]
    constructor
    · intro y
      cases y <;> norm_num [noEffectModel, Fintype.sum_bool]
    constructor
    · intro x y
      cases x <;> cases y <;> norm_num [noEffectModel, Fintype.sum_bool]
    · intro x y
      cases x <;> cases y <;> norm_num [noEffectModel, Fintype.sum_bool]
  · constructor
    · intro x
      cases x <;> norm_num [flipEffectModel, Fintype.sum_bool]
    constructor
    · intro y
      cases y <;> norm_num [flipEffectModel, Fintype.sum_bool]
    constructor
    · intro x y
      cases x <;> cases y <;> norm_num [flipEffectModel, Fintype.sum_bool]
    · intro x y
      cases x <;> cases y <;> norm_num [flipEffectModel, Fintype.sum_bool]

#print axioms stable_and_flip_observational_laws_are_uniform_independent

end D5.S3.ConceptDynamics.InterventionLaws.StableFlipObservationalLaw
