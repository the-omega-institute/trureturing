/- GID: D5/S3/ConceptDynamics/InterventionLaws/SingleWorldPerfectInterventionLaw
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionLaws/SingleWorldPerfectInterventionLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stable and flip Boolean SCMs agree under every perfect intervention. -/

import D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/- Library-search audit trail (2026-08-26):
   * The exact family primitives `DeterministicBoolSCM`, `Int`,
     `noEffectModel`, and `flipEffectModel` construct the two source models and
     their treatment-intervention marginals; they are imported directly.
   * The nearby frozen theorem `intervention_strictly_weaker_than_counterfactual`
     omits perfect interventions on the outcome and the endogenous joint law,
     so it is not an exact bind for this atom.
   * Body-shape searches for a Boolean perfect-intervention type, an endogenous
     response under `do(X)`/`do(Y)`, and the corresponding four-point count law
     found no D5 primitive. Pinned Mathlib has no causal-law declaration; its
     finite sums are used to count the explicit uniform exogenous population. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.ConceptDynamics.InterventionLaws.SingleWorldPerfectInterventionLaw

open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation

/-- A single-world perfect intervention fixes exactly one endogenous Boolean
variable. -/
inductive PerfectIntervention where
  | setX : Bool -> PerfectIntervention
  | setY : Bool -> PerfectIntervention
  deriving DecidableEq

/-- The endogenous `(X,Y)` response constructed from independent exogenous
Boolean coordinates. A perfect intervention replaces only the selected
structural equation. -/
def endogenousResponse (model : DeterministicBoolSCM)
    (intervention : PerfectIntervention) (exogenous : Bool × Bool) : Bool × Bool :=
  match intervention with
  | .setX x => (x, model.outcome exogenous.2 x)
  | .setY y => (exogenous.1, y)

/-- The joint count law on the uniform four-point exogenous population. -/
def endogenousLaw (model : DeterministicBoolSCM)
    (intervention : PerfectIntervention) : Bool × Bool -> Nat :=
  fun result =>
    ∑ naturalX : Bool, ∑ unit : Bool,
      if endogenousResponse model intervention (naturalX, unit) = result then 1 else 0

/-- In both source SCMs, every imposed treatment gives one occurrence of each
outcome over the uniform exogenous unit, hence a Bernoulli one-half law.
Moreover, the full endogenous joint count laws agree under every perfect
single-world intervention, including interventions fixing `Y`. -/
theorem all_single_world_perfect_intervention_laws_agree :
    (forall treatment result : Bool,
      Int noEffectModel treatment result = 1 ∧
        Int flipEffectModel treatment result = 1) ∧
      forall intervention : PerfectIntervention, forall result : Bool × Bool,
        endogenousLaw noEffectModel intervention result =
          endogenousLaw flipEffectModel intervention result := by
  constructor
  · intro treatment result
    cases treatment <;> cases result <;> decide
  · intro intervention result
    rcases result with ⟨x, y⟩
    cases intervention with
    | setX treatment =>
        cases treatment <;> cases x <;> cases y <;> decide
    | setY outcome =>
        cases outcome <;> cases x <;> cases y <;> decide

#print axioms all_single_world_perfect_intervention_laws_agree

end D5.S3.ConceptDynamics.InterventionLaws.SingleWorldPerfectInterventionLaw
