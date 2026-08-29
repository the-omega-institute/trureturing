/- GID: D5/S3/ConceptDynamics/TargetRisk/LocalGlobalResidualExpressibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TargetRisk/LocalGlobalResidualExpressibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: LGRes is empty exactly for expressible targets, including degenerate carriers. -/

import D5.S3.ConceptDynamics.RefinementFactorization.CompleteObservationExpressibilityCriterion
import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-08-25):
   * Exact repository searches found the canonical `defectRelation`, but no named
     local-global target residual or theorem giving its expressibility equation.
   * `complete_observation_expressibility_tfae` supplies the required equivalence
     with fiber constancy, so the proof below applies it instead of reproving it.
   * Pinned Mathlib supplies the set-extensionality and function-extensionality
     primitives used for the empty-set and constant-map degeneracy probes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TargetRisk.LocalGlobalResidualExpressibility

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.RefinementFactorization
open D5.S3.ConceptDynamics.RefinementFactorization.CompleteObservationExpressibilityCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

universe u v w z

/-- The local-global residual consists of pairs merged by every local readout
but separated by the target. It reuses the canonical target-defect relation. -/
def localGlobalResidual
    {I : Type u} {X : Type v} {V : I -> Type w} {Y : Type z}
    (target : X -> Y) (q : forall i, X -> V i) : Set (X × X) :=
  defectRelation (jointReadout q) target

/-- The local-global target residual is empty exactly when the target factors
through the effective complete joint observation. -/
theorem local_global_residual_empty_iff_expressible
    {I : Type u} {X : Type v} {V : I -> Type w} {Y : Type z}
    (target : X -> Y) (q : forall i, X -> V i) :
    localGlobalResidual target q = ∅ ↔
      Refines target (effectiveReadout (jointReadout q)) := by
  have criterion := complete_observation_expressibility_tfae q target
  constructor
  · intro emptyResidual
    apply (criterion.out 2 0).mp
    intro x y sameComponents
    by_contra differentTarget
    have escaped : (x, y) ∈ localGlobalResidual target q := by
      exact ⟨funext sameComponents, differentTarget⟩
    rw [emptyResidual] at escaped
    exact escaped
  · intro expressible
    have fiberConstant := (criterion.out 0 2).mp expressible
    ext pair
    constructor
    · rintro ⟨sameReadout, differentTarget⟩
      apply differentTarget
      apply fiberConstant
      intro i
      exact congrFun sameReadout i
    · intro impossible
      exact impossible.elim
#print axioms local_global_residual_empty_iff_expressible

example {I : Type u} {V : I -> Type w} {Y : Type z} (target : Empty -> Y)
    (q : forall i, Empty -> V i) :
    localGlobalResidual target q = ∅ := by
  ext pair
  exact nomatch pair.1

example {I : Type u} {X : Type v} {V : I -> Type w} {Y : Type z}
    (q : forall i, X -> V i) (value : Y) :
    localGlobalResidual (fun _ => value) q = ∅ := by
  ext pair
  simp [localGlobalResidual, defectRelation]

example {I : Type u} {X : Type v} {V : I -> Type w} {Y : Type z}
    (values : forall i, V i) (target : X -> Y) :
    localGlobalResidual target (fun i _ => values i) =
      {pair | target pair.1 ≠ target pair.2} := by
  ext pair
  constructor
  · rintro ⟨-, targetSeparates⟩
    exact targetSeparates
  · intro targetSeparates
    exact ⟨rfl, targetSeparates⟩

end D5.S3.ConceptDynamics.TargetRisk.LocalGlobalResidualExpressibility
