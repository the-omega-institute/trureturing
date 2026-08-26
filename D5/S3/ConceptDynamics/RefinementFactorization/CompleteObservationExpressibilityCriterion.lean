/- GID: D5/S3/ConceptDynamics/RefinementFactorization/CompleteObservationExpressibilityCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/CompleteObservationExpressibilityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete observation expressibility is equivalent to joint-kernel inclusion and fiber constancy. -/

import D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Tactic.TFAE

/- Library-search audit trail (2026-08-26):
   * Exact current-tree hits `jointReadout` and `effectiveReadout` are the
     canonical dependent profile and its realized-image normalization; both
     are imported rather than redeclared.
   * `refinement_iff_kernel_inclusion_on_effective_images` is the closest D5
     theorem, but it maps between two realized images and does not package the
     source's three public clauses for an arbitrary target codomain.
   * Exact pinned-Mathlib hits `Set.rangeSplitting`,
     `Set.apply_rangeSplitting`, and `List.TFAE` construct the factor on the
     realized profile and expose the three-way equivalence. No exact whole
     theorem was found in D5 or pinned Mathlib. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementFactorization.CompleteObservationExpressibilityCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w z

/-- A target is expressible from the realized complete joint observation
exactly when the joint observation kernel is contained in the target kernel,
equivalently when equality of every component readout forces equal targets. -/
theorem complete_observation_expressibility_tfae
    {I : Type u} {X : Type v} {V : I -> Type w} {Y : Type z}
    (q : forall i, X -> V i) (target : X -> Y) :
    let profile := jointReadout q
    List.TFAE [
      Refines target (effectiveReadout profile),
      Setoid.ker profile <= Setoid.ker target,
      forall x y, (forall i, q i x = q i y) -> target x = target y] := by
  classical
  dsimp only
  let profile := jointReadout q
  change List.TFAE [
    Refines target (effectiveReadout profile),
    Setoid.ker profile <= Setoid.ker target,
    forall x y, (forall i, q i x = q i y) -> target x = target y]
  tfae_have 1 <-> 2 := by
    constructor
    · rintro ⟨factor, factorization⟩ x y sameProfile
      have sameEffective :
          effectiveReadout profile x = effectiveReadout profile y :=
        (effectiveReadout_eq_iff profile x y).2 sameProfile
      calc
        target x = factor (effectiveReadout profile x) :=
          congrFun factorization x
        _ = factor (effectiveReadout profile y) := congrArg factor sameEffective
        _ = target y := (congrFun factorization y).symm
    · intro kernelInclusion
      refine ⟨fun value => target (Set.rangeSplitting profile value), ?_⟩
      funext x
      apply kernelInclusion
      exact (Set.apply_rangeSplitting profile (effectiveReadout profile x)).symm
  tfae_have 2 <-> 3 := by
    constructor
    · intro kernelInclusion x y sameComponents
      apply kernelInclusion
      funext i
      exact sameComponents i
    · intro fiberConstant x y sameProfile
      apply fiberConstant x y
      intro i
      exact congrFun sameProfile i
  tfae_finish

#print axioms complete_observation_expressibility_tfae

end D5.S3.ConceptDynamics.RefinementFactorization.CompleteObservationExpressibilityCriterion
