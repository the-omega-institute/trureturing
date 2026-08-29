/- GID: D5/S3/ConceptDynamics/Governance/SoundnessLivenessShapeOnlyIndependence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/SoundnessLivenessShapeOnlyIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Soundness and liveness are independent and no shape-only test captures liveness. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-29):
   * Exact and shape searches for shape-invariant tests, soundness/liveness
     independence, and liveness characterization in `D5/S0/Rewriting`,
     `D5/S1/FixedPoints`, and `D5/S3/ConceptDynamics` found no matching theorem.
   * Direct inspection of `CommitInterfaceSealPreservation` and
     `TargetLaunderingCriterion` found no judge-shape or liveness interface.
   * Pinned Lean core supplies `Iff.trans`; pinned Mathlib v4.31.0 supplies the
     Bool and product instances used to verify the concrete model. The generic
     shape-invariance contradiction below composes `Iff.trans` directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.SoundnessLivenessShapeOnlyIndependence

/-- The concrete two-coordinate judge model. -/
abbrev Judge := Bool × Bool

/-- Soundness reads the first coordinate. -/
def sound (judge : Judge) : Prop := judge.1 = true

/-- Liveness reads the second coordinate. -/
def live (judge : Judge) : Prop := judge.2 = true

/-- Shape exposes the first coordinate rather than collapsing all judges. -/
def shape (judge : Judge) : Bool := judge.1

/-- A same-shape pair with different liveness rules out every shape-invariant
test family as an exact characterization of liveness. -/
theorem shape_invariant_tests_fail_of_liveness_difference
    {OtherJudge OtherShape : Type*}
    (otherShape : OtherJudge -> OtherShape)
    (otherLive : OtherJudge -> Prop)
    (witness : exists first second,
      otherShape first = otherShape second ∧
        Not (Iff (otherLive first) (otherLive second))) :
    forall test : OtherJudge -> Prop,
      (forall first second,
        otherShape first = otherShape second ->
          Iff (test first) (test second)) ->
      Not (forall judge, Iff (test judge) (otherLive judge)) := by
  obtain ⟨first, second, sameShape, differentLiveness⟩ := witness
  intro test shapeInvariant characterizesLiveness
  apply differentLiveness
  exact (characterizesLiveness first).symm.trans
    ((shapeInvariant first second sameShape).trans
      (characterizesLiveness second))

/-- In the concrete Bool-by-Bool model, soundness and liveness imply neither
other. Equal first-coordinate shape also cannot support any exact liveness test;
the same obstruction holds in every model with an equal-shape liveness split. -/
theorem soundness_liveness_independent_of_shape_only_tests :
    sound (true, false) ∧
      Not (live (true, false)) ∧
      live (false, true) ∧
      Not (sound (false, true)) ∧
      shape (true, false) = shape (true, true) ∧
      Not (Iff (live (true, false)) (live (true, true))) ∧
      Not (forall judge, sound judge -> live judge) ∧
      Not (forall judge, live judge -> sound judge) ∧
      (forall test : Judge -> Prop,
        (forall first second,
          shape first = shape second -> Iff (test first) (test second)) ->
        Not (forall judge, Iff (test judge) (live judge))) ∧
      (forall {OtherJudge OtherShape : Type*}
        (otherShape : OtherJudge -> OtherShape)
        (otherLive : OtherJudge -> Prop),
        (exists first second,
          otherShape first = otherShape second ∧
            Not (Iff (otherLive first) (otherLive second))) ->
        forall test : OtherJudge -> Prop,
          (forall first second,
            otherShape first = otherShape second ->
              Iff (test first) (test second)) ->
          Not (forall judge, Iff (test judge) (otherLive judge))) := by
  have differentConcreteLiveness :
      Not (Iff (live (true, false)) (live (true, true))) := by
    simp [live]
  have concreteShapeOnlyFailure :
      forall test : Judge -> Prop,
        (forall first second,
          shape first = shape second -> Iff (test first) (test second)) ->
        Not (forall judge, Iff (test judge) (live judge)) :=
    shape_invariant_tests_fail_of_liveness_difference shape live
      ⟨(true, false), (true, true), rfl, differentConcreteLiveness⟩
  refine ⟨by simp [sound], by simp [live], by simp [live], by simp [sound], rfl,
    differentConcreteLiveness, ?_, ?_, concreteShapeOnlyFailure, ?_⟩
  · intro soundImpliesLive
    exact (by simp [live] : Not (live (true, false)))
      (soundImpliesLive (true, false) (by simp [sound]))
  · intro liveImpliesSound
    exact (by simp [sound] : Not (sound (false, true)))
      (liveImpliesSound (false, true) (by simp [live]))
  · intro OtherJudge OtherShape otherShape otherLive witness
    exact shape_invariant_tests_fail_of_liveness_difference
      (OtherJudge := OtherJudge) (OtherShape := OtherShape)
      otherShape otherLive witness

#print axioms soundness_liveness_independent_of_shape_only_tests

end D5.S3.ConceptDynamics.Governance.SoundnessLivenessShapeOnlyIndependence
