/- GID: D5/S3/ConceptDynamics/Communication/JointLosslessCommunicationCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Communication/JointLosslessCommunicationCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint communication is lossless exactly on realized behavior records. -/

import D5.S3.ConceptDynamics.Coding.LosslessEncodingCriterion
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.ObserverMemory.Fusion.LeastCommonRefinement

/- Library-search audit trail (2026-08-28):
   * Exact D5 search found and reuses `messageConcept`,
     `lossless_iff_injective_on_image`, and the canonical dependent
     `jointReadout`; no readout, message, or coordinatewise encoder is redeclared.
   * The core lossless theorem does not contain the source's coordinatewise
     sufficient condition, compensation countermodel, or quotient-fusion clause,
     so it is imported rather than receipt-bound as coverage of the whole atom.
   * Exact D5 hit `least_common_refinement_universal_property` supplies the final
     unique surjective descent and is applied directly with every public premise.
   * Pinned Mathlib supplies `Set.InjOn`, `Setoid.ker`, dependent function
     extensionality, and quotient setoids; no exact combined theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Communication.JointLosslessCommunicationCriterion

open D5.S3.ConceptDynamics.Coding.LosslessEncodingCriterion
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ObserverMemory.Fusion.LeastCommonRefinement

/-- Joint coordinatewise communication preserves exactly the distinctions of the
realized joint behavior iff its coordinatewise encoder is injective on that
realized image. Coordinatewise injectivity is sufficient but not necessary, as
the correlated Boolean countermodel shows. The canonical intersection quotient
also retains its unique surjective least-common-refinement descent. -/
theorem joint_lossless_communication_criterion
    {I X : Type*} {Behavior Message : I -> Type*}
    (behavior : forall i, X -> Behavior i)
    (compress : forall i, Behavior i -> Message i) :
    let fullBehavior := jointReadout behavior
    let jointCompression : (forall i, Behavior i) -> forall i, Message i :=
      fun record i => compress i (record i)
    let jointMessage := messageConcept fullBehavior jointCompression
    (Setoid.ker jointMessage = Setoid.ker fullBehavior <->
      Set.InjOn jointCompression (Set.range fullBehavior)) /\
    ((forall i, Set.InjOn (compress i) (Set.range (behavior i))) ->
      Setoid.ker jointMessage = Setoid.ker fullBehavior) /\
    (exists (counterBehavior : forall _ : Bool, Bool -> Bool)
      (counterCompression : forall _ : Bool, Bool -> Bool),
      Setoid.ker
          (messageConcept (jointReadout counterBehavior)
            (fun record i => counterCompression i (record i))) =
        Setoid.ker (jointReadout counterBehavior) /\
      Not (forall i,
        Set.InjOn (counterCompression i) (Set.range (counterBehavior i)))) /\
    (forall {Y W : Type*} (first second : Setoid Y)
      (projection : Y -> W)
      (toFirst : W -> Quotient first) (toSecond : W -> Quotient second),
      Function.Surjective projection ->
      Function.Surjective toFirst ->
      Function.Surjective toSecond ->
      (forall y, toFirst (projection y) = (Quotient.mk'' y : Quotient first)) ->
      (forall y, toSecond (projection y) = (Quotient.mk'' y : Quotient second)) ->
      ExistsUnique fun descend : W -> Quotient (first ⊓ second) =>
        Function.Surjective descend /\
          forall y, descend (projection y) = Quotient.mk'' y) := by
  dsimp only
  have criterion :
      Setoid.ker
          (messageConcept (jointReadout behavior)
            (fun record i => compress i (record i))) =
          Setoid.ker (jointReadout behavior) <->
        Set.InjOn (fun record i => compress i (record i))
          (Set.range (jointReadout behavior)) := by
    constructor
    · intro kernelEquality
      apply (lossless_iff_injective_on_image
        (jointReadout behavior) (fun record i => compress i (record i))).mpr
      intro x y
      change
        Setoid.ker
            (messageConcept (jointReadout behavior)
              (fun record i => compress i (record i))) x y <->
          Setoid.ker (jointReadout behavior) x y
      rw [kernelEquality]
    · intro injective
      apply Setoid.ext
      intro x y
      exact (lossless_iff_injective_on_image
        (jointReadout behavior) (fun record i => compress i (record i))).mp
          injective x y
  refine ⟨criterion, ?_, ?_, ?_⟩
  · intro coordinateInjective
    apply criterion.mpr
    intro first firstInRange second secondInRange equalMessages
    rcases firstInRange with ⟨x, rfl⟩
    rcases secondInRange with ⟨y, rfl⟩
    funext i
    apply coordinateInjective i
    · exact ⟨x, rfl⟩
    · exact ⟨y, rfl⟩
    · exact congrFun equalMessages i
  · refine ⟨fun _ => id, fun i b => i && b, ?_, ?_⟩
    · apply Setoid.ext
      intro x y
      constructor
      · intro equalMessages
        change (fun i => i && x) = (fun i => i && y) at equalMessages
        have equalAtTrue := congrFun equalMessages true
        simp only [Bool.true_and] at equalAtTrue
        subst y
        rfl
      · intro equalBehavior
        change (fun _ : Bool => x) = (fun _ : Bool => y) at equalBehavior
        have equalAtFalse := congrFun equalBehavior false
        subst y
        rfl
    · intro coordinateInjective
      have falseInjective := coordinateInjective false
      exact Bool.false_ne_true
        (falseInjective ⟨false, rfl⟩ ⟨true, rfl⟩ rfl)
  · intro Y W first second projection toFirst toSecond projectionSurjective
      firstSurjective secondSurjective firstCompatible secondCompatible
    exact least_common_refinement_universal_property first second projection
      toFirst toSecond projectionSurjective firstSurjective secondSurjective
      firstCompatible secondCompatible

#print axioms joint_lossless_communication_criterion

end D5.S3.ConceptDynamics.Communication.JointLosslessCommunicationCriterion
