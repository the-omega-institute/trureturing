/- GID: D5/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Restoration/IndexedTargetSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Indexed target sufficiency is empty target defect, fiber stability, and factorization. -/

import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

/- Library-search audit trail (2026-08-26):
   * `TargetRecoveryCriterion.target_recovery_criterion` is the exact one-readout
     recovery/fiber/defect owner, but it does not construct an indexed complete
     readout. It is instantiated below rather than restated from Mathlib.
   * `ExperimentIdentifiability.identifiable_tfae` constructs the indexed readout
     but has no target-defect emptiness clause, so it is not an exact bind target.
   * Body-shape search for `fun x i => q i x` found the canonical `jointReadout`;
     search for target-sensitive pair relations found the canonical
     `defectRelation`. Both are imported rather than redeclared.
   * Pinned Mathlib's `Function.factorsThrough_iff` is already applied by the
     imported recovery criterion. Loogle and LeanSearch were unavailable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Restoration.IndexedTargetSufficiency

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

universe u v w z

/-- For an inhabited state space, an indexed readout family is sufficient for a
target exactly when its complete dependent readout has no target-sensitive
defect, equivalently when the target is stable on every local fiber and factors
through that complete readout. Constant local readouts with a constant target
show publicly that this task-level sufficiency need not recover state identity. -/
theorem indexed_target_sufficiency
    {I : Type u} {X : Type v} {Output : I -> Type w} {Target : Type z}
    [Nonempty X] (readout : forall i, X -> Output i) (target : X -> Target) :
    let completeReadout := jointReadout readout
    let locallyStable := forall x y,
      (forall i, readout i x = readout i y) -> target x = target y
    let recoverable := Exists fun recover : (forall i, Output i) -> Target =>
      target = recover ∘ completeReadout
    (defectRelation completeReadout target = ∅ <-> locallyStable) /\
      (locallyStable <-> recoverable) /\
      (defectRelation completeReadout target = ∅ <-> recoverable) /\
      Exists fun witnessReadout : forall _ : Unit, Bool -> Unit =>
        Exists fun witnessTarget : Bool -> Unit =>
          defectRelation (jointReadout witnessReadout) witnessTarget = ∅ /\
          (Exists fun recover : (forall _ : Unit, Unit) -> Unit =>
            witnessTarget = recover ∘ jointReadout witnessReadout) /\
          Not (Function.Injective (jointReadout witnessReadout)) := by
  dsimp only
  have criterion := target_recovery_criterion (jointReadout readout) target
  have fiberBridge :
      (forall x y,
        jointReadout readout x = jointReadout readout y -> target x = target y) <->
        forall x y,
          (forall i, readout i x = readout i y) -> target x = target y := by
    constructor
    · intro stable x y sameCoordinates
      apply stable x y
      funext i
      exact sameCoordinates i
    · intro stable x y sameCompleteReadout
      apply stable x y
      intro i
      exact congrFun sameCompleteReadout i
  refine ⟨criterion.2.1.symm.trans fiberBridge,
    fiberBridge.symm.trans criterion.1.symm,
    criterion.2.2.1, ?_⟩
  let witnessReadout : forall _ : Unit, Bool -> Unit := fun _ _ => ()
  let witnessTarget : Bool -> Unit := fun _ => ()
  refine ⟨witnessReadout, witnessTarget, ?_, ?_, ?_⟩
  · simp [defectRelation, witnessTarget]
  · exact ⟨fun _ => (), rfl⟩
  · intro injective
    apply Bool.false_ne_true
    apply injective
    rfl

#print axioms indexed_target_sufficiency

end D5.S3.ConceptDynamics.Restoration.IndexedTargetSufficiency
