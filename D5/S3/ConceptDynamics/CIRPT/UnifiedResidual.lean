/- GID: D5/S3/ConceptDynamics/CIRPT/UnifiedResidual
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CIRPT/UnifiedResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Kernel residuals unify four-role defects with exact union and data-processing laws. -/

import D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle
import D5.S3.ConceptDynamics.Postprocessing.PostprocessingKernelMonotonicity
import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-09-04):
   * Repository searches for `kernelResidual`, residual extensionality, joint
     target residuals, four-role residuals, and kernel data processing found no
     existing declaration with this kernel-parametric API.
   * Exact repository hits `TargetRisk.RefinementRiskCostTradeoff.defectRelation`
     and `Faithfulness.JointFaithfulnessLeibnizCriterion.diagonal` are reused as
     the canonical CUT defect and equality diagonal; neither is copied.
   * Exact repository hits `PrimitiveBundle.primitive_bundle_joint_kernel` and
     `PostprocessingKernelMonotonicity.postprocessing_kernel_mono` are applied
     in the joint-target and postprocessing proofs.
   * Pinned Mathlib exact hit `Set.sdiff_iInter` supplies the residual-of-an-
     intersection identity. Searches for a packaged four-role specialization
     and residual extensionality theorem found no further exact hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CIRPT

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Postprocessing.PostprocessingKernelMonotonicity
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

universe u v w z

/-- Pairs identified by the current kernel but distinguished by the target kernel. -/
def kernelResidual {X : Type u} (current target : DecidableKernel X) : Set (X × X) :=
  {pair | current.relation pair.1 pair.2 ∧ ¬target.relation pair.1 pair.2}

/-- A CUT-to-CUT kernel residual is definitionally the canonical target defect relation. -/
theorem kernelResidual_cut_eq_defectRelation
    {X : Type u} {B : Type v} {Target : Type w}
    [DecidableEq B] [DecidableEq Target]
    (q : X -> B) (target : X -> Target) :
    kernelResidual (cutKernel q) (cutKernel target) =
      defectRelation q target :=
  rfl

/-- The discrete identity kernel relates exactly equal states. -/
def identityKernel (X : Type u) [DecidableEq X] : DecidableKernel X :=
  cutKernel (id : X -> X)

/-- Absolute escape is the residual against the discrete identity target. -/
def escapeOfKernel {X : Type u} [DecidableEq X]
    (kernel : DecidableKernel X) : Set (X × X) :=
  kernelResidual kernel (identityKernel X)

/-- Absolute escape is the current kernel with the equality diagonal removed. -/
theorem escapeOfKernel_eq_sdiff_diagonal
    {X : Type u} [DecidableEq X] (kernel : DecidableKernel X) :
    escapeOfKernel kernel =
      {pair : X × X | kernel.relation pair.1 pair.2} \ diagonal X :=
  rfl

/-- CIRPT-IE-005: residuals depend only on the two underlying relations. -/
theorem residual_extensional
    {X : Type u}
    {current current' target target' : DecidableKernel X}
    (currentEq : forall x y,
      current.relation x y <-> current'.relation x y)
    (targetEq : forall x y,
      target.relation x y <-> target'.relation x y) :
    kernelResidual current target = kernelResidual current' target' := by
  ext pair
  simp only [kernelResidual, Set.mem_ofPred_eq]
  exact and_congr (currentEq pair.1 pair.2)
    (not_congr (targetEq pair.1 pair.2))

/-- CIRPT-IE-006: for an arbitrary indexed target family, the residual against
its joint kernel is the union of the component residuals. -/
theorem residual_joint_target_eq_iUnion
    {X : Type u} {J : Type v} (current : DecidableKernel X)
    (targets : J -> DecidableKernel X) (joint : DecidableKernel X)
    (hjoint : forall x y,
      joint.relation x y <-> forall index, (targets index).relation x y) :
    kernelResidual current joint =
      ⋃ index, kernelResidual current (targets index) := by
  calc
    kernelResidual current joint =
        {pair : X × X | current.relation pair.1 pair.2} \
          {pair : X × X | joint.relation pair.1 pair.2} := rfl
    _ = {pair : X × X | current.relation pair.1 pair.2} \
          ⋂ index,
            {pair : X × X |
              (targets index).relation pair.1 pair.2} := by
        congr 1
        ext pair
        simpa only [Set.mem_ofPred_eq, Set.mem_iInter] using
          hjoint pair.1 pair.2
    _ = ⋃ index,
          {pair : X × X | current.relation pair.1 pair.2} \
            {pair : X × X |
              (targets index).relation pair.1 pair.2} :=
        Set.sdiff_iInter _ _
    _ = ⋃ index, kernelResidual current (targets index) := rfl

/-- Finite engine corollary of CIRPT-IE-006 for a primitive bundle target. -/
theorem residual_joint_target_eq_iUnion_bundle
    {X : Type u} (current : DecidableKernel X) (targets : PrimitiveBundle X) :
    kernelResidual current targets.toKernel =
      ⋃ index, kernelResidual current (targets.atom index).kernel := by
  apply residual_joint_target_eq_iUnion current
    (fun index => (targets.atom index).kernel) targets.toKernel
  intro x y
  rfl

/-- The defect of one bundle role consists of current-kernel pairs separated
by at least one atom carrying that role. -/
def bundleRoleDefect {X : Type u} (current : DecidableKernel X)
    (targets : PrimitiveBundle X) (axis : PrimitiveAxis) : Set (X × X) :=
  {pair | current.relation pair.1 pair.2 ∧
    ∃ index, (targets.atom index).axis = axis ∧
      ¬(targets.atom index).kernel.relation pair.1 pair.2}

/-- CUT-role defect against a target readout. -/
def cutDefect
    {X : Type u} {B : Type v} {Target : Type w}
    [DecidableEq B] [DecidableEq Target]
    (q : X -> B) (target : X -> Target) : Set (X × X) :=
  kernelResidual (cutKernel q) (cutKernel target)

/-- FLOW-role defect against an observed flow output. -/
def flowDefect
    {X : Type u} {B : Type v} {Y : Type w} {C : Type z}
    [DecidableEq B] [DecidableEq C]
    (q : X -> B) (flow : X -> Y) (observe : Y -> C) : Set (X × X) :=
  kernelResidual (cutKernel q) (flowKernel (observe ∘ flow))

/-- ADMIT-role defect against the admission truth-value kernel. -/
def admitDefect
    {X : Type u} {B : Type v} [DecidableEq B]
    (q : X -> B) (admit : X -> Prop) [DecidablePred admit] : Set (X × X) :=
  kernelResidual (cutKernel q) (admitKernel admit)

/-- Symmetric ANCHOR-role defect against equality with one distinguished state. -/
def anchorDefect
    {X : Type u} {B : Type v} [DecidableEq X] [DecidableEq B]
    (q : X -> B) (anchor : X) : Set (X × X) :=
  kernelResidual (cutKernel q) (anchorKernel anchor)

/-- CIRPT-IE-010: the residual against the four-role target readout is exactly
the union of the four role defects, with overlaps counted only once. -/
theorem four_role_residual_eq_union
    {X : Type u} {B : Type v} {Y : Type w} {C Target : Type z}
    [DecidableEq X] [DecidableEq B] [DecidableEq C] [DecidableEq Target]
    (q : X -> B) (target : X -> Target) (flow : X -> Y) (observe : Y -> C)
    (admit : X -> Prop) [DecidablePred admit] (anchor : X) :
    kernelResidual (cutKernel q)
        (cutKernel (fun state =>
          (target state, observe (flow state), decide (admit state),
            decide (state = anchor)))) =
      cutDefect q target ∪ flowDefect q flow observe ∪
        admitDefect q admit ∪ anchorDefect q anchor := by
  ext pair
  simp only [kernelResidual, cutDefect, flowDefect, admitDefect, anchorDefect,
    cutKernel_relation_iff, flowKernel_relation_iff, admitKernel_relation_iff,
    anchorKernel_relation_iff, Set.mem_ofPred_eq, Set.mem_union, Function.comp_apply,
    Prod.mk.injEq, decide_eq_decide]
  by_cases hCut : target pair.1 = target pair.2
    <;> by_cases hFlow : observe (flow pair.1) = observe (flow pair.2)
    <;> by_cases hAdmit : admit pair.1 <-> admit pair.2
    <;> by_cases hAnchor : (pair.1 = anchor) <-> (pair.2 = anchor)
    <;> simp_all

/-- CIRPT-IE-012: postprocessing a target readout can only shrink its residual. -/
theorem postprocessing_residual_mono
    {X : Type u} {Y : Type v} {Z : Type w}
    [DecidableEq Y] [DecidableEq Z]
    (current : DecidableKernel X) (readout : X -> Y) (postprocess : Y -> Z) :
    kernelResidual current (cutKernel (postprocess ∘ readout)) ⊆
      kernelResidual current (cutKernel readout) := by
  intro pair residualPair
  refine ⟨residualPair.1, ?_⟩
  intro sameReadout
  exact residualPair.2
    (postprocessing_kernel_mono readout postprocess sameReadout)

#print axioms residual_joint_target_eq_iUnion

end D5.S3.ConceptDynamics.CIRPT
