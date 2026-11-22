import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HilbertOperators.RankOneProjectionCommutator
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

/-! The norm of the projected component as an observation at a fixed projection. -/

namespace Reg.D5.S3.HilbertOperators.RankOneProjectionCommutator

open _root_.D5.S3.HilbertOperators.RankOneProjectionCommutator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.RealScalarLift
open ContinuousLinearMap InnerProductSpace LeanInformationAudit

noncomputable section

universe u v

abbrev signature : Signature where
  Params := Σ 𝕜 : Type u, Σ H : Type v, Σ scalar : RCLike 𝕜,
    Σ additive : SeminormedAddCommGroup H, Σ inner : @InnerProductSpace 𝕜 H scalar additive,
      letI := scalar
      letI := additive
      letI := inner
      H →L[𝕜] H
  State p := p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev observe {𝕜 H : Type*} [RCLike 𝕜] [SeminormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (P : H →L[𝕜] H) (w : H) : ℝ :=
  ‖P w‖

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p => by
    rcases p with ⟨𝕜, H, scalar, additive, inner, P⟩
    exact @observe 𝕜 H scalar additive inner P) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law S := ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [SeminormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (P : H →L[𝕜] H) (_ : P.toLinearMap.IsSymmetricProjection) (w : H),
    ‖rankOne 𝕜 w w ∘L P - P ∘L rankOne 𝕜 w w‖ =
      S.readout () ⟨𝕜, H, inferInstance, inferInstance, inferInstance, P⟩ w * ‖w - P w‖

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let P : (ULift.{v} ℝ) →L[ULift.{u} ℝ] (ULift.{v} ℝ) := 0
  have hP : P.toLinearMap.IsSymmetricProjection := ⟨by simp [P, IsIdempotentElem], by simp [P]⟩
  have hzero := h P hP (ULift.up (1 : ℝ))
  norm_num [P, rejected, realize] at hzero

private theorem varies : ObservationalDependence signature.{u,v} actual := by
  let P := ContinuousLinearMap.id (ULift.{u} ℝ) (ULift.{v} ℝ)
  intro _
  refine ⟨⟨ULift.{u} ℝ, ULift.{v} ℝ, inferInstance, inferInstance, inferInstance, P⟩,
    0, ULift.up 1, ?_⟩
  change ‖(0 : ℝ)‖ ≠ ‖(1 : ℝ)‖
  norm_num

def evidence : Registration arena.{u,v} (type_of% @norm_rankOne_projection_commutator.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@norm_rankOne_projection_commutator.{u,v}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (@Subsingleton.elim Unit inferInstance j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := varies

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@norm_rankOne_projection_commutator.{u,v}) (Realization signature.{u,v}) Unit Unit := {
  unitName := `D5.S3.HilbertOperators.RankOneProjectionCommutator.norm_rankOne_projection_commutator.audit
  realizationName := `Reg.D5.S3.HilbertOperators.RankOneProjectionCommutator.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => by
    rcases p with ⟨𝕜, H, scalar, additive, inner, P⟩
    exact @observe 𝕜 H scalar additive inner P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HilbertOperators.RankOneProjectionCommutator
    definition := none
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.HilbertOperators.RankOneProjectionCommutator
