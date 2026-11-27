import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondShearObstruction4D
import Reg.Support.SingleDependentReadout

/-! Source-bound audits for the plane-wave angular mismatch. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondShearObstruction4D

open _root_.NullConeGravity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout

private abbrev Rectangle := Σ _α : ℝ, Σ _u₁ : ℝ, Σ _u₂ : ℝ, ℝ

private theorem witness_amplitude_pos : 0 < Real.pi / 5 := by positivity

private theorem witness_precaustic : (4 : ℝ) < Real.pi / (Real.pi / 5) := by
  apply (lt_div_iff₀ witness_amplitude_pos).mpr
  linarith [Real.pi_pos]

private theorem collapsed_rectangle (α u₁ u₂ v θ : ℝ) :
    rectMismatch α u₁ u₂ v v θ = 0 := by
  unfold rectMismatch
  ring

private theorem witness_axis_pos : 0 < rectMismatch (Real.pi / 5) 1 2 3 4 0 :=
  rectMismatch_axis_pos witness_amplitude_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) witness_precaustic

namespace AxisMismatch

abbrev sig := signature Rectangle (fun _ => ℝ) (fun _ => ℝ)

abbrev arena : Arena where
  signature := sig
  Law r := ∀ {α u₁ u₂ v₁ v₂ : ℝ}, 0 < α → 0 < u₁ → u₁ < u₂ → u₂ < v₁ →
    v₁ < v₂ → v₂ < Real.pi / α → 0 < r.readout () ⟨α, u₁, u₂, v₁⟩ v₂

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  have hzero := h (u₁ := 1) (u₂ := 2) (v₁ := 3) (v₂ := 4)
    witness_amplitude_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) witness_precaustic
  exact (lt_irrefl (0 : ℝ)) hzero

def source_registration : Registration arena (type_of% @rectMismatch_axis_pos) where
  actual := realize sig
    (fun _ p v₂ => rectMismatch p.1 p.2.1 p.2.2.1 p.2.2.2 v₂ 0) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@rectMismatch_axis_pos, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨⟨Real.pi / 5, 1, 2, 3⟩, 3, 4, ?_⟩
    change rectMismatch (Real.pi / 5) 1 2 3 3 0 ≠ rectMismatch (Real.pi / 5) 1 2 3 4 0
    rw [collapsed_rectangle]
    exact witness_axis_pos.ne

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rectMismatch_axis_pos) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondShearObstruction4D.AxisMismatch.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondShearObstruction4D.AxisMismatch.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig
    (fun _ p v₂ => rectMismatch p.1 p.2.1 p.2.2.1 p.2.2.2 v₂ 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondShearObstruction4D
    definition := none, coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg"]
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AxisMismatch

namespace AngularMismatch

abbrev sig := signature Rectangle (fun _ => ℝ) (fun _ => ℝ → ℝ)

abbrev arena : Arena where
  signature := sig
  Law r := ∀ {α u₁ u₂ v₁ v₂ : ℝ}, 0 < α → 0 < u₁ → u₁ < u₂ → u₂ < v₁ →
    v₁ < v₂ → v₂ < Real.pi / α →
      0 < ∫ θ in (0 : ℝ)..(2 * Real.pi), (r.readout () ⟨α, u₁, u₂, v₁⟩ v₂ θ) ^ 2

private theorem rejected_law :
    ¬ arena.Law (realize sig (fun _ _ _ _ => 0) (fun e => nomatch e)) := by
  intro h
  have hzero := h (u₁ := 1) (u₂ := 2) (v₁ := 3) (v₂ := 4)
    witness_amplitude_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) witness_precaustic
  norm_num [Realization.readout, realize] at hzero

def source_registration : Registration arena (type_of% @rectMismatch_integral_sq_pos) where
  actual := realize sig
    (fun _ p v₂ => rectMismatch p.1 p.2.1 p.2.2.1 p.2.2.2 v₂) (fun e => nomatch e)
  bridge := Iff.rfl
  variation := ⟨@rectMismatch_integral_sq_pos, _, rejected_law⟩
  sensitivity := sensitivity _ _ _ rejected_law
  dependence := by
    intro _
    refine ⟨⟨Real.pi / 5, 1, 2, 3⟩, 3, 4, ?_⟩
    intro h
    have h0 : rectMismatch (Real.pi / 5) 1 2 3 3 0 = rectMismatch (Real.pi / 5) 1 2 3 4 0 :=
      congrFun h 0
    rw [collapsed_rectangle] at h0
    exact witness_axis_pos.ne h0

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rectMismatch_integral_sq_pos) (Realization sig) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondShearObstruction4D.AngularMismatch.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondShearObstruction4D.AngularMismatch.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig
    (fun _ p v₂ => rectMismatch p.1 p.2.1 p.2.2.1 p.2.2.2 v₂) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondShearObstruction4D
    definition := none, coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "fn", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AngularMismatch

end Reg.D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondShearObstruction4D
