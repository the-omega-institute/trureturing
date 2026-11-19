import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.Signed.SpatialUniqueness

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround.Signed.SpatialUniqueness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.SpatialUniqueness
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {Rreal : ℝ} (hRpos : 0 < Rreal) (hRone : Rreal ≤ 1)
    (F : ℂ × ℂ → ℂ) (e f square : Bool) (hnegative : e = false ∨ f = false)
    (hdiff : ∀ u v : ℂ, ‖u‖ < Rreal → ‖v‖ < Rreal →
      DifferentiableAt ℂ F (u, v))
    (hpde : ∀ u v : ℂ, ‖u‖ < Rreal → ‖v‖ < Rreal →
      (if f then (1 : ℂ) else v) *
        (u * (1 - u) * deriv (fun w => F (w, v)) u +
          (if e then (1 - 3 * u) / 2 else -(1 + u) / 2) * F (u, v)) +
      (if square then (-1 : ℂ) else 1) * (if e then (1 : ℂ) else u) *
        (v * (1 - v) * deriv (fun w => F (u, w)) v +
          (if f then (1 - 3 * v) / 2 else -(1 + v) / 2) * F (u, v)) = 0),
    ∀ u v : ℂ, ‖u‖ < Rreal → ‖v‖ < Rreal → R.readout () () (F (u, v)) 0

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh (Rreal := 1) (by norm_num) (by norm_num) (fun _ => 0)
    false false false (Or.inl rfl) (by intros; fun_prop) (by intros; simp)
    0 0 (by norm_num) (by norm_num)

def family : Registration arena (type_of% (@signed_spatial_zero)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@signed_spatial_zero, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signed_spatial_zero) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.SpatialUniqueness.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.SpatialUniqueness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.SpatialUniqueness
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.SpatialUniqueness
