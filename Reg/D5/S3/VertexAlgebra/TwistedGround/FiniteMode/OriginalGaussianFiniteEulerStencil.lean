import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteEulerStencil

/-! Faithful equality observation for the full finite polynomial Euler stencil. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteMode
open OriginalGaussianFiniteCandidateModes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes

namespace P_euler_stencil
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (r * PPrime p q r - (p + 1/2 : ℂ) * (P p q r - shiftX P p q r))
      (r * a p r * a q r / 4 - (1-r) *
        (a p r - (if p=0 then 0 else a (p-1) r)) * (r * aPrime q r) / 2)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@P_euler_stencil)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@P_euler_stencil, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@P_euler_stencil) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.P_euler_stencil.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.P_euler_stencil.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteEulerStencil
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end P_euler_stencil

end Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes
