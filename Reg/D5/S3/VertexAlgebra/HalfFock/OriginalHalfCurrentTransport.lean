import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

namespace ChamberCoefficient

def arena : Arena where
  signature := complexSignature
  Law observed := ∀ (eta : ℂ) (p q : ℕ),
    observed.readout () () (chamberCoefficient eta p q) (eta^(p+q+1) * contractionScalar p q)

theorem sourceBridge :
    (type_of% (@chamber_coefficient_eq_contraction)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@chamber_coefficient_eq_contraction)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp chamber_coefficient_eq_contraction, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@chamber_coefficient_eq_contraction)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName :=
    `D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport.chamber_coefficient_eq_contraction.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport.ChamberCoefficient.family
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
    owner := `D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport
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

end ChamberCoefficient

end Reg.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport
