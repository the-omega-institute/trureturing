import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.PositiveAdapter

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open SignedFinite OriginalGaussianExternalResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.PositiveAdapter

namespace tSigned_positive_eq
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () () (tSigned true true p q r) (OriginalGaussianFiniteCandidateModes.t p q r)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh 0 0 0
def family : Registration arena (type_of% (@tSigned_positive_eq)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@tSigned_positive_eq, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@tSigned_positive_eq) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.PositiveAdapter.tSigned_positive_eq.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.PositiveAdapter.tSigned_positive_eq.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.SignedFinite.PositiveAdapter
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
end tSigned_positive_eq

end Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.PositiveAdapter
