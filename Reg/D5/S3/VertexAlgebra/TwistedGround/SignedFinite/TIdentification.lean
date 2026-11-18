import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.TIdentification

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open SignedFinite OriginalGaussianExternalResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.TIdentification

namespace externalT_signed_finite_eq
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) (p q : ℕ) {z : ℂ} (_hz : ‖z‖ < 1),
    R.readout () () (externalT e p f q z) (tSigned e f p q (z^2))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false 0 0 (z := 0) (by norm_num)
def family : Registration arena (type_of% (@externalT_signed_finite_eq)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@externalT_signed_finite_eq, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalT_signed_finite_eq) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.TIdentification.externalT_signed_finite_eq.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.TIdentification.externalT_signed_finite_eq.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.SignedFinite.TIdentification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end externalT_signed_finite_eq

end Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.TIdentification
