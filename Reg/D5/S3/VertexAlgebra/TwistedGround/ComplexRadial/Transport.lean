import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Transport
import D5.S3.VertexAlgebra.TwistedGround.Signed.Identification
noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianComplexRadialContinuation OriginalGaussianExternalGeneratedSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Transport

namespace kernelMode_eq_candidate_complex_of_real
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (square e f : Bool) {u v z : ℂ}
      (_realSupplier : RealRadialSupplier square e f u v)
      (_hu : ‖u‖ + ‖z‖ < 1) (_hv : ‖v‖ + ‖z‖ < 1),
    R.readout () () (kernelMode square e f u v z) (signedCandidate square e f u v (z ^ 2))
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  apply hh false false false (u := 0) (v := 0) (z := 0) _ (by norm_num) (by norm_num)
  intro r hr hr1 hu hv
  exact OriginalGaussianSignedIdentification.signedJ_eq_candidateJ false false hr hr1 hu hv
    (Or.inl rfl)
def family : Registration arena (type_of% (@kernelMode_eq_candidate_complex_of_real)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@kernelMode_eq_candidate_complex_of_real, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernelMode_eq_candidate_complex_of_real) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Transport.kernelMode_eq_candidate_complex_of_real.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Transport.kernelMode_eq_candidate_complex_of_real.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Transport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end kernelMode_eq_candidate_complex_of_real

end Reg.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial.Transport
