import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Source

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open SignedFinite OriginalGaussianExternalResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Source

namespace sourceAmplitude_false_finite
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p : ℕ) {r : ℂ} (_hr : ‖r‖ < 1),
    R.readout () () (OriginalGaussianSourceEvaluation.sourceAmplitude false p r) (C r*(A r)⁻¹^p*OriginalGaussianFiniteCandidateModes.a p r)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh 0 (r := 0) (by norm_num)
def family : Registration arena (type_of% (@sourceAmplitude_false_finite)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@sourceAmplitude_false_finite, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceAmplitude_false_finite) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Source.sourceAmplitude_false_finite.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Source.sourceAmplitude_false_finite.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Source
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
end sourceAmplitude_false_finite

end Reg.D5.S3.VertexAlgebra.TwistedGround.SignedFinite.Source
