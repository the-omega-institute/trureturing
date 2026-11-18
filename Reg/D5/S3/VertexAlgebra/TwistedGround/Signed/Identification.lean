import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.Signed.Identification

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianSignedIdentification OriginalGaussianExternalGeneratedSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.Identification
namespace signedJ_eq_candidateJ
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v : ℂ} {r : ℝ} (_hr : 0 < r) (_hr1 : r < 1)
      (_hu : ‖u‖ + Real.sqrt r < 1) (_hv : ‖v‖ + Real.sqrt r < 1)
      (_hneg : e = false ∨ f = false),
    R.readout () ()
      (OriginalGaussianExternalGeneratedSource.kernelMode false e f u v (Real.sqrt r : ℂ))
      (OriginalGaussianExternalSignedCandidate.candidateJ e f u v (r : ℂ))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false (u := 0) (v := 0) (r := 1/4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (Or.inl rfl)

def family : Registration arena (type_of% (@signedJ_eq_candidateJ)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@signedJ_eq_candidateJ, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signedJ_eq_candidateJ) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.Identification.signedJ_eq_candidateJ.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.Identification.signedJ_eq_candidateJ.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.Identification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end signedJ_eq_candidateJ

namespace signedT_eq_candidateT
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v : ℂ} {r : ℝ} (_hr : 0 < r) (_hr1 : r < 1)
      (_hu : ‖u‖ + Real.sqrt r < 1) (_hv : ‖v‖ + Real.sqrt r < 1)
      (_hneg : e = false ∨ f = false),
    R.readout () ()
      (OriginalGaussianExternalGeneratedSource.kernelMode true e f u v (Real.sqrt r : ℂ))
      (OriginalGaussianExternalSignedCandidate.candidateT e f u v (r : ℂ))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false (u := 0) (v := 0) (r := 1/4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (Or.inl rfl)

def family : Registration arena (type_of% (@signedT_eq_candidateT)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@signedT_eq_candidateT, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@signedT_eq_candidateT) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.Identification.signedT_eq_candidateT.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.Identification.signedT_eq_candidateT.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.Identification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end signedT_eq_candidateT

end Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.Identification
