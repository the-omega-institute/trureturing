import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.Signed.JSpatial

noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianExternalSignedCandidate OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalGenerators
open OriginalGaussianExternalAnalyticCandidate (b ell correction)
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.JSpatial
namespace candidateJ_original_displacement
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (e f : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1),
    let x : ℂ := r
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 / period x
    R.readout () () (modeScale f v * L e (fun w => candidateJ e f w v x) u +
      modeScale e u * L f (fun w => candidateJ e f u w x) v) (      (1 - x) * sourceMode e u x * sourceMode f v x *
        (modeA e u x * modeH f v x lam + modeH e u x lam * modeA f v x) / 2 +
          modeB e * modeB f)
private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro hh
  exact hh false false (u := 0) (v := 0) (r := 1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@candidateJ_original_displacement)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@candidateJ_original_displacement, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidateJ_original_displacement) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.JSpatial.candidateJ_original_displacement.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.JSpatial.candidateJ_original_displacement.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.Signed.JSpatial
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end candidateJ_original_displacement

end Reg.D5.S3.VertexAlgebra.TwistedGround.Signed.JSpatial
