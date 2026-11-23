import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCorrectionJets

/-! The complex equality readout of the bivariate physical correction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMActualChart
  (Chart Puncture scale loweringParameter)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMPhysicalCovariance (jac slotCorrection)
open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic (coefficient)
open _root_.D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport (contractionScalar)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCorrectionJets

open _root_.D5.S3.VertexAlgebra.TwistedGround.OriginalFourMInverseJets
  (coefficient_neg_slotCorrection_div_jac)

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (c : Chart) (i : Puncture) (p q : ℕ),
    r.readout () ()
      (coefficient q (fun v => coefficient p (fun u =>
        -(slotCorrection c x i i u v / (jac c x i u * jac c x i v)))))
      ((-loweringParameter c i / scale c x i) ^ (p + q + 1) * contractionScalar p q)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h (x := 3 / 4) (by norm_num) (by norm_num) .A .P 0 0

def family : Registration arena (type_of% (@coefficient_neg_slotCorrection_div_jac)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@coefficient_neg_slotCorrection_div_jac, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coefficient_neg_slotCorrection_div_jac) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCorrectionJets.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCorrectionJets.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCorrectionJets
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCorrectionJets
