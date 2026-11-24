import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMBivariateInverseJets

/-! Dependent-family equality readouts for the physical inverse jet coefficients. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.TwistedGround
open FourPoint.OriginalFourMActualChart
open OriginalFourMOccupationTransport (rawLocal)
open OriginalFourMPhysicalCovariance (jac)
open OriginalFourMInverseJets (inverseJetWeight coefficient_comp_pair_div_jac)
open OriginalGaussianSewnAnalytic (coefficient)
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMBivariateInverseJets

namespace PairCoefficient

abbrev arena : Arena where
  signature := complexSignature
  Law r := ∀ {f : ℂ × ℂ → ℂ} (_hf : AnalyticAt ℂ f (0, 0))
    {x : ℝ} (_hx : 0 < x) (_hx₁ : x < 1) (c : Chart) (i j : Puncture) (p q : ℕ),
    r.readout () ()
      (coefficient q (fun v => coefficient p (fun u =>
        f (rawLocal c x i u, rawLocal c x j v) / (jac c x i u * jac c x j v))))
      (∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (q + 1),
        coefficient b (fun v => coefficient a (fun u => f (u, v))) *
          inverseJetWeight c x i p a * inverseJetWeight c x j q b)

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h (f := fun _ => 0) analyticAt_const (x := 1 / 2) (by norm_num)
    (by norm_num) .B .P .Q 0 0

def family : Registration arena (type_of% (@coefficient_comp_pair_div_jac)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@coefficient_comp_pair_div_jac, complexFalse, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coefficient_comp_pair_div_jac) (Realization complexSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMBivariateInverseJets.PairCoefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMBivariateInverseJets.PairCoefficient.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMBivariateInverseJets
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PairCoefficient

end Reg.D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMBivariateInverseJets
