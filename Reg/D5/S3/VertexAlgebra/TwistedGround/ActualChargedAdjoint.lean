import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFock
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.SignedOscillatorWick
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric (complexSignature complexEqual complexFalse complexEqualDependence complexNotEqual complexNotEqualDependence)
open scoped TensorProduct

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i
private theorem emptyUnit : IsUnit emptyLattice.G.det := by
  change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
  simp
private def oneLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact ⟨1, rfl⟩

namespace actual_charged_coefficient_adjoint
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (e : ℤ) (x y : ActualTensor D hu),
    R.readout () () (actualForm D hu (chargedCoefficient D hu a e x) y)
      (paritySign (bilinear D a a / 2) * actualForm D hu x (chargedCoefficient D hu a (-e-2*chargeNorm D a) y))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actual_charged_coefficient_adjoint)) ↔ arena.Law complexEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice emptyUnit 0 0 0 0
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actual_charged_coefficient_adjoint)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actual_charged_coefficient_adjoint, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actual_charged_coefficient_adjoint) (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actual_charged_coefficient_adjoint "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actual_charged_coefficient_adjoint.family
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
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
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
#print axioms family
end actual_charged_coefficient_adjoint

namespace actualForm_nondegenerate
private instance tensorNontrivial : Nontrivial (ActualTensor emptyLattice emptyUnit) :=
  (TensorProduct.equivFinsuppOfBasisRight (M := Oscillator emptyLattice)
    (Pi.basisFun ℂ (Half (groundRank emptyLattice emptyUnit)))).toEquiv.nontrivial
abbrev Params := {D : LatticeData // IsUnit D.G.det}
abbrev Form (p : Params) := LinearMap.BilinForm ℂ (ActualTensor p.1 p.2)
abbrev signature := Reg.Support.SingleDependentReadout.signature Params Form Form
def actual : Realization signature := realize signature (fun _ _ B => B) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det),
    (R.readout () ⟨D, hu⟩ (actualForm D hu)).Nondegenerate

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actualForm_nondegenerate)) ↔ arena.Law actual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact (h emptyLattice emptyUnit).ne_zero rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨emptyLattice, emptyUnit⟩, 0, actualForm emptyLattice emptyUnit, ?_⟩
  change (0 : LinearMap.BilinForm ℂ _) ≠ _
  exact Ne.symm ((D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actualForm_nondegenerate emptyLattice emptyUnit).ne_zero)
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actualForm_nondegenerate)) where
  actual := actual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actualForm_nondegenerate, rejected, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actualForm_nondegenerate) (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actualForm_nondegenerate "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.actualForm_nondegenerate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end actualForm_nondegenerate


namespace chargedDualCoefficient_nonzero_second_ground
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (u : ActualGround D hu), u ≠ 0 → ∃ x : ActualTensor D hu,
      R.readout () () (chargedDualCoefficient D hu (-chargeNorm D a) x ((1 : Oscillator D) ⊗ₜ[ℂ] u) (Finsupp.single a 1)) 0
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.chargedDualCoefficient_nonzero_second_ground)) ↔ arena.Law complexNotEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  obtain ⟨x, hx⟩ := h emptyLattice emptyUnit 0 1 one_ne_zero
  exact hx
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.chargedDualCoefficient_nonzero_second_ground)) where
  actual := complexNotEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.chargedDualCoefficient_nonzero_second_ground, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexNotEqual complexFalse rejectedLaw
  dependence := complexNotEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.chargedDualCoefficient_nonzero_second_ground) (type_of% (realize complexSignature complexNotEqual.readout complexNotEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.chargedDualCoefficient_nonzero_second_ground "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.chargedDualCoefficient_nonzero_second_ground.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexNotEqual.readout complexNotEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end chargedDualCoefficient_nonzero_second_ground

end Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
