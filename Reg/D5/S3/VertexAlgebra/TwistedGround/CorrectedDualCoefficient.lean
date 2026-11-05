import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.CorrectedDualCoefficient
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.CorrectedDualCoefficient
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

namespace correctedDualCoefficient_nonzero_second_ground
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (u : ActualGround D hu), u ≠ 0 → ∃ x : ActualTensor D hu,
      R.readout () () (correctedDualCoefficient D hu (-chargeNorm D a) x ((1 : Oscillator D) ⊗ₜ[ℂ] u) (Finsupp.single a (1 : Oscillator D))) 0
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.correctedDualCoefficient_nonzero_second_ground)) ↔ arena.Law complexNotEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  obtain ⟨x, hx⟩ := h emptyLattice emptyUnit 0 1 one_ne_zero
  exact hx
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.correctedDualCoefficient_nonzero_second_ground)) where
  actual := complexNotEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.correctedDualCoefficient_nonzero_second_ground, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexNotEqual complexFalse rejectedLaw
  dependence := complexNotEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.correctedDualCoefficient_nonzero_second_ground) (type_of% (realize complexSignature complexNotEqual.readout complexNotEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint.correctedDualCoefficient_nonzero_second_ground "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.CorrectedDualCoefficient.correctedDualCoefficient_nonzero_second_ground.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.CorrectedDualCoefficient
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
end correctedDualCoefficient_nonzero_second_ground

end Reg.D5.S3.VertexAlgebra.TwistedGround.CorrectedDualCoefficient
