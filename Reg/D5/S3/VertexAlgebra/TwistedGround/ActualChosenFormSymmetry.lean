import D5.S3.VertexAlgebra.TwistedGround.ActualChosenFormSymmetry
import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Faithful full-telescope equality-readout audit attempt. The typed bridge,
variation, sensitivity and dependence below do not assert current admission.
IsSymm source reconstruction remains a separate producer obligation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChosenFormSymmetry
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChosenFormSymmetry
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i
private theorem emptyUnit : IsUnit emptyLattice.G.det := by
  change IsUnit (0 : Matrix (Fin 0) (Fin 0) ℤ).det
  simp

def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (x y : ActualTensor D hu),
    R.readout () () (actualForm D hu x y) (actualForm D hu y x)

theorem sourceBridge : (type_of% (@actualForm_isSymm)) ↔ arena.Law complexEqual := by
  constructor
  · intro h D hu x y
    exact (h D hu).eq x y
  · intro h D hu
    exact ⟨h D hu⟩

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice emptyUnit 0 0

def family : Registration arena (type_of% (@actualForm_isSymm)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp actualForm_isSymm, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actualForm_isSymm)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.TwistedGround.ActualChosenFormSymmetry.actualForm_isSymm
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChosenFormSymmetry.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sourceBridge
#print axioms family
#print axioms registration
end Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChosenFormSymmetry
end
