import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open _root_.D5.S3.VertexAlgebra.LatticeInvolution
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.SourceBPZ.OriginalSourcePairing
open _root_.D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexEqual complexFalse complexEqualDependence)

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact Fin.elim0 i

private def oneLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intro i j; rfl
  even_diagonal := by intro i; exact ⟨1, rfl⟩

namespace sourcePairing_theta
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (u v : Carrier D),
    R.readout () () (sourcePairing D (theta D u) (theta D v)) (sourcePairing D u v)

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_theta)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice 0 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_theta)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_theta, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_theta)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_theta "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_theta.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
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

#print axioms family
end sourcePairing_theta

namespace sourcePairing_neutralMode
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (i : Fin D.rank) (m : ℤ) (u v : Carrier D),
    R.readout () () (sourcePairing D (neutralMode D i m u) v) (-sourcePairing D u (neutralMode D i (-m) v))

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_neutralMode)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h oneLattice ⟨0, by change 0 < 1; decide⟩ 0 0 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_neutralMode)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_neutralMode, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_neutralMode)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_neutralMode "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_neutralMode.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end sourcePairing_neutralMode

namespace sourcePairing_grade
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData) (h k : ℤ) (_hk : h ≠ k)
    (u v : Carrier D) (_hu : u ∈ grade D h) (_hv : v ∈ grade D k),
    R.readout () () (sourcePairing D u v) 0

theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_grade)) ↔ arena.Law complexEqual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  exact h emptyLattice 0 1 (by decide) 0 0 (Submodule.zero_mem _) (Submodule.zero_mem _)

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_grade)) where
  actual := complexEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_grade, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexEqual complexFalse rejectedLaw
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_grade)
    (type_of% (realize complexSignature complexEqual.readout complexEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_grade "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws.sourcePairing_grade.family
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
    owner := `D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end sourcePairing_grade

end Reg.D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
